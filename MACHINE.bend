import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm
import ./bytes_enc.bend as E

# framebender: the law of the program (implementation layer).
#
# The science (LAWS.bend, types.bend, run.bend, tan.bend) defines run, the
# whole-file result, and mentions no code. This file states that the program
# (Norm.start, Norm.step in norm.bend) writes exactly what run says. The
# program may organize its work in any way: read the reference in any windows,
# many at once, cache, work on many lines in parallel. Changing the program
# changes only proofs, never an approved law.

def truth.of(m: Maybe<&2, String>, +a: Nat, +b: Nat) -> P.Ans:
  match m:
    case None{}:
      P.Unknown{}
    case Some{+r}:
      +n = String.length(r)
      P.Known{n, Nat.min(a, n), E.enc(String.take(String.drop(r, a), Nat.sub(b, a)))}

# The truthful answer to "the letters of contig chrom from index a up to b".
def truth(+fa: List<&2, B.Contig>, +chrom: String, +a: Nat, +b: Nat) -> P.Ans:
  truth.of(B.Fasta.find(fa, chrom), a, b)

def truths.one(+fa: List<&2, B.Contig>, r: P.Req) -> P.Ans:
  match r:
    case P.Req{c, a, b}:
      truth(fa, c, a, b)

# The truthful answers to a list of reads, in order.
def truths(+fa: List<&2, B.Contig>, rs: List<&2, P.Req>) -> List<&1, P.Ans>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      truths.one(fa, r) <> truths(fa, t)

# The driver, as a definition: it feeds the machine the VCF file in the pieces
# cs (each packed by E.enc), then the end of the file (once), answers all
# reference reads truthfully (packed by E.enc), and collects the text of what
# the machine writes (E.text) until it asks to stop.
#   eof: the end of the file was given; done: the exit code, once it stopped.
type DSt is Type:
  DSt{st: Norm.St, next: P.Next, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, out: String, notes: List<&2, B.Note>, done: Maybe<&2, Nat>}

def absorb.out(m: Maybe<&2, String>, +out: String) -> String & Bool:
  match m:
    case Some{t}:
      (out ++ t, True{})
    case None{}:
      (out, False{})

def absorb.k(st: Norm.St, nx: P.Next, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, r: String & Bool, +notes: List<&2, B.Note>, ns: List<&2, B.Note>) -> DSt:
  (out, ok) = r
  DSt{st, nx, cs, eof, reads, good && ok, out, List.append(&2, B.Note, notes, ns), None{}}

# A step's output is added as the text it holds (E.out); an output buffer that
# is not well formed clears good, and the run then has no result.
def absorb(s: Norm.Step, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match s:
    case Norm.Step{st, o, ns, nx}:
      absorb.k(st, nx, cs, eof, reads, good, absorb.out(E.out(o), out), notes, ns)

def dstep.more(cs: List<&2, String>, eof: Bool, st: Norm.St, reads: Nat, good: Bool, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match cs eof:
    case Nil{} True{}:
      DSt{st, P.More{}, Nil{}, True{}, reads, good, out, notes, None{}}
    case Nil{} False{}:
      absorb(Norm.step(st, P.Eof{}), Nil{}, True{}, reads, good, out, notes)
    case c <> t _:
      absorb(Norm.step(st, P.Chunk{E.enc(c)}), t, eof, reads, good, out, notes)

# One step of the driver. Asking for more after the end of the file gets
# nothing (so such a machine never stops). reads counts the reference reads.
def dstep(+fa: List<&2, B.Contig>, d: DSt) -> DSt:
  match d:
    case DSt{st, nx, cs, e, k, g, out, notes, Some{c}}:
      DSt{st, nx, cs, e, k, g, out, notes, Some{c}}
    case DSt{st, P.Finish{+c}, cs, e, k, g, out, notes, None{}}:
      DSt{st, P.Finish{c}, cs, e, k, g, out, notes, Some{c}}
    case DSt{st, P.Ask{+rs}, cs, e, k, g, out, notes, None{}}:
      absorb(Norm.step(st, P.Ref{truths(fa, rs)}), cs, e, Nat.add(k, List.length(&2, P.Req, rs)), g && E.reqs_ok(rs), out, notes)
    case DSt{st, P.More{}, cs, e, k, g, out, notes, None{}}:
      dstep.more(cs, e, st, k, g, out, notes)

def drive(fuel: Nat, +fa: List<&2, B.Contig>, d: DSt) -> DSt:
  match fuel:
    case 0n:
      d
    case 1n+f:
      drive(f, fa, dstep(fa, d))

def result.if(ok: Bool, r: R.Report) -> Maybe<&2, R.Report>:
  match ok:
    case True{}:
      Some{r}
    case False{}:
      None{}

# The report, if the machine stopped within the steps, made at most limit
# reference reads, wrote only well-formed buffers and asked for no window of
# more than 2^31 letters (good).
def result(d: DSt, +limit: Nat) -> Maybe<&2, R.Report>:
  match d:
    case DSt{st, nx, cs, e, k, g, out, notes, Some{c}}:
      result.if(g && Nat.is_le(k, limit), R.Report{out, notes, c})
    case DSt{st, nx, cs, e, k, g, out, notes, None{}}:
      None{}

def pieces_len(cs: List<&2, String>) -> Nat:
  List.length(&2, String, cs)

def args_len(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(Nat.add(String.length(x), 1n), args_len(t))

# How many driver steps the machine may take, and how many reference reads it
# may make in all (a step is one input given to Norm.step: a piece, the end of
# the file, or one batch of reference answers): the pieces, plus 3, plus the
# command line's length (run echoes it in the header, and one step writes at
# most 2^31 bytes), plus (VCF length + 1) times (FASTA length + 3), as if each
# of at most VCF length + 1 lines needed up to FASTA length + 3 reads. A bound
# for the proof (the machine must stop and cannot read without end); not a
# speed target.
def bound(argv: List<&2, String>, fasta: String, vcf: String, cs: List<&2, String>) -> Nat:
  Nat.add(Nat.add(Nat.add(pieces_len(cs), 3n), args_len(argv)), Nat.mul(1n+String.length(vcf), Nat.add(String.length(fasta), 3n)))

# What a started program produces: the FASTA and VCF paths it opens, and its
# report.
type Launch is Data:
  Launch{ref: String, vcf: String, rep: R.Report}

def launch.of(m: Maybe<&2, R.Report>, r: String, v: String) -> Maybe<&2, Launch>:
  match m:
    case None{}:
      None{}
    case Some{rep}:
      Some{Launch{r, v, rep}}

def launch(b: Norm.Begin, argv: List<&2, String>, +fasta: String, +vcf: String, +cs: List<&2, String>) -> Maybe<&2, Launch>:
  match b:
    case Norm.Usage{}:
      None{}
    case Norm.Begin{st, r, v}:
      +n = bound(argv, fasta, vcf, cs)
      launch.of(result(drive(n, B.Fasta.parse(fasta), DSt{st, P.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}}), n), r, v)

# The inputs are bytes (E.texts_ok): the command line, the FASTA and the VCF
# pieces hold only characters below 256, as the driver reads files one byte
# per character, and each piece has at most 2^31 bytes, as the driver chooses
# its piece size. The program must write well-formed buffers and ask for
# windows of at most 2^31 letters, or the run has no result (result's good).
# A program with more than 2^31 bytes to write at once may ask for no reads
# (P.Ask{[]}) to get another step: the driver answers it like any Ask.
#
# The program: started with a command line B.Args.parse accepts, it opens the
# FASTA and VCF files it names and, for a FASTA file whose sequence lines hold
# no spaces or tabs (P.Fasta.plain), however the VCF file is cut into pieces,
# given truthful reference reads, writes exactly what run says (stdout bytes,
# stderr messages, exit code), within bound steps and bound reads.
#
# What this law does not cover (the trusted driver, main.bend, with its effects
# in io64.c):
# - Reading the files' bytes (the command line's bytes too; for a VCF that is
#   BGZF, the bytes its blocks decompress to, each block's CRC32 and length
#   checked, the file ending with the empty end-of-file block; a VCF whose
#   first two bytes are 1f 8b and that does not start with a BGZF block header
#   is refused), packing each VCF piece and each reference answer as exactly E.enc of its text (bytes four
#   to a word, little-endian, zero-padded, in the smallest block), and writing
#   every stdout byte (the bytes of each output buffer, D.view) and message
#   (B.Note.render) exactly, then exiting with the code.
# - Answering each reference read Req{chrom, a, b} of an Ask, in order, with
#   exactly truth(B.Fasta.parse(fasta), chrom, a, b): Unknown when the .fai has
#   no such contig, else Known with the contig's length String.length(Contig.raw)
#   and the slice a .. b - 1 of Contig.raw (the letters without line breaks,
#   spaces, tabs and CRs). The driver reads it through the .fai index (built by
#   samtools faidx 1.24 from this FASTA file), at 64-bit offsets.
# - For a FASTA file that is not P.Fasta.plain the law says nothing.
# - The driver's read-ahead and reference reads in flight, and the runtime's
#   thread count, follow --threads (B.Args.threads); reading and writing stay
#   exactly as above.
# - The driver's own errors, each one line on stderr and exit code 2: a usage
#   error (law usage; prints B.usage), "error: cannot read <path>", "error:
#   cannot write", "error: out of memory" (libdeflate's decompressor),
#   "error: unsupported gzip <path> (not BGZF; ...)", "error:
#   bad BGZF <path>" (also a BGZF VCF without the end-of-file block, as one cut
#   at a block boundary), "error: no BGZF in this build <path>", "error: bad
#   .fai index <path>.fai", "error: unsupported FASTA <path>" (a byte read that the
#   .fai layout does not explain), "error: .fai index does not match <path>"
#   (fewer letters than the index promises), "error: FASTA read too large
#   <path>" (never for a window the law allows: the program asks for at most
#   2^31 letters per read, and the driver reads any physical span, line
#   breaks included, in parts). A <path> has each backslash, LF and CR
#   written as \\, \n and \r.
# - Bend's runtime, also trusted, which can stop a run outside this law, with
#   one line "bend: ..." on stderr and exit code 1: when the heap is exhausted,
#   by the machine or by a block the driver allocates for a piece or an answer
#   ("bend: out of memory: ..."; the driver cannot catch this on a CPU build;
#   memory grows with --threads N, so this can happen at one N and not at
#   another),
#   and on any number of 2^48 or more, such as a VCF POS that large ("bend: a
#   Nat past the largest immediate 2^48-1").
law machine:
  for argv: List<&2, String>
  for o: B.Opts
  for ref: String
  for vcfpath: String
  for fasta: String
  for vcf: String
  for cs: List<&2, String>
  for ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for h: {String.concat(cs) == vcf : String}
  for hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, Launch>}

# A command line B.Args.parse does not accept is a usage error.
law usage:
  for argv: List<&2, String>
  for ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
  {Norm.start(argv) == Norm.Usage{} : Norm.Begin}

# A command line: "norm", then the words pre, then the words post.
def command(pre: List<&2, String>, post: List<&2, String>) -> List<&2, String>:
  "norm" <> List.append(&2, String, pre, post)

# --threads N changes nothing the program writes. Wherever the parser expects
# an option (B.Args.expecting: no option waiting for its value, as after
# "norm", after an option's value or after the VCF path), adding --threads N (N from 1 to B.Args.max_threads()) gives
# the same paths and the same report (stdout bytes, messages, exit code) as
# the same command line without it; so two values of N give the same too, at
# any such position. The program may size its work by N. It follows from law
# machine: parse gives the same Cfg with or without --threads N where an option
# is expected, and Opts.args does not record it. Outside this law, as for law
# machine: Bend's runtime may run out of memory at one N and not at another
# (memory grows with N).
law threads:
  for pre: List<&2, String>
  for x: String
  for n: Nat
  for post: List<&2, String>
  for fasta: String
  for vcf: String
  for cs: List<&2, String>
  for he: {B.Args.expecting(pre) == True{} : Bool}
  for hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
  for hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for h: {String.concat(cs) == vcf : String}
  for hb: {E.texts_ok(command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
  {launch(Norm.start(command(pre, "--threads" <> x <> post)), command(pre, "--threads" <> x <> post), fasta, vcf, cs)
    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
