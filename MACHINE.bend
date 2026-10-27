import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm

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
      P.Known{n, Nat.min(a, n), String.take(String.drop(r, a), Nat.sub(b, a))}

# The truthful answer to "the letters of contig chrom from index a up to b".
def truth(+fa: List<&2, B.Contig>, +chrom: String, +a: Nat, +b: Nat) -> P.Ans:
  truth.of(B.Fasta.find(fa, chrom), a, b)

def truths.one(+fa: List<&2, B.Contig>, r: P.Req) -> P.Ans:
  match r:
    case P.Req{c, a, b}:
      truth(fa, c, a, b)

# The truthful answers to a list of reads, in order.
def truths(+fa: List<&2, B.Contig>, rs: List<&2, P.Req>) -> List<&2, P.Ans>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      truths.one(fa, r) <> truths(fa, t)

# The driver, as a definition: it feeds the machine the VCF file in the pieces
# cs, then the end of the file (once), answers all reference reads truthfully,
# and collects what the machine writes until it asks to stop.
#   eof: the end of the file was given; done: the exit code, once it stopped.
type DSt is Data:
  DSt{st: Norm.St, next: P.Next, cs: List<&2, String>, eof: Bool, reads: Nat, out: String, notes: List<&2, B.Note>, done: Maybe<&2, Nat>}

def absorb(s: Norm.Step, cs: List<&2, String>, eof: Bool, reads: Nat, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match s:
    case Norm.Step{st, o, ns, nx}:
      DSt{st, nx, cs, eof, reads, out ++ o, List.append(&2, B.Note, notes, ns), None{}}

def dstep.more(cs: List<&2, String>, eof: Bool, st: Norm.St, reads: Nat, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match cs eof:
    case Nil{} True{}:
      DSt{st, P.More{}, Nil{}, True{}, reads, out, notes, None{}}
    case Nil{} False{}:
      absorb(Norm.step(st, P.Eof{}), Nil{}, True{}, reads, out, notes)
    case c <> t _:
      absorb(Norm.step(st, P.Chunk{c}), t, eof, reads, out, notes)

# One step of the driver. Asking for more after the end of the file gets
# nothing (so such a machine never stops). reads counts the reference reads.
def dstep(+fa: List<&2, B.Contig>, d: DSt) -> DSt:
  match d:
    case DSt{st, nx, cs, e, k, out, notes, Some{c}}:
      DSt{st, nx, cs, e, k, out, notes, Some{c}}
    case DSt{st, P.Finish{+c}, cs, e, k, out, notes, None{}}:
      DSt{st, P.Finish{c}, cs, e, k, out, notes, Some{c}}
    case DSt{st, P.Ask{+rs}, cs, e, k, out, notes, None{}}:
      absorb(Norm.step(st, P.Ref{truths(fa, rs)}), cs, e, Nat.add(k, List.length(&2, P.Req, rs)), out, notes)
    case DSt{st, P.More{}, cs, e, k, out, notes, None{}}:
      dstep.more(cs, e, st, k, out, notes)

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

# The report, if the machine stopped within the steps and made at most
# limit reference reads.
def result(d: DSt, +limit: Nat) -> Maybe<&2, R.Report>:
  match d:
    case DSt{st, nx, cs, e, k, out, notes, Some{c}}:
      result.if(Nat.is_le(k, limit), R.Report{out, notes, c})
    case DSt{st, nx, cs, e, k, out, notes, None{}}:
      None{}

def pieces_len(cs: List<&2, String>) -> Nat:
  List.length(&2, String, cs)

# How many driver steps the machine may take, and how many reference reads it
# may make in all (a step is one input given to Norm.step: a piece, the end of
# the file, or one batch of reference answers): the pieces, plus 3, plus (VCF
# length + 1) times (FASTA length + 3), as if each of at most VCF length + 1
# lines needed up to FASTA length + 3 reads. A bound for the proof (the
# machine must stop and cannot read without end); not a speed target.
def bound(fasta: String, vcf: String, cs: List<&2, String>) -> Nat:
  Nat.add(Nat.add(pieces_len(cs), 3n), Nat.mul(1n+String.length(vcf), Nat.add(String.length(fasta), 3n)))

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

def launch(b: Norm.Begin, +fasta: String, +vcf: String, +cs: List<&2, String>) -> Maybe<&2, Launch>:
  match b:
    case Norm.Usage{}:
      None{}
    case Norm.Begin{st, r, v}:
      +n = bound(fasta, vcf, cs)
      launch.of(result(drive(n, B.Fasta.parse(fasta), DSt{st, P.More{}, cs, False{}, 0n, "", Nil{}, None{}}), n), r, v)

# The program: started with a command line B.Args.parse accepts, it opens the
# FASTA and VCF files it names and, for a FASTA file whose sequence lines hold
# no spaces or tabs (P.Fasta.plain), however the VCF file is cut into pieces,
# given truthful reference reads, writes exactly what run says (stdout bytes,
# stderr messages, exit code), within bound steps and bound reads.
#
# What this law does not cover (the trusted driver, main.bend): reading the
# files' bytes; answering each reference read Req{chrom, a, b} of an Ask with
# exactly truth(B.Fasta.parse(fasta), chrom, a, b), in order: Unknown when the .fai has no such
# contig, else Known with the contig's length L.len(Contig.raw) and the slice
# a .. b - 1 of Contig.raw (the sequence letters without line breaks, spaces,
# tabs and CRs). The driver reads it through the .fai index (built by
# samtools faidx), whose offsets count only line breaks (for a FASTA file that
# is not P.Fasta.plain the law says nothing; the driver stops with
# "error: unsupported FASTA", exit code 2, when a read holds a space or tab);
# writing the bytes and the messages
# (B.Note.render); exiting with the code; and the errors outside the laws: a
# usage error (law usage: prints B.usage and exits with code 2) and a file
# that cannot be read (prints "error: cannot read <path>" and exits with
# code 2).
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
  {launch(Norm.start(argv), fasta, vcf, cs) == Some{Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, Launch>}

# A command line B.Args.parse does not accept is a usage error.
law usage:
  for argv: List<&2, String>
  for ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
  {Norm.start(argv) == Norm.Usage{} : Norm.Begin}
