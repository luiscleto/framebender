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

# Whether a parsed command line asks to split multiallelic records (-m).
def splits.of(m: Maybe<&2, B.Cfg>) -> Bool:
  match m:
    case Some{B.Cfg{B.Opts{s, w, split, over0, args}, r, v}}:
      split
    case None{}:
      False{}

# The bound's room for split records: (VCF length + 1) squared with -m, else
# nothing.
def split_room(sp: Bool, +vcf: String) -> Nat:
  match sp:
    case True{}:
      Nat.mul(1n+String.length(vcf), 1n+String.length(vcf))
    case False{}:
      0n

# How many driver steps the machine may take, and how many reference reads it
# may make in all (a step is one input given to Norm.step: a piece, the end of
# the file, or one batch of reference answers): the pieces, plus 3, plus the
# command line's length (run echoes it in the header, and one step writes at
# most 2^31 bytes), plus (VCF length + 1) times (FASTA length + 3), as if each
# of at most VCF length + 1 lines needed up to FASTA length + 3 reads. With
# -m, plus (VCF length + 1) squared, so that each record of a split line (one
# per ALT) can be charged a line's allowance. A bound for the proof (the
# machine must stop and cannot read without end); not a speed target.
def bound(+argv: List<&2, String>, fasta: String, +vcf: String, cs: List<&2, String>) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.add(pieces_len(cs), 3n), args_len(argv)), Nat.mul(1n+String.length(vcf), Nat.add(String.length(fasta), 3n))),
    split_room(splits.of(B.Args.parse(argv)), vcf))

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
# given truthful reference reads, writes exactly what run says (the output
# bytes, stderr messages, exit code), within bound steps and bound reads.
#
# What this law does not cover (the trusted driver, main.bend, with its effects
# in io64.c):
# - Reading the files' bytes (the command line's bytes too; for a VCF that is
#   BGZF, the bytes its blocks decompress to, each block's CRC32 and length
#   checked, the file ending with the empty end-of-file block; a VCF whose
#   first two bytes are 1f 8b and that does not start with a BGZF block header
#   is refused), packing each VCF piece and each reference answer as exactly E.enc of its text (bytes four
#   to a word, little-endian, zero-padded, in the smallest block), and writing
#   every output byte (the bytes of each output buffer, D.view) and message
#   (B.Note.render) exactly, then exiting with the code.
# - Where and how the output bytes are written, as B.Args.output(argv) says
#   (law output): to stdout, or to the file it names, opened at the first
#   write, after the first VCF piece was read (created with mode 0666 less the
#   umask, or emptied first if it is a regular file); as they are, or in BGZF:
#   cut into blocks as bgzip 1.24 cuts text (each block a whole number of lines
#   when they fit 65280 bytes, the header's lines apart from the records), each
#   block a gzip member with the BC extra field, deflated by libdeflate at the
#   level (htslib's mapping), in order. Only when the run ends with exit code 0
#   is the 28-byte empty end-of-file block written: a BGZF file is complete
#   exactly when the run succeeded (if closing a regular -o file fails after
#   it, it is cut off again, the run exiting 2, unless that take-back fails
#   itself, when the file may keep it; a pipe cannot take it back).
#   Decompressed, the file is a prefix of the output bytes: all of them when
#   the machine finished. After a failed write nothing more is written to the
#   output.
# - The index, as B.Args.index(argv) says (laws index and index_sink): for
#   Idx{fmt, path} (-W with a BGZF -o file), at the open of the -o file, in
#   this order: (1) it is opened without being emptied, and without waiting
#   for a reader (a FIFO with no reader is refused, not waited on); (2) it
#   must be a regular file and not an input (as above); (3) neither
#   <-o path>.csi nor <-o path>.tbi may be a directory (itself, or through a
#   symlink), a name that cannot be looked at, or (itself, or the file a
#   symlink there names) the -o file, an input or stderr's regular file; and
#   for TBI, no older index may be at a name htslib 1.24 reads before
#   <-o path>.tbi: it tries <-o path>.csi (moved aside in (5)), then <stem>.csi
#   (the -o path up to its last '.' after the first byte: o.vcf.csi for
#   o.vcf.gz), then <-o path>.tbi, taking the first name stat finds; while
#   <stem>.csi exists the run is refused and the file is left alone (it may
#   be the index of another file, such as o.vcf); a CSI comes first, so
#   nothing hides it; (4) a temporary file is created next to
#   path, path.tmp (path.tmp1, path.tmp2, ... when that name exists), mode
#   0666 less the umask; (5) each of <-o path>.csi and <-o path>.tbi that
#   exists is renamed aside, to <name>.old (.old1, ... when that name exists;
#   never replacing a file: renameat2 with RENAME_NOREPLACE, or, where the
#   file system lacks it, link then unlink; where it has neither, the run is
#   refused); (6) the -o file is emptied, and if that fails the
#   old indexes are renamed back; (7) the renamed old indexes are removed (an
#   index of either format there describes the file being replaced, and
#   htslib reads <-o path>.csi before <-o path>.tbi; if one cannot be removed,
#   it stays as <name>.old, a name htslib never reads, and the run goes on). A
#   failure in (1) to (6) leaves the old -o file and both old indexes as they
#   were (a -o file that did not exist stays, empty), except that an index whose
#   move back fails stays as <name>.old beside the unchanged -o file (the
#   message is the step's own: "cannot write <path>" or "cannot write <name>").
#   Each line of the output is parsed as
#   tabix -p vcf parses it (htslib 1.24's tbx_parse1, on the compressor
#   threads; a line holding END= under a lock, as tbx_parse1 then touches a
#   static; lines longer than a block are joined first) and pushed
#   (hts_idx_push, in order, by the writer thread, before the block's bytes
#   are freed) at the virtual offset where it ends (each block's address in
#   the file and the offset in its text, as bgzf_tell gives them to a reader;
#   a last line without LF at the end-of-file block's address). Only for exit
#   code 0 is the index finished (at the end-of-file block's address) and,
#   after the end-of-file block is written and the file closed, saved
#   (hts_idx_save_as, given a name htslib cannot take for a URL: ./ before a
#   relative path) to the temporary file, then renamed to path: the index is
#   what tabix -p vcf (TBI) or bcftools index (CSI, min_shift 14) writes for
#   the -o file under a .vcf.gz name (tabix decides some formats by the name:
#   a name ending in .cram takes its CRAM path), byte for byte when their
#   htslib compresses as the linked one does (libdeflate), else the same
#   index once decompressed. Once the open is done, a run that does not
#   exit 0 leaves no index at either name; no run leaves the temporary file
#   unless it is killed or Bend's runtime stops it (with _exit: out of memory,
#   a Nat past 2^48), and a stray path.tmp or <name>.old is a file htslib
#   never reads. On a normal exit, the index is there exactly
#   when the run exits 0, and the -o file is then complete; when the index
#   cannot be saved or renamed, the end-of-file block is cut off again (as
#   when closing fails) and the run exits 2, and as there, the file may keep
#   the block when that take-back fails, or when the duplicate descriptor's
#   close fails after the rename (the new index is then removed). When a line
#   cannot be indexed, the run continues as without -W, and at the end, for
#   exit code 0 only, after all of the machine's messages, it writes no
#   end-of-file block and exits 2 ("cannot index <path>"); for any other exit
#   code the run is the run without -W, with no index. htslib's own log
#   messages are switched off.
# - Old indexes without -W: when B.Args.output(argv) names a BGZF -o file and
#   B.Args.index(argv) is NoIdx, before any input is opened, one line on
#   stderr for each index name htslib 1.24 would read for the -o path, in its
#   order (<-o path>.csi, <stem>.csi, <-o path>.tbi, <stem>.tbi; <stem> as in
#   (3), no <stem> names when the path has no '.' after its first byte),
#   where stat finds something that is not a directory (htslib finds a
#   directory too, but cannot read it) and that is not the -o path itself:
#   "warning: htslib would read <name> as the index of <path>; remove it or
#   use -W". Nothing there is opened or changed (<stem>.csi may index another
#   file). These lines come before the messages run says, and change nothing
#   else: the output bytes, the other messages and the exit code are as
#   above.
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
#   cannot write" (stdout or stderr), "error: cannot write <path>" (the -o
#   file: it cannot be opened, written or closed), "error: output is an input
#   <path>" (the -o file, of any type, a pipe or FIFO too, is the VCF, the
#   FASTA or its .fai, or is stderr's regular file: refused before the file
#   is emptied; also <-o path>.csi or <-o path>.tbi with -W, itself or the
#   file a symlink there names, before anything is changed), "error: out of
#   memory" (libdeflate's decompressor or compressor; with -W, a table of the
#   open), "error: -W needs a BGZF -o file" (B.Args.index is BadIdx: refused
#   before any input is opened), "error: no index in this build <path>" (-W
#   with BGZF output in a build with libdeflate and without htslib: see
#   build.sh; a build without libdeflate says "no BGZF in this build"
#   first), "error: cannot index <path> (not a regular file)" (the -o file,
#   with -W; a FIFO with no reader too), "error: cannot index <path>" (with
#   -W, for a run whose code is 0, after all of its messages: exactly when
#   tabix -p vcf (TBI) or bcftools index (CSI) refuses the same file under a
#   .vcf.gz name; known causes: for CSI, a text that does not begin with the
#   16 bytes ##fileformat=VCF (bcftools index reads the format from them:
#   an input without that line, or with a # line before it); a POS that
#   htslib reads otherwise, such as one with a leading zero, octal to its
#   strtoll, or 0x, on a line passed unchanged; a position
#   (POS or INFO/END) past what the index holds: 2^29 for TBI, and for CSI
#   past the levels the longest ##contig length sets, or 2^38 with no length;
#   or no memory for the index), "error: cannot write <path>.csi" or ".tbi"
#   (with -W: an index name that is a directory, itself or through a
#   symlink, or cannot be looked at, the temporary file cannot be created,
#   an old index cannot be renamed aside, all before anything is changed; or
#   the index cannot be saved or renamed), "error: cannot write <path>.tbi
#   (htslib would read <stem>.csi first)" (with -W=tbi: an older index there,
#   step (3), before anything is changed),
#   "error: cannot write <path>.csi (it is the -o file)" (or .tbi: the -o
#   path names that index, through a symlink or a hard link),
#   "error: unsupported gzip <path> (not BGZF; ...)", "error:
#   bad BGZF <path>" (also a BGZF VCF without the end-of-file block, as one cut
#   at a block boundary), "error: no BGZF in this build <path>" (a BGZF VCF,
#   or BGZF output to the -o file <path>, "-" for stdout, in a build without
#   libdeflate), "error: bad
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

# The output options choose only how and where the text is written, never the
# text. Wherever the parser expects an option (B.Args.expecting), adding one
# output option o (B.Args.out_opt: -o PATH, -O T or the glued -OT) gives the
# same paths and the same report (output bytes, messages, exit code) as the
# same command line without it. The driver then writes the output bytes where
# and how B.Args.output says (see law machine's comment). The law covers the
# machine's report; the driver's own errors for the -o file ("cannot write
# <path>", "output is an input <path>") are outside it, as law machine's
# comment says. It follows from law machine: parse gives the same Cfg with or
# without o where an option is expected, and Opts.args does not record it.
# Outside this law, as for law machine: Bend's runtime may run out of memory
# with a compressed output, or a higher level, and not without it.
law output:
  for pre: List<&2, String>
  for o: List<&2, String>
  for post: List<&2, String>
  for fasta: String
  for vcf: String
  for cs: List<&2, String>
  for he: {B.Args.expecting(pre) == True{} : Bool}
  for ho: {B.Args.out_opt(o) == True{} : Bool}
  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for h: {String.concat(cs) == vcf : String}
  for hb: {E.texts_ok(command(pre, List.append(&2, String, o, post)), fasta, cs) == True{} : Bool}
  {launch(Norm.start(command(pre, List.append(&2, String, o, post))), command(pre, List.append(&2, String, o, post)), fasta, vcf, cs)
    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}

# -W asks for the output's index and changes nothing in the machine's report.
# Wherever the parser expects an option (B.Args.expecting), adding one index
# option x (B.Args.idx_opt: -W, -Wcsi, -Wtbi, -W=csi, -W=tbi, --write-index,
# --write-index=csi or --write-index=tbi) gives the same paths and the same
# report (output bytes, messages, exit code) as the same command line without
# it. The driver then writes the index where B.Args.index says (see law
# machine's comment). The law covers the machine's report, not the process:
# the driver's own errors for the index ("-W needs a BGZF -o file", "cannot
# index <path>", "cannot write <path>.csi", ...) are outside it, as law
# machine's comment says, and with them the process exits 2 where the
# machine's code is 0. It follows from law machine: parse gives the same Cfg
# with or without x where an option is expected, and Opts.args does not
# record it.
law index:
  for pre: List<&2, String>
  for x: String
  for post: List<&2, String>
  for fasta: String
  for vcf: String
  for cs: List<&2, String>
  for he: {B.Args.expecting(pre) == True{} : Bool}
  for hx: {B.Args.idx_opt(x) == True{} : Bool}
  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for h: {String.concat(cs) == vcf : String}
  for hb: {E.texts_ok(command(pre, x <> post), fasta, cs) == True{} : Bool}
  {launch(Norm.start(command(pre, x <> post)), command(pre, x <> post), fasta, vcf, cs)
    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}

# What the driver takes from a command line besides the machine's report:
# where and how it writes the output (B.Args.output) and its thread count
# (B.Args.threads).
type Route is Data:
  Route{sink: Maybe<&2, B.Sink>, thr: Maybe<&2, Nat>}

def route(+argv: List<&2, String>) -> Route:
  Route{B.Args.output(argv), B.Args.threads(argv)}

# -W changes neither where and how the output is written nor the thread
# count: wherever the parser expects an option (B.Args.expecting), adding one
# index option x (B.Args.idx_opt) gives the same B.Args.output and the same
# B.Args.threads as the command line without it. With law index, the run
# with -W is the run without it, plus the index; B.Args.index is built on
# B.Args.output's Sink (B.Args.idx.mk), so the index is that of the file the
# driver writes. It follows from the parser: where an option is expected, x
# changes only the index format the parser keeps (Drv.idx), which
# B.Args.sink and B.Args.threads do not read.
law index_sink:
  for pre: List<&2, String>
  for x: String
  for post: List<&2, String>
  for he: {B.Args.expecting(pre) == True{} : Bool}
  for hx: {B.Args.idx_opt(x) == True{} : Bool}
  {route(command(pre, x <> post)) == route(command(pre, post)) : Route}
