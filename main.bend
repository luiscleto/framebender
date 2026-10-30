import Base
import ./types.bend as B
import ./protocol.bend as P
import ./norm.bend as Norm
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY

# framebender: the driver (trusted, not proven; see the comment on law machine
# in MACHINE.bend).
#
#   framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] [-W[=csi|tbi]] in.vcf
#
# It only runs the proven machine (Norm.start, Norm.step): it reads the VCF
# file in pieces (its bytes, or for a BGZF file the bytes its blocks
# decompress to; up to 16 pieces, or --threads N, are read ahead, in order, by
# a helper thread), gives the machine an empty piece after every 16 pieces
# (or N: the machine's batches), answers the reads of each Ask in order with
# the contig's letters at the .fai offsets (line breaks removed; up to 32
# reads, or N, at a time are read in parallel, then taken in order), writes
# what the machine writes, and exits with the machine's code. The thread
# count is B.Args.threads of the command line (law threads: it changes nothing
# the machine writes); io64.c also sets Bend's worker threads from it. It
# writes the output where and how B.Args.output says (law output): stdout or
# the -o file, plain or BGZF (Io.out_set, Io.out_write, Io.out_close in
# io64.c; the BGZF end-of-file block only for exit code 0), and with -W the
# output's index where B.Args.index says (law index, law index_sink;
# Io.out_index, and the index writer in io64.c: see law machine's comment).
# Every error of its own prints one line "error: ..." and exits with code 2:
#   usage (B.usage), "cannot read <path>", "cannot write" (stdout/stderr),
#   "cannot write <path>" (the -o file), "output is an input <path>" (the -o
#   file is the VCF, the FASTA, its .fai or stderr's file), "no BGZF in this
#   build <path>" also for BGZF output (<path> the -o file, "-" for stdout),
#   "internal error: no output" (B.Args.output refused a command line that
#   Norm.start accepted; never, by output_ok in proof_f_out.bend), "internal
#   error: no index" (the same for B.Args.index: never, by index_ok in
#   proof_f_index.bend), "-W needs a BGZF -o file" (B.Args.index is BadIdx:
#   before any input is opened), "no index in this build <path>" (-W with
#   BGZF output, built without htslib: see build.sh), "cannot index <path>
#   (not a regular file)", "cannot index <path>" (a file tabix -p vcf or
#   bcftools index refuses, or no memory for the index: only for a run whose
#   code is 0, after all of its messages), "cannot write <path>.csi" (or
#   .tbi; also "... (it is the -o file)", and "cannot write <path>.tbi
#   (htslib would read <stem>.csi first)"), "output is an input <path>.csi"
#   (or .tbi), as law machine's comment lists them,
#   "out of memory" (no room for libdeflate's decompressor), "unsupported
#   gzip <path> (not BGZF; use gzip -dc
#   <path> | framebender ... /dev/stdin)" (a VCF whose first two bytes are
#   1f 8b, gzip's, and that does not start with a BGZF block header), "bad
#   BGZF <path>" (a BGZF block of the VCF that is damaged or cut short, or a
#   BGZF VCF that does not end with the empty end-of-file block, as a file
#   cut at a block boundary), "no BGZF in this build <path>" (a BGZF VCF and
#   a binary built without libdeflate: see build.sh), "bad .fai index
#   <path>.fai" (a line that is not a name and four numbers of at most 14
#   digits, a contig whose line layout samtools would not write, or a
#   contig's length or offset of 2^45 or more; a line with an empty name is checked and then ignored, as
#   B.Fasta.parse ignores ">"), "unsupported FASTA <path>" (a byte the .fai
#   layout does not explain: a space or tab, a CR not just before LF, a line
#   break out of place), ".fai index does not match <path>" (fewer letters
#   read than the .fai promises), "FASTA read too large <path>"
#   (a read of more than 2^31 letters, which the program never asks for: a
#   packed buffer holds at most 2^31 bytes; any smaller window is read, its
#   bytes on disk, line breaks included, in parts).
# Arguments, paths and all output are bytes, copied exactly, except that a
# path in an error has each backslash, LF and CR written as \\, \n and \r, so
# the error stays one line.
# Bend's runtime, also trusted, can stop a run with one line "bend: ..." and
# exit code 1: when the heap is exhausted, by the machine or by a block the
# driver allocates for a piece or an answer ("bend: out of memory: ..."), and
# on any number of 2^48 or more, such as a VCF POS that large ("bend: a Nat
# past the largest immediate 2^48-1").

type Fai is Data:
  Fai{len: Nat, off: Nat, lb: Nat, lw: Nat}

# Everything the loop carries: the files, the FASTA path, the .fai index, the
# pieces per batch (k), the reads started at once (g), the pieces read since
# the last empty one (c), and the -o path (out; None for stdout), for errors.
type Io is Type:
  Io{vcf: File, fa: File, ref: String, fai: Map<&2, Maybe<&2, Fai>>, k: Nat, g: Nat, c: Nat, out: Maybe<&2, String>}

# ---------------------------------------------------------------------------
# Effects of the driver (io64.c): a full read at a 64-bit offset, and a write
# of bytes to an inherited descriptor (1: stdout, 2: stderr)
# ---------------------------------------------------------------------------

# Read the next piece of a file's text, up to max bytes, packed (n, block) as
# bytes_enc.bend's enc; n = 0 at the end of the file. The text is the file's
# bytes; with gz = 1, for a file that starts with a BGZF block header, the
# bytes its BGZF blocks decompress to. Fails with an errno, or with 1001 (gzip
# but not BGZF), 1002 (a damaged or cut BGZF block), 1003 (BGZF, but this
# build has no libdeflate).
def Io.read_block(file: File, max: U32, gz: U32) -> IO(File & Result<&1, &1, U32 & String, U32 & Array<U32>>):
  import "./io64.c"
  import "./io64.js"

# Start a read of the shi * 2^32 + slo bytes of the FASTA at offset
# hi * 2^32 + lo (in parts), whose first byte is at column col of a line
# layout of lb letters per line, lw bytes per line (col, lb and lw also as
# 64-bit halves), on a helper thread; answers its ticket. At most 32 are
# started before each is waited for.
def Io.fa_start(file: File, hi: U32, lo: U32, shi: U32, slo: U32, chi: U32, clo: U32, bhi: U32, blo: U32, whi: U32, wlo: U32, want: U32) -> IO(File & U32):
  import "./io64.c"
  import "./io64.js"

# Wait for the read with ticket t; answers (code, (n, block)): code 0 when
# every byte fits the layout and exactly want letters were read (packed as
# enc), 1 when a byte does not fit, 2 when the count differs.
def Io.fa_wait(file: File, t: U32) -> IO(File & Result<&1, &1, U32 & String, U32 & (U32 & Array<U32>)>):
  import "./io64.c"
  import "./io64.js"

# Where and how the output is written (B.Args.output's Sink): the -o path's
# bytes when file is 1 (else stdout), BGZF when z is 1, at level (0 to 9),
# with n compressor threads (0: 16); fa is the open FASTA, which the -o file
# must not be. Called once, before the first step; the file is opened at the
# first Io.out_write (or at Io.out_close). Answers (fa, 0), or 2002 for BGZF
# in a build without libdeflate.
def Io.out_set(fa: File, path: List<&2, U32>, file: U32, z: U32, level: U32, n: U32) -> IO(File & U32):
  import "./io64.c"
  import "./io64.js"

# The index of the -o file, with -W (B.Args.index's Idx): fmt 1 for CSI, 2
# for TBI; path its bytes. Called once, after Io.out_set accepted the output
# and before the first step. Answers 0, 2003 in a build without htslib (no
# index in this build), or 12 (out of memory).
def Io.out_index(fmt: U32, path: List<&2, U32>) -> IO(U32):
  import "./io64.c"
  import "./io64.js"

# Write the first n bytes of a block to the output; answers 0 or the first
# error of the output: an errno (cannot write), 12 (out of memory), 2001 (the
# -o file is an input or stderr's file), or with -W an index error of the
# open (2005, 2006 to 2012: see out_fail).
def Io.out_write(n: U32, a: Array<U32>) -> IO(U32):
  import "./io64.c"
  import "./io64.js"

# The end of the output, for a run ending with exit code c: the last blocks,
# the BGZF end-of-file block only when c is 0, the -o file closed; with -W,
# for c = 0, the index finished, saved and renamed into place. Answers 0 or
# the first error of the output (with -W: 2004 when the index cannot be
# built, 2006 or 2007 when it cannot be written).
def Io.out_close(c: U32) -> IO(U32):
  import "./io64.c"
  import "./io64.js"

def Io.write_fd(fd: U32, data: List<&2, U32>) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./io64.c"
  import "./io64.js"

# Size the VCF read-ahead by the thread count n (0: the default, 16 pieces;
# at most 128). Called once, before the first read; answers 0.
def Io.threads(n: U32) -> IO(U32):
  import "./io64.c"
  import "./io64.js"

# ---------------------------------------------------------------------------
# Bytes and text: one Char per byte, so every byte is copied exactly
# ---------------------------------------------------------------------------

def bytes_str?(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case b <> t:
      SCon{Chr{b}, bytes_str(t)}

def str_bytes?(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> str_bytes(t)

def args_str?(xs: List<List<&2, U32>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      bytes_str(x) <> args_str(t)

# ---------------------------------------------------------------------------
# Errors and output
# ---------------------------------------------------------------------------

# Print "error: <what>" and a LF on stderr, exactly as bytes, and exit 2.
def die?(-A: Type, what: String) -> IO(A):
  do IO<A>:
    r : Result<&1, &1, U32 & String, Unit> <- Io.write_fd(2, str_bytes("error: " ++ what ++ "\n"))
    IO.exit(2)
    IO.die(A, 2, "")

def usage?(-A: Type) -> IO(A):
  do IO<A>:
    r : Result<&1, &1, U32 & String, Unit> <- Io.write_fd(2, str_bytes(B.usage()))
    IO.exit(2)
    IO.die(A, 2, "")

def or_die?(-A: Type, r: Result<&1, &1, U32 & String, A>, what: String) -> IO(A):
  match r:
    case Done{x}:
      IO.pure(A, x)
    case Fail{e}:
      die(A, what)

# A path as it appears in an error: backslash, LF and CR as \\, \n and \r.
def esc?(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      esc.char(Char.is_eq(c, '\\'), Char.is_eq(c, '\n'), Char.is_eq(c, '\r'), c) ++ esc(t)

def esc.char?(bs: Bool, lf: Bool, cr: Bool, c: Char) -> String:
  match bs lf cr:
    case True{} _ _:
      "\\\\"
    case False{} True{} _:
      "\\n"
    case False{} False{} True{}:
      "\\r"
    case False{} False{} False{}:
      SCon{c, SNil{}}

# A failed read of the file at path: "out of memory" for ENOMEM (12), the
# BGZF errors for 1001-1003 (Io.read_block), else "cannot read <path>".
def read_fail?(-A: Type, +e: U32 & String, +path: String) -> IO(A):
  match e:
    case (+code, msg):
      read_fail.go(A, U32.is_eq(code, 12), U32.is_eq(code, 1001), U32.is_eq(code, 1002), U32.is_eq(code, 1003), path)

def read_fail.go?(-A: Type, oom: Bool, gz: Bool, bad: Bool, nolib: Bool, +path: String) -> IO(A):
  match oom gz bad nolib:
    case True{} _ _ _:
      die(A, "out of memory")
    case False{} True{} _ _:
      die(A, "unsupported gzip " ++ esc(path) ++ " (not BGZF; use gzip -dc " ++ esc(path) ++ " | framebender ... /dev/stdin)")
    case False{} False{} True{} _:
      die(A, "bad BGZF " ++ esc(path))
    case False{} False{} False{} True{}:
      die(A, "no BGZF in this build " ++ esc(path))
    case False{} False{} False{} False{}:
      die(A, "cannot read " ++ esc(path))

def or_die_read?(-A: Type, r: Result<&1, &1, U32 & String, A>, +path: String) -> IO(A):
  match r:
    case Done{x}:
      IO.pure(A, x)
    case Fail{+e}:
      read_fail(A, e, path)

def put?(fd: U32, s: String) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Unit> <- Io.write_fd(fd, str_bytes(s))
    or_die(Unit, r, "cannot write")

# The -o path in an error ("-" for stdout).
def out_name?(out: Maybe<&2, String>) -> String:
  match out:
    case None{}:
      "-"
    case Some{p}:
      esc(p)

def cannot_write?(out: Maybe<&2, String>) -> String:
  match out:
    case None{}:
      "cannot write"
    case Some{p}:
      "cannot write " ++ esc(p)

# An error of the output (Io.out_set, Io.out_index, Io.out_write,
# Io.out_close): "out of memory" (12), "output is an input <path>" (2001), "no
# BGZF in this build <path>" (2002), an index error (2003 to 2012:
# ix_msg), else "cannot write" (stdout) or "cannot write <path>".
def out_fail?(-A: Type, +c: U32, +out: Maybe<&2, String>) -> IO(A):
  out_fail.ix(A, U32.is_lt(c, 2003) || U32.is_lt(2012, c), c, out)

def out_fail.ix?(-A: Type, other: Bool, +c: U32, +out: Maybe<&2, String>) -> IO(A):
  match other:
    case True{}:
      out_fail.go(A, U32.is_eq(c, 12), U32.is_eq(c, 2001), U32.is_eq(c, 2002), out)
    case False{}:
      die(A, ix_msg(c, out_name(out)))

# The index errors: 2003 no index in this build, 2004 cannot index, 2005 not
# a regular file, then for <path>.csi and <path>.tbi: 2006/2007 cannot write,
# 2008/2009 an input, 2010/2011 the -o file itself; 2012 an older
# <stem>.csi that htslib reads before <path>.tbi.
def ix_msg?(+c: U32, +p: String) -> String:
  Bool.pick(String, U32.is_eq(c, 2003), "no index in this build " ++ p,
  Bool.pick(String, U32.is_eq(c, 2004), "cannot index " ++ p,
  Bool.pick(String, U32.is_eq(c, 2005), "cannot index " ++ p ++ " (not a regular file)",
  Bool.pick(String, U32.is_eq(c, 2006), "cannot write " ++ p ++ ".csi",
  Bool.pick(String, U32.is_eq(c, 2007), "cannot write " ++ p ++ ".tbi",
  Bool.pick(String, U32.is_eq(c, 2008), "output is an input " ++ p ++ ".csi",
  Bool.pick(String, U32.is_eq(c, 2009), "output is an input " ++ p ++ ".tbi",
  Bool.pick(String, U32.is_eq(c, 2010), "cannot write " ++ p ++ ".csi (it is the -o file)",
  Bool.pick(String, U32.is_eq(c, 2011), "cannot write " ++ p ++ ".tbi (it is the -o file)",
  "cannot write " ++ p ++ ".tbi (htslib would read " ++ ix_stem(p) ++ ".csi first)")))))))))

# <stem>: the path p up to its last '.' after the first byte, as htslib's
# hts_idx_check_local cuts it (p itself when there is none).
def ix_stem?(+p: String) -> String:
  match p:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ix_stem.k(c, ix_cut(t), t)

def ix_stem.k?(+c: Char, m: Maybe<&2, String>, t: String) -> String:
  match m:
    case None{}:
      SCon{c, t}
    case Some{q}:
      SCon{c, q}

# The text before the last '.' of s, or None when s has no '.'.
def ix_cut?(+s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      ix_cut.k(ix_cut(t), Char.is_eq(c, '.'), c)

def ix_cut.k?(m: Maybe<&2, String>, dot: Bool, +c: Char) -> Maybe<&2, String>:
  match m dot:
    case Some{q} _:
      Some{SCon{c, q}}
    case None{} True{}:
      Some{SNil{}}
    case None{} False{}:
      None{}

def out_fail.go?(-A: Type, oom: Bool, inp: Bool, nolib: Bool, out: Maybe<&2, String>) -> IO(A):
  match oom inp nolib:
    case True{} _ _:
      die(A, "out of memory")
    case False{} True{} _:
      die(A, "output is an input " ++ out_name(out))
    case False{} False{} True{}:
      die(A, "no BGZF in this build " ++ out_name(out))
    case False{} False{} False{}:
      die(A, cannot_write(out))

def out_code?(+c: U32, out: Maybe<&2, String>) -> IO(Unit):
  out_code.go(U32.is_zero(c), c, out)

def out_code.go?(ok: Bool, +c: U32, out: Maybe<&2, String>) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      out_fail(Unit, c, out)

# Write an output buffer's bytes (D.view) to the output.
def put_bytes?(out: Maybe<&2, String>, b: D.Bytes) -> IO(Unit):
  match b:
    case D.Bytes{n, a}:
      do IO<Unit>:
        c : U32 <- Io.out_write(n, a)
        out_code(c, out)

def notes_text?(ns: List<&2, B.Note>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> t:
      B.Note.render(n) ++ notes_text(t)

# ---------------------------------------------------------------------------
# Files
# ---------------------------------------------------------------------------

def open?(+path: String) -> IO(File):
  do IO<File>:
    r : Result<&1, &1, U32 & String, File> <- File.open_bytes(str_bytes(path), "r")
    or_die_read(File, r, path)

# The pieces of a whole file, last first, each read with Io.read_block (which
# retries an interrupted read) and taken as its bytes (BY.to_list, which is
# D.view: law to_list_view).
def read_all?(f: File, +path: String, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  do IO<List<&2, List<&2, U32>>>:
    p : File & Result<&1, &1, U32 & String, U32 & Array<U32>> <- Io.read_block(f, piece(), 0)
    read_all.k(p, path, acc)

def read_all.k?(p: File & Result<&1, &1, U32 & String, U32 & Array<U32>>, +path: String, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match p:
    case (f, Fail{+e}):
      read_fail(List<&2, List<&2, U32>>, e, path)
    case (f, Done{(+n, blk)}):
      read_all.more(U32.is_zero(n), f, path, n, blk, acc)

def read_all.more?(eof: Bool, f: File, +path: String, +n: U32, blk: Array<U32>, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match eof:
    case True{}:
      do IO<List<&2, List<&2, U32>>>:
        File.close(f)
        return acc
    case False{}:
      read_all.cons(BY.to_list(D.Bytes{n, blk}, 0, n), f, path, acc)

def read_all.cons?(r: D.Bytes & List<&2, U32>, f: File, +path: String, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match r:
    case (b, bs):
      read_all(f, path, bs <> acc)

def concat_rev?(cs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case c <> t:
      concat_rev(t, List.append(&2, U32, c, acc))

# ---------------------------------------------------------------------------
# The .fai index: name, length, offset, letters per line, bytes per line
# ---------------------------------------------------------------------------

def fai_entry.ok?(ok: Bool, f: Fai) -> Maybe<&2, Fai>:
  match ok:
    case True{}:
      Some{f}
    case False{}:
      None{}

# A .fai entry; None unless all four are numbers, a contig with letters
# has a line layout samtools writes (letters per line > 0, bytes per line =
# letters per line + 1 for LF or + 2 for CR LF), and its length and offset
# are below 2^45 (32 TiB). Then every byte offset of the contig is below
# offset + 3 * length < 2^47: every number the driver computes stays below
# the runtime's 2^48 and every number it passes to Io.fa_start is exact in
# 64 bits.
def fai_entry?(n: Maybe<&2, Nat>, o: Maybe<&2, Nat>, lb: Maybe<&2, Nat>, lw: Maybe<&2, Nat>) -> Maybe<&2, Fai>:
  match n o lb lw:
    case Some{+a} Some{+b} Some{+c} Some{+d}:
      fai_entry.ok((Nat.is_eq(a, 0n) || (Bool.not(Nat.is_eq(c, 0n)) && (Nat.is_eq(d, Nat.add(c, 1n)) || Nat.is_eq(d, Nat.add(c, 2n))))) && Nat.is_lt(a, two45()) && Nat.is_lt(b, two45()), Fai{a, b, c, d})
    case _ _ _ _:
      None{}

def fai_load.keep?(empty: Bool, name: String, f: Fai, m: Map<&2, Maybe<&2, Fai>>) -> Map<&2, Maybe<&2, Fai>>:
  match empty:
    case True{}:
      m
    case False{}:
      Map.set(&2, Maybe<&2, Fai>, m, name, Some{f})

# A number of at most 14 characters: below 10^14, so B.Pos.read stays below
# the runtime's 2^48 (a longer one stops the runtime). Every number of an
# entry fai_entry keeps (below 2^45) has at most 14 digits.
def fai_num?(+s: String) -> Maybe<&2, Nat>:
  fai_num.go(Nat.is_le(String.length(s), 14n), s)

def fai_num.go?(short: Bool, +s: String) -> Maybe<&2, Nat>:
  match short:
    case True{}:
      B.Pos.read(s)
    case False{}:
      None{}

# A line must be exactly five tab-separated fields.
def fai_entry.shape?(ok: Bool, e: Maybe<&2, Fai>) -> Maybe<&2, Fai>:
  match ok:
    case True{}:
      e
    case False{}:
      None{}

# An entry with an empty name (samtools indexes a header ">" under "") is
# checked but not kept: B.Fasta.parse ignores such a contig, so "" is Unknown.
def fai_load.add?(e: Maybe<&2, Fai>, +name: String, t: List<&2, String>, m: Map<&2, Maybe<&2, Fai>>) -> Maybe<&2, Map<&2, Maybe<&2, Fai>>>:
  match e:
    case None{}:
      None{}
    case Some{f}:
      fai_load(t, fai_load.keep(String.is_empty(name), name, f, m))

def fai_load.line?(empty: Bool, +l: String, t: List<&2, String>, m: Map<&2, Maybe<&2, Fai>>) -> Maybe<&2, Map<&2, Maybe<&2, Fai>>>:
  match empty:
    case True{}:
      fai_load(t, m)
    case False{}:
      +fs = B.Rec.fields(l)
      +shape = Nat.is_eq(List.length(&2, String, fs), 5n)
      fai_load.add(fai_entry.shape(shape, fai_entry(fai_num(B.Rec.field(fs, 1n)), fai_num(B.Rec.field(fs, 2n)), fai_num(B.Rec.field(fs, 3n)), fai_num(B.Rec.field(fs, 4n)))), B.Rec.field(fs, 0n), t, m)

# The .fai lines as entries; None if a line is not a name and four numbers.
def fai_load?(ls: List<&2, String>, m: Map<&2, Maybe<&2, Fai>>) -> Maybe<&2, Map<&2, Maybe<&2, Fai>>>:
  match ls:
    case Nil{}:
      Some{m}
    case +l <> t:
      fai_load.line(String.is_empty(l), l, t, m)

# 2^32 (a Nat literal stops at 2^32 - 1).
def two32?() -> Nat:
  Nat.add(4294967295n, 1n)

# 2^45.
def two45?() -> Nat:
  Nat.mul(two32(), 8192n)

# A number below 2^64 as its high and low 32 bits.
def hi?(+x: Nat) -> U32:
  U32.from_nat(Nat.div(x, two32()))

def lo?(+x: Nat) -> U32:
  U32.from_nat(Nat.mod(x, two32()))

# The byte offset of 0-based letter i of a contig.
def fai_at?(+e: Fai, +i: Nat) -> Nat:
  match e:
    case Fai{n, off, +lb, +lw}:
      Nat.add(off, Nat.add(Nat.mul(Nat.div(i, lb), lw), Nat.mod(i, lb)))

# ---------------------------------------------------------------------------
# Answering a reference read
# ---------------------------------------------------------------------------

def answer.k?(p: File & Result<&1, &1, U32 & String, U32 & (U32 & Array<U32>)>, +ref: String, +n: Nat, +a: Nat) -> IO(File & P.Ans):
  match p:
    case (fa, Fail{+e}):
      read_fail(File & P.Ans, e, ref)
    case (fa, Done{(c, (k, blk))}):
      answer.check(c, ref, fa, P.Known{n, a, D.Bytes{k, blk}})

def answer.check?(+c: U32, +ref: String, fa: File, ans: P.Ans) -> IO(File & P.Ans):
  answer.check.go(U32.is_eq(c, 0), U32.is_eq(c, 1), ref, fa, ans)

def answer.check.go?(ok: Bool, bad: Bool, +ref: String, fa: File, ans: P.Ans) -> IO(File & P.Ans):
  match ok bad:
    case True{} _:
      IO.pure(File & P.Ans, (fa, ans))
    case False{} True{}:
      die(File & P.Ans, "unsupported FASTA " ++ esc(ref))
    case False{} False{}:
      die(File & P.Ans, ".fai index does not match " ++ esc(ref))

# A read of an Ask, once started: the contig is unknown; an empty span (the
# contig's length n, from a2); too large (the driver stops when it comes to
# it); a read started with ticket t.
type Pend is Data:
  PUnk{}
  PEmpty{n: Nat, a: Nat}
  PBig{}
  PRead{t: U32, n: Nat, a: Nat}

def start.k?(p: File & U32, +n: Nat, +a2: Nat) -> IO(File & Pend):
  match p:
    case (fa, t):
      IO.pure(File & Pend, (fa, PRead{t, n, a2}))

def start.read.go?(small: Bool, fa: File, +f: Fai, +a2: Nat, +b2: Nat, +o0: Nat, +span: Nat) -> IO(File & Pend):
  match small f:
    case False{} _:
      IO.pure(File & Pend, (fa, PBig{}))
    case True{} Fai{+n, off, +lb, +lw}:
      do IO<File & Pend>:
        p : File & U32 <- Io.fa_start(fa, hi(o0), lo(o0), hi(span), lo(span), hi(Nat.mod(a2, lb)), lo(Nat.mod(a2, lb)), hi(lb), lo(lb), hi(lw), lo(lw), U32.from_nat(Nat.sub(b2, a2)))
        start.k(p, n, a2)

# Start reading letters a2 .. b2 - 1 of contig f (as answer.read reads them).
def start.read?(fa: File, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & Pend):
  +o0 = fai_at(f, a2)
  +o1 = fai_at(f, b2)
  start.read.go(Nat.is_le(Nat.sub(b2, a2), 2147483648n), fa, f, a2, b2, o0, Nat.sub(o1, o0))

def start.span?(some: Bool, fa: File, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & Pend):
  match some f:
    case False{} Fai{n, off, lb, lw}:
      IO.pure(File & Pend, (fa, PEmpty{n, a2}))
    case True{} _:
      start.read(fa, f, a2, b2)

# A read started (as answer.got answers it).
def start.got?(got: Map<&2, Maybe<&2, Fai>> & Maybe<&2, Fai>, fa: File, +a: Nat, +b: Nat) -> IO(Map<&2, Maybe<&2, Fai>> & (File & Pend)):
  match got:
    case (m, None{}):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & Pend), (m, (fa, PUnk{})))
    case (m, Some{Fai{+n, +off, +lb, +lw}}):
      +a2 = Nat.min(a, n)
      +b2 = Nat.min(Nat.max(a2, b), n)
      do IO<Map<&2, Maybe<&2, Fai>> & (File & Pend)>:
        q : File & Pend <- start.span(Nat.is_lt(a2, b2), fa, Fai{n, off, lb, lw}, a2, b2)
        return (m, q)

def starts.cons?(+p: Pend, r: Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)):
  match r:
    case (m, (fa, ps)):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>), (m, (fa, p <> ps)))

def starts.k?(q: Map<&2, Maybe<&2, Fai>> & (File & Pend), t: List<&2, P.Req>) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)):
  match q:
    case (m, (fa, p)):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)>:
        r : Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>) <- starts(t, m, fa)
        starts.cons(p, r)

# Every read of rs started, in order.
def starts?(rs: List<&2, P.Req>, fai: Map<&2, Maybe<&2, Fai>>, fa: File) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)):
  match rs:
    case Nil{}:
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>), (fai, (fa, Nil{})))
    case P.Req{c, a, b} <> t:
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>)>:
        q : Map<&2, Maybe<&2, Fai>> & (File & Pend) <- start.got(Map.get(Maybe<&2, Fai>, None{}, fai, c), fa, a, b)
        starts.k(q, t)

# A started read's answer (as answer.got gives it, its errors included).
def wait1?(p: Pend, fa: File, +ref: String) -> IO(File & P.Ans):
  match p:
    case PUnk{}:
      IO.pure(File & P.Ans, (fa, P.Unknown{}))
    case PEmpty{n, a2}:
      IO.pure(File & P.Ans, (fa, P.Known{n, a2, D.Bytes{0, Array.new(U32, 0n, 0)}}))
    case PBig{}:
      die(File & P.Ans, "FASTA read too large " ++ esc(ref))
    case PRead{t, +n, +a2}:
      do IO<File & P.Ans>:
        q : File & Result<&1, &1, U32 & String, U32 & (U32 & Array<U32>)> <- Io.fa_wait(fa, t)
        answer.k(q, ref, n, a2)

def waits.cons?(+ans: P.Ans, r: File & List<&1, P.Ans>) -> IO(File & List<&1, P.Ans>):
  match r:
    case (fa, as):
      IO.pure(File & List<&1, P.Ans>, (fa, ans <> as))

def waits.k?(q: File & P.Ans, t: List<&2, Pend>, +ref: String) -> IO(File & List<&1, P.Ans>):
  match q:
    case (fa, ans):
      do IO<File & List<&1, P.Ans>>:
        r : File & List<&1, P.Ans> <- waits(t, fa, ref)
        waits.cons(ans, r)

# The answers of the started reads, in order (the first failing one stops the
# driver).
def waits?(ps: List<&2, Pend>, fa: File, +ref: String) -> IO(File & List<&1, P.Ans>):
  match ps:
    case Nil{}:
      IO.pure(File & List<&1, P.Ans>, (fa, Nil{}))
    case p <> t:
      do IO<File & List<&1, P.Ans>>:
        q : File & P.Ans <- wait1(p, fa, ref)
        waits.k(q, t, ref)

# The first k reads, and the rest.
def split?(+k: Nat, rs: List<&2, P.Req>) -> List<&2, P.Req> & List<&2, P.Req>:
  match k rs:
    case 0n rs:
      (Nil{}, rs)
    case 1n+j Nil{}:
      (Nil{}, Nil{})
    case 1n+j +r <> t:
      split.cons(r, split(j, t))

def split.cons?(+r: P.Req, p: List<&2, P.Req> & List<&2, P.Req>) -> List<&2, P.Req> & List<&2, P.Req>:
  match p:
    case (a, b):
      (r <> a, b)

def answers.app?(+as: List<&1, P.Ans>, r: Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match r:
    case (m, (fa, bs)):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), (m, (fa, List.append(&1, P.Ans, as, bs))))

def answers.w?(+n: Nat, w: File & List<&1, P.Ans>, m: Map<&2, Maybe<&2, Fai>>, rest: List<&2, P.Req>, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match w:
    case (fa, as):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)>:
        r : Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>) <- answers(n, rest, m, fa, ref)
        answers.app(as, r)

def answers.s?(+n: Nat, q: Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>), rest: List<&2, P.Req>, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match q:
    case (m, (fa, ps)):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)>:
        w : File & List<&1, P.Ans> <- waits(ps, fa, ref)
        answers.w(n, w, m, rest, ref)

def answers.g?(+n: Nat, p: List<&2, P.Req> & List<&2, P.Req>, fai: Map<&2, Maybe<&2, Fai>>, fa: File, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match p:
    case (g, rest):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)>:
        q : Map<&2, Maybe<&2, Fai>> & (File & List<&2, Pend>) <- starts(g, fai, fa)
        answers.s(n, q, rest, ref)

# The answers to the reads rs, in order: up to n at a time (n at least 1: 32,
# or --threads N), each group's reads started at once (in parallel) and then
# taken in order.
def answers?(+n: Nat, rs: List<&2, P.Req>, fai: Map<&2, Maybe<&2, Fai>>, fa: File, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match rs:
    case Nil{}:
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), (fai, (fa, Nil{})))
    case +r <> +t:
      answers.g(n, split(n, r <> t), fai, fa, ref)

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

# The size of a piece of the VCF file read at once (3.5 MB: with the bytes
# carried over it fits a 4 MB output buffer).
def piece?() -> U32:
  3670016

def loop.input?(+n: U32, blk: Array<U32>, st: Norm.St) -> Norm.Step:
  loop.input.go(U32.is_zero(n), n, blk, st)

def loop.input.go?(eof: Bool, +n: U32, blk: Array<U32>, st: Norm.St) -> Norm.Step:
  match eof:
    case True{}:
      Norm.step(st, P.Eof{})
    case False{}:
      Norm.step(st, P.Chunk{D.Bytes{n, blk}})

# The next piece: after k pieces, an empty one (it ends the machine's batch),
# else the next piece of the file.
def loop.piece?(full: Bool, vcf: File, fa: File, +ref: String, fai: Map<&2, Maybe<&2, Fai>>, +k: Nat, +g: Nat, +c: Nat, +out: Maybe<&2, String>, +vpath: String, st: Norm.St) -> IO(Unit):
  match full:
    case True{}:
      emit(Io{vcf, fa, ref, fai, k, g, 0n, out}, vpath, Norm.step(st, P.Chunk{D.Bytes{0, Array.new(U32, 0n, 0)}}))
    case False{}:
      do IO<Unit>:
        p : File & Result<&1, &1, U32 & String, U32 & Array<U32>> <- Io.read_block(vcf, piece(), 1)
        loop.more(p, fa, ref, vpath, fai, k, g, 1n+c, out, st)

# At the end: the output finished (Io.out_close; the BGZF end-of-file block
# only for code 0), then exit with the machine's code.
def loop?(io: Io, +vpath: String, st: Norm.St, next: P.Next) -> IO(Unit):
  match io:
    case Io{vcf, fa, +ref, fai, +k, +g, +c, +out}:
      match next:
        case P.Finish{+code}:
          do IO<Unit>:
            File.close(vcf)
            File.close(fa)
            r : U32 <- Io.out_close(U32.from_nat(code))
            out_code(r, out)
            IO.exit(U32.from_nat(code))
        case P.More{}:
          loop.piece(Nat.is_le(k, c), vcf, fa, ref, fai, k, g, c, out, vpath, st)
        case P.Ask{rs}:
          do IO<Unit>:
            q : Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>) <- answers(g, rs, fai, fa, ref)
            loop.ref(q, vcf, ref, k, g, c, out, vpath, st)

def loop.ref?(q: Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), vcf: File, +ref: String, +k: Nat, +g: Nat, +c: Nat, +out: Maybe<&2, String>, +vpath: String, st: Norm.St) -> IO(Unit):
  match q:
    case (fai, (fa, as)):
      emit(Io{vcf, fa, ref, fai, k, g, c, out}, vpath, Norm.step(st, P.Ref{as}))

def loop.more?(p: File & Result<&1, &1, U32 & String, U32 & Array<U32>>, fa: File, +ref: String, +vpath: String, fai: Map<&2, Maybe<&2, Fai>>, +k: Nat, +g: Nat, +c: Nat, +out: Maybe<&2, String>, st: Norm.St) -> IO(Unit):
  match p:
    case (vcf, Fail{+e}):
      read_fail(Unit, e, vpath)
    case (vcf, Done{(n, blk)}):
      emit(Io{vcf, fa, ref, fai, k, g, c, out}, vpath, loop.input(n, blk, st))

# Write what a step wrote, then go on with what it wants next.
def emit?(io: Io, +vpath: String, s: Norm.Step) -> IO(Unit):
  match io s:
    case Io{vcf, fa, +ref, fai, +k, +g, +c, +out} Norm.Step{st, o, ns, next}:
      do IO<Unit>:
        put_bytes(out, o)
        put(2, notes_text(ns))
        loop(Io{vcf, fa, ref, fai, k, g, c, out}, vpath, st, next)

def bool_u32?(b: Bool) -> U32:
  Bool.pick(U32, b, 1, 0)

def path_bytes?(m: Maybe<&2, String>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{p}:
      str_bytes(p)

# The index format for Io.out_index.
def ifmt_u32?(f: B.IFmt) -> U32:
  match f:
    case B.Csi{}:
      1
    case B.Tbi{}:
      2

# With -W, the index of the output (Io.out_index), once the output is set.
def run.ix?(ix: B.Idx, +out: Maybe<&2, String>) -> IO(Unit):
  match ix:
    case B.NoIdx{}:
      IO.pure(Unit, Unit{})
    case B.Idx{f, p}:
      do IO<Unit>:
        r : U32 <- Io.out_index(ifmt_u32(f), str_bytes(p))
        out_code(r, out)
    case B.BadIdx{}:
      die(Unit, "-W needs a BGZF -o file")

# Start the loop once the output is set (Io.out_set's answer q).
def run.set?(q: File & U32, v: File, +ref: String, fai: Map<&2, Maybe<&2, Fai>>, +k: Nat, +g: Nat, +out: Maybe<&2, String>, +vcf: String, st: Norm.St, ix: B.Idx) -> IO(Unit):
  match q:
    case (fa, +r):
      do IO<Unit>:
        out_code(r, out)
        run.ix(ix, out)
        loop(Io{v, fa, ref, fai, k, g, 0n, out}, vcf, st, P.More{})

def run.fai?(m: Maybe<&2, Map<&2, Maybe<&2, Fai>>>, st: Norm.St, +ref: String, +vcf: String, +k: Nat, +g: Nat, sk: B.Sink, +n: Nat, ix: B.Idx) -> IO(Unit):
  match m sk:
    case None{} _:
      die(Unit, "bad .fai index " ++ esc(ref ++ ".fai"))
    case Some{fai} B.Sink{+out, z, level}:
      do IO<Unit>:
        fa : File <- open(ref)
        v : File <- open(vcf)
        q : File & U32 <- Io.out_set(fa, path_bytes(out), bool_u32(Maybe.is_some(&2, String, out)), bool_u32(z), U32.from_nat(level), U32.from_nat(n))
        run.set(q, v, ref, fai, k, g, out, vcf, st, ix)

def run?(st: Norm.St, +ref: String, +vcf: String, +k: Nat, +g: Nat, sk: B.Sink, +n: Nat, ix: B.Idx) -> IO(Unit):
  do IO<Unit>:
    fi : File <- open(ref ++ ".fai")
    cs : List<&2, List<&2, U32>> <- read_all(fi, ref ++ ".fai", Nil{})
    run.fai(fai_load(String.split(bytes_str(concat_rev(cs, Nil{})), '\n'), Map.new(&2, Maybe<&2, Fai>)), st, ref, vcf, k, g, sk, n, ix)

# A command line Norm.start accepted has an output (B.Args.output; output_ok
# in proof_f_out.bend) and an index answer (B.Args.index; index_ok in
# proof_f_index.bend): None there is an internal error, never a fallback.
# BadIdx (-W with stdout or plain output) stops here, before any input is
# opened.
def main.k?(b: Norm.Begin, m: Maybe<&2, B.Sink>, x: Maybe<&2, B.Idx>, +k: Nat, +g: Nat, +n: Nat) -> IO(Unit):
  match b m x:
    case Norm.Usage{} _ _:
      usage(Unit)
    case Norm.Begin{st, ref, vcf} Some{sk} Some{B.BadIdx{}}:
      die(Unit, "-W needs a BGZF -o file")
    case Norm.Begin{st, ref, vcf} Some{sk} Some{ix}:
      run(st, ref, vcf, k, g, sk, n, ix)
    case Norm.Begin{st, ref, vcf} None{} _:
      die(Unit, "internal error: no output")
    case Norm.Begin{st, ref, vcf} Some{sk} None{}:
      die(Unit, "internal error: no index")

# The thread count n (0 when none) sizes the driver's work: the read-ahead
# (Io.threads), the pieces per batch (16, or n), the reads started at once
# (32, or n) and the BGZF compressor threads (16, or n). n is at most 128
# (Args.threads, proof_f_args.bend's threads_ok).
def main.t?(+n: Nat, b: Norm.Begin, m: Maybe<&2, B.Sink>, x: Maybe<&2, B.Idx>) -> IO(Unit):
  do IO<Unit>:
    r : U32 <- Io.threads(U32.from_nat(n))
    main.k(b, m, x, Bool.pick(Nat, Nat.is_eq(n, 0n), 16n, n), Bool.pick(Nat, Nat.is_eq(n, 0n), 32n, n), n)

def main.n?(+xs: List<&2, String>) -> IO(Unit):
  main.t(Maybe.default(&2, Nat, B.Args.threads(xs), 0n), Norm.start(xs), B.Args.output(xs), B.Args.index(xs))

def main.args?(args: List<List<&2, U32>>) -> IO(Unit):
  match args:
    case Nil{}:
      usage(Unit)
    case prog <> rest:
      main.n(args_str(rest))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<List<&2, U32>> <- IO.args_bytes()
    main.args(args)
