import Base
import ./types.bend as B
import ./protocol.bend as P
import ./norm_par.bend as Norm
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY

# framebender: the driver (trusted, not proven; see the comment on law machine
# in MACHINE.bend).
#
#   framebender norm -f ref.fa [-c e|w] [-w N] in.vcf > out.vcf
#
# It only runs the proven machine (Norm.start, Norm.step): it reads the VCF
# file in pieces (its bytes, or for a BGZF file the bytes its blocks
# decompress to), answers the reads of each Ask in order with the contig's
# letters at the .fai offsets (line breaks removed), writes what the machine
# writes, and exits with the machine's code. Every error of its own prints one
# line "error: ..." and exits with code 2:
#   usage (B.usage), "cannot read <path>", "cannot write" (stdout/stderr),
#   "out of memory" (no room for a read's buffer or for libdeflate's
#   decompressor), "unsupported gzip <path> (not BGZF; use gzip -dc
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

# Everything the loop carries: the files, the FASTA path and the .fai index.
type Io is Type:
  Io{vcf: File, fa: File, ref: String, fai: Map<&2, Maybe<&2, Fai>>}

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

# Read the shi * 2^32 + slo bytes of the FASTA at offset hi * 2^32 + lo (in
# parts), whose first byte is at column col of a line layout of lb letters
# per line, lw bytes per line (col, lb and lw also as 64-bit halves);
# answers (code, (n, block)): code 0 when every byte fits the layout and
# exactly want letters were read (packed as enc), 1 when a byte does not
# fit, 2 when the count differs.
def Io.fa_read(file: File, hi: U32, lo: U32, shi: U32, slo: U32, chi: U32, clo: U32, bhi: U32, blo: U32, whi: U32, wlo: U32, want: U32) -> IO(File & Result<&1, &1, U32 & String, U32 & (U32 & Array<U32>)>):
  import "./io64.c"
  import "./io64.js"

# Write the first n bytes of a block to an inherited descriptor (1: stdout);
# answers 0 or an errno (EINVAL if the block is not a packed buffer).
def Io.write_block(fd: U32, n: U32, a: Array<U32>) -> IO(U32):
  import "./io64.c"
  import "./io64.js"

def Io.write_fd(fd: U32, data: List<&2, U32>) -> IO(Result<&1, &1, U32 & String, Unit>):
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

def put_code?(c: U32) -> IO(Unit):
  put_ok(U32.is_zero(c))

def put_ok?(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      die(Unit, "cannot write")

# Write an output buffer's bytes (D.view) to stdout.
def put_bytes?(b: D.Bytes) -> IO(Unit):
  match b:
    case D.Bytes{n, a}:
      do IO<Unit>:
        c : U32 <- Io.write_block(1, n, a)
        put_code(c)

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
# the runtime's 2^48 and every number it passes to Io.fa_read is exact in
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

def answer.read.go?(small: Bool, fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat, +o0: Nat, +span: Nat) -> IO(File & P.Ans):
  match small f:
    case False{} _:
      die(File & P.Ans, "FASTA read too large " ++ esc(ref))
    case True{} Fai{+n, off, +lb, +lw}:
      do IO<File & P.Ans>:
        p : File & Result<&1, &1, U32 & String, U32 & (U32 & Array<U32>)> <- Io.fa_read(fa, hi(o0), lo(o0), hi(span), lo(span), hi(Nat.mod(a2, lb)), lo(Nat.mod(a2, lb)), hi(lb), lo(lb), hi(lw), lo(lw), U32.from_nat(Nat.sub(b2, a2)))
        answer.k(p, ref, n, a2)

# Read letters a2 .. b2 - 1 of contig f (a2 < b2 <= its length, at most 2^31
# letters): the bytes from the .fai offset of letter a2 up to that of letter
# b2.
def answer.read?(fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & P.Ans):
  +o0 = fai_at(f, a2)
  +o1 = fai_at(f, b2)
  answer.read.go(Nat.is_le(Nat.sub(b2, a2), 2147483648n), fa, ref, f, a2, b2, o0, Nat.sub(o1, o0))

def answer.span?(some: Bool, fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & P.Ans):
  match some f:
    case False{} Fai{n, off, lb, lw}:
      IO.pure(File & P.Ans, (fa, P.Known{n, a2, D.Bytes{0, Array.new(U32, 0n, 0)}}))
    case True{} _:
      answer.read(fa, ref, f, a2, b2)

# The truthful answer: Unknown when the .fai has no such contig; else the
# contig's length and its letters from a2 = min(a, n) up to min(max(a2, b), n).
def answer.got?(got: Map<&2, Maybe<&2, Fai>> & Maybe<&2, Fai>, fa: File, +ref: String, +a: Nat, +b: Nat) -> IO(Map<&2, Maybe<&2, Fai>> & (File & P.Ans)):
  match got:
    case (m, None{}):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & P.Ans), (m, (fa, P.Unknown{})))
    case (m, Some{Fai{+n, +off, +lb, +lw}}):
      +a2 = Nat.min(a, n)
      +b2 = Nat.min(Nat.max(a2, b), n)
      do IO<Map<&2, Maybe<&2, Fai>> & (File & P.Ans)>:
        q : File & P.Ans <- answer.span(Nat.is_lt(a2, b2), fa, ref, Fai{n, off, lb, lw}, a2, b2)
        return (m, q)

def answers.cons?(+ans: P.Ans, r: Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match r:
    case (m, (fa, as)):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), (m, (fa, ans <> as)))

def answers.k?(q: Map<&2, Maybe<&2, Fai>> & (File & P.Ans), t: List<&2, P.Req>, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match q:
    case (m, (fa, ans)):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)>:
        r : Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>) <- answers(t, m, fa, ref)
        answers.cons(ans, r)

# The answers to the reads rs, in order.
def answers?(rs: List<&2, P.Req>, fai: Map<&2, Maybe<&2, Fai>>, fa: File, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)):
  match rs:
    case Nil{}:
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), (fai, (fa, Nil{})))
    case P.Req{c, a, b} <> t:
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>)>:
        q : Map<&2, Maybe<&2, Fai>> & (File & P.Ans) <- answer.got(Map.get(Maybe<&2, Fai>, None{}, fai, c), fa, ref, a, b)
        answers.k(q, t, ref)

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

def loop?(io: Io, +vpath: String, st: Norm.St, next: P.Next) -> IO(Unit):
  match io:
    case Io{vcf, fa, +ref, fai}:
      match next:
        case P.Finish{code}:
          do IO<Unit>:
            File.close(vcf)
            File.close(fa)
            IO.exit(U32.from_nat(code))
        case P.More{}:
          do IO<Unit>:
            p : File & Result<&1, &1, U32 & String, U32 & Array<U32>> <- Io.read_block(vcf, piece(), 1)
            loop.more(p, fa, ref, vpath, fai, st)
        case P.Ask{rs}:
          do IO<Unit>:
            q : Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>) <- answers(rs, fai, fa, ref)
            loop.ref(q, vcf, ref, vpath, st)

def loop.ref?(q: Map<&2, Maybe<&2, Fai>> & (File & List<&1, P.Ans>), vcf: File, +ref: String, +vpath: String, st: Norm.St) -> IO(Unit):
  match q:
    case (fai, (fa, as)):
      emit(Io{vcf, fa, ref, fai}, vpath, Norm.step(st, P.Ref{as}))

def loop.more?(p: File & Result<&1, &1, U32 & String, U32 & Array<U32>>, fa: File, +ref: String, +vpath: String, fai: Map<&2, Maybe<&2, Fai>>, st: Norm.St) -> IO(Unit):
  match p:
    case (vcf, Fail{+e}):
      read_fail(Unit, e, vpath)
    case (vcf, Done{(n, blk)}):
      emit(Io{vcf, fa, ref, fai}, vpath, loop.input(n, blk, st))

# Write what a step wrote, then go on with what it wants next.
def emit?(io: Io, +vpath: String, s: Norm.Step) -> IO(Unit):
  match s:
    case Norm.Step{st, o, ns, next}:
      do IO<Unit>:
        put_bytes(o)
        put(2, notes_text(ns))
        loop(io, vpath, st, next)

def run.fai?(m: Maybe<&2, Map<&2, Maybe<&2, Fai>>>, st: Norm.St, +ref: String, +vcf: String) -> IO(Unit):
  match m:
    case None{}:
      die(Unit, "bad .fai index " ++ esc(ref ++ ".fai"))
    case Some{fai}:
      do IO<Unit>:
        fa : File <- open(ref)
        v : File <- open(vcf)
        loop(Io{v, fa, ref, fai}, vcf, st, P.More{})

def run?(st: Norm.St, +ref: String, +vcf: String) -> IO(Unit):
  do IO<Unit>:
    fi : File <- open(ref ++ ".fai")
    cs : List<&2, List<&2, U32>> <- read_all(fi, ref ++ ".fai", Nil{})
    run.fai(fai_load(String.split(bytes_str(concat_rev(cs, Nil{})), '\n'), Map.new(&2, Maybe<&2, Fai>)), st, ref, vcf)

def main.k?(b: Norm.Begin) -> IO(Unit):
  match b:
    case Norm.Usage{}:
      usage(Unit)
    case Norm.Begin{st, ref, vcf}:
      run(st, ref, vcf)

def main.args?(args: List<List<&2, U32>>) -> IO(Unit):
  match args:
    case Nil{}:
      usage(Unit)
    case prog <> rest:
      main.k(Norm.start(args_str(rest)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<List<&2, U32>> <- IO.args_bytes()
    main.args(args)
