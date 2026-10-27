import Base
import ./types.bend as B
import ./protocol.bend as P
import ./norm.bend as Norm

# framebender: the driver (trusted, not proven; see the comment on law machine
# in MACHINE.bend).
#
#   framebender norm -f ref.fa [-c e|w] [-w N] in.vcf > out.vcf
#
# It only runs the proven machine (Norm.start, Norm.step): it reads the VCF
# file in pieces, answers the reads of each Ask in order with the contig's
# letters at the .fai offsets (line breaks removed), writes what the machine
# writes, and exits with the machine's code. Every error of its own prints one
# line "error: ..." and exits with code 2:
#   usage (B.usage), "cannot read <path>", "cannot write" (stdout/stderr),
#   "bad .fai index <path>.fai" (a line that is not name and four numbers, or
#   a contig with letters but no letters per line), "unsupported FASTA <path>"
#   (a byte the .fai layout does not explain: a space or tab, a CR not just
#   before LF, a line break out of place), ".fai index does not match <path>"
#   (fewer letters read than the .fai promises), "FASTA read too large <path>"
#   (one read of 4 GiB or more).
# Arguments, paths and all output are bytes, copied exactly.

type Fai is Data:
  Fai{len: Nat, off: Nat, lb: Nat, lw: Nat}

# Everything the loop carries: the files, the FASTA path and the .fai index.
type Io is Type:
  Io{vcf: File, fa: File, ref: String, fai: Map<&2, Maybe<&2, Fai>>}

# ---------------------------------------------------------------------------
# Effects of the driver (io64.c): a full read at a 64-bit offset, and a write
# of bytes to an inherited descriptor (1: stdout, 2: stderr)
# ---------------------------------------------------------------------------

def Io.pread_full(file: File, hi: U32, lo: U32, n: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, U32>>):
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

def put?(fd: U32, s: String) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Unit> <- Io.write_fd(fd, str_bytes(s))
    or_die(Unit, r, "cannot write")

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
    or_die(File, r, "cannot read " ++ path)

def read_all?(f: File, +path: String, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  do IO<List<&2, List<&2, U32>>>:
    p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4194304)
    read_all.k(p, path, acc)

def read_all.k?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +path: String, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match p:
    case (f, r):
      do IO<List<&2, List<&2, U32>>>:
        bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read " ++ path)
        read_all.more(f, path, bs, acc)

def read_all.more?(f: File, +path: String, +bs: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match bs:
    case Nil{}:
      do IO<List<&2, List<&2, U32>>>:
        File.close(f)
        return acc
    case _:
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

# A .fai entry; None unless all four are numbers, and a contig with letters
# has letters on its lines.
def fai_entry?(n: Maybe<&2, Nat>, o: Maybe<&2, Nat>, lb: Maybe<&2, Nat>, lw: Maybe<&2, Nat>) -> Maybe<&2, Fai>:
  match n o lb lw:
    case Some{+a} Some{b} Some{+c} Some{d}:
      fai_entry.ok(Nat.is_eq(a, 0n) || Bool.not(Nat.is_eq(c, 0n)), Fai{a, b, c, d})
    case _ _ _ _:
      None{}

def fai_load.add?(e: Maybe<&2, Fai>, name: String, t: List<&2, String>, m: Map<&2, Maybe<&2, Fai>>) -> Maybe<&2, Map<&2, Maybe<&2, Fai>>>:
  match e:
    case None{}:
      None{}
    case Some{f}:
      fai_load(t, Map.set(&2, Maybe<&2, Fai>, m, name, Some{f}))

def fai_load.line?(empty: Bool, +l: String, t: List<&2, String>, m: Map<&2, Maybe<&2, Fai>>) -> Maybe<&2, Map<&2, Maybe<&2, Fai>>>:
  match empty:
    case True{}:
      fai_load(t, m)
    case False{}:
      +fs = B.Rec.fields(l)
      fai_load.add(fai_entry(B.Pos.read(B.Rec.field(fs, 1n)), B.Pos.read(B.Rec.field(fs, 2n)), B.Pos.read(B.Rec.field(fs, 3n)), B.Pos.read(B.Rec.field(fs, 4n))), B.Rec.field(fs, 0n), t, m)

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

# The byte offset of 0-based letter i of a contig.
def fai_at?(+e: Fai, +i: Nat) -> Nat:
  match e:
    case Fai{n, off, +lb, +lw}:
      Nat.add(off, Nat.add(Nat.mul(Nat.div(i, lb), lw), Nat.mod(i, lb)))

# ---------------------------------------------------------------------------
# Answering a reference read
# ---------------------------------------------------------------------------

def letters.put?(skip: Bool, b: U32, rest: String) -> String:
  match skip:
    case True{}:
      rest
    case False{}:
      SCon{Chr{b}, rest}

# The bytes read, without line breaks.
def letters?(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case +b <> t:
      letters.put(U32.is_eq(b, 10) || U32.is_eq(b, 13), b, letters(t))

# Byte b at column col of a line of the .fai layout (lb letters, then the
# line break: LF, or CR LF when lw = lb + 2) is where the layout puts it.
def fits.byte?(+b: U32, +col: Nat, +lb: Nat, +lw: Nat) -> Bool:
  Bool.pick(Bool, U32.is_eq(b, 10), Nat.is_eq(Nat.add(col, 1n), lw),
  Bool.pick(Bool, U32.is_eq(b, 13), Nat.is_eq(col, lb) && Nat.is_eq(lw, Nat.add(lb, 2n)),
  Bool.not(U32.is_eq(b, 32) || U32.is_eq(b, 9)) && Nat.is_lt(col, lb)))

# Every byte read from file offset x on fits the layout of the contig that
# starts at off.
def fits?(bs: List<&2, U32>, +x: Nat, +off: Nat, +lb: Nat, +lw: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> t:
      fits.byte(b, Nat.mod(Nat.sub(x, off), lw), lb, lw) && fits(t, 1n+x, off, lb, lw)

def answer.check?(fit: Bool, full: Bool, +ref: String, fa: File, ans: P.Ans) -> IO(File & P.Ans):
  match fit full:
    case False{} _:
      die(File & P.Ans, "unsupported FASTA " ++ ref)
    case True{} False{}:
      die(File & P.Ans, ".fai index does not match " ++ ref)
    case True{} True{}:
      IO.pure(File & P.Ans, (fa, ans))

def answer.k?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +ref: String, +f: Fai, +a: Nat, +b: Nat, +o0: Nat) -> IO(File & P.Ans):
  match p f:
    case (fa, r) Fai{+n, +off, +lb, +lw}:
      do IO<File & P.Ans>:
        +bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read " ++ ref)
        +s : String = letters(bs)
        answer.check(fits(bs, o0, off, lb, lw), Nat.is_eq(String.length(s), Nat.sub(b, a)), ref, fa, P.Known{n, a, s})

def answer.read.go?(small: Bool, fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat, +o0: Nat, +span: Nat) -> IO(File & P.Ans):
  match small:
    case False{}:
      die(File & P.Ans, "FASTA read too large " ++ ref)
    case True{}:
      do IO<File & P.Ans>:
        p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- Io.pread_full(fa, U32.from_nat(Nat.div(o0, two32())), U32.from_nat(Nat.mod(o0, two32())), U32.from_nat(span))
        answer.k(p, ref, f, a2, b2, o0)

# Read letters a2 .. b2 - 1 of contig f (a2 < b2 <= its length).
def answer.read?(fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & P.Ans):
  +o0 = fai_at(f, a2)
  +o1 = fai_at(f, b2)
  answer.read.go(Nat.is_lt(Nat.sub(o1, o0), two32()), fa, ref, f, a2, b2, o0, Nat.sub(o1, o0))

def answer.span?(some: Bool, fa: File, +ref: String, +f: Fai, +a2: Nat, +b2: Nat) -> IO(File & P.Ans):
  match some f:
    case False{} Fai{n, off, lb, lw}:
      IO.pure(File & P.Ans, (fa, P.Known{n, a2, ""}))
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

def answers.cons?(+ans: P.Ans, r: Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)):
  match r:
    case (m, (fa, as)):
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>), (m, (fa, ans <> as)))

def answers.k?(q: Map<&2, Maybe<&2, Fai>> & (File & P.Ans), t: List<&2, P.Req>, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)):
  match q:
    case (m, (fa, ans)):
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)>:
        r : Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>) <- answers(t, m, fa, ref)
        answers.cons(ans, r)

# The answers to the reads rs, in order.
def answers?(rs: List<&2, P.Req>, fai: Map<&2, Maybe<&2, Fai>>, fa: File, +ref: String) -> IO(Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)):
  match rs:
    case Nil{}:
      IO.pure(Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>), (fai, (fa, Nil{})))
    case P.Req{c, a, b} <> t:
      do IO<Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>)>:
        q : Map<&2, Maybe<&2, Fai>> & (File & P.Ans) <- answer.got(Map.get(Maybe<&2, Fai>, None{}, fai, c), fa, ref, a, b)
        answers.k(q, t, ref)

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

def loop.input?(bs: List<&2, U32>, st: Norm.St) -> Norm.Step:
  match bs:
    case Nil{}:
      Norm.step(st, P.Eof{})
    case b <> t:
      Norm.step(st, P.Chunk{bytes_str(b <> t)})

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
            p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(vcf, 65536)
            loop.more(p, fa, ref, vpath, fai, st)
        case P.Ask{rs}:
          do IO<Unit>:
            q : Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>) <- answers(rs, fai, fa, ref)
            loop.ref(q, vcf, ref, vpath, st)

def loop.ref?(q: Map<&2, Maybe<&2, Fai>> & (File & List<&2, P.Ans>), vcf: File, +ref: String, +vpath: String, st: Norm.St) -> IO(Unit):
  match q:
    case (fai, (fa, as)):
      emit(Io{vcf, fa, ref, fai}, vpath, Norm.step(st, P.Ref{as}))

def loop.more?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, fa: File, +ref: String, +vpath: String, fai: Map<&2, Maybe<&2, Fai>>, st: Norm.St) -> IO(Unit):
  match p:
    case (vcf, r):
      do IO<Unit>:
        +bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read " ++ vpath)
        emit(Io{vcf, fa, ref, fai}, vpath, loop.input(bs, st))

# Write what a step wrote, then go on with what it wants next.
def emit?(io: Io, +vpath: String, s: Norm.Step) -> IO(Unit):
  match s:
    case Norm.Step{st, o, ns, next}:
      do IO<Unit>:
        put(1, o)
        put(2, notes_text(ns))
        loop(io, vpath, st, next)

def run.fai?(m: Maybe<&2, Map<&2, Maybe<&2, Fai>>>, st: Norm.St, +ref: String, +vcf: String) -> IO(Unit):
  match m:
    case None{}:
      die(Unit, "bad .fai index " ++ ref ++ ".fai")
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
