import Base
import ./types.bend as B
import ./norm.bend as Norm

# framebender: the driver (trusted, not proven; see the comment on law machine
# in LAWS.bend).
#
#   framebender norm -f ref.fa [-c e|w] [-w N] in.vcf > out.vcf
#
# It only runs the proven machine (Norm.start, Norm.step): it reads the VCF
# file in pieces, answers each reference read with the contig's letters at the
# .fai offsets (line breaks removed), writes what the machine writes, and exits
# with the machine's code. Usage errors and unreadable files exit with code 2.

type Fai is Data:
  Fai{len: Nat, off: Nat, lb: Nat, lw: Nat}

# Everything the loop carries: the files and the .fai index.
type Io is Type:
  Io{vcf: File, fa: File, out: File, err: File, fai: Map<&2, Fai>}

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

def num?(s: String) -> Nat:
  Maybe.default(&2, Nat, B.Pos.read(s), 0n)

def args_data?(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      x <> args_data(t)

# ---------------------------------------------------------------------------
# The .fai index: name, length, offset, letters per line, bytes per line
# ---------------------------------------------------------------------------

def fai_add?(m: Map<&2, Fai>, line: String) -> Map<&2, Fai>:
  +fs = B.Rec.fields(line)
  Map.set(&2, Fai, m, B.Rec.field(fs, 0n), Fai{num(B.Rec.field(fs, 1n)), num(B.Rec.field(fs, 2n)), num(B.Rec.field(fs, 3n)), num(B.Rec.field(fs, 4n))})

def fai_load?(ls: List<&2, String>, m: Map<&2, Fai>) -> Map<&2, Fai>:
  match ls:
    case Nil{}:
      m
    case l <> t:
      fai_load(t, fai_add(m, l))

# The byte offset of 0-based letter i of a contig.
def fai_at?(+e: Fai, +i: Nat) -> Nat:
  match e:
    case Fai{n, off, +lb, +lw}:
      Nat.add(off, Nat.add(Nat.mul(Nat.div(i, lb), lw), Nat.mod(i, lb)))

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

def has_blank?(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +b <> t:
      U32.is_eq(b, 32) || U32.is_eq(b, 9) || has_blank(t)

# ---------------------------------------------------------------------------
# IO helpers
# ---------------------------------------------------------------------------

def or_die?(-A: Type, r: Result<&1, &1, U32 & String, A>, what: String) -> IO(A):
  match r:
    case Done{x}:
      IO.pure(A, x)
    case Fail{e}:
      match e:
        case (code, msg):
          IO.die(A, 2, "error: " ++ what ++ "\n")

def open?(+path: String, mode: String) -> IO(File):
  do IO<File>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, mode)
    or_die(File, r, "cannot read " ++ path)

def read_all?(f: File, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  do IO<List<&2, List<&2, U32>>>:
    p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 4194304)
    read_all.k(p, acc)

def read_all.k?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match p:
    case (f, r):
      do IO<List<&2, List<&2, U32>>>:
        bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read the .fai index")
        read_all.more(f, bs, acc)

def read_all.more?(f: File, +bs: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> IO(List<&2, List<&2, U32>>):
  match bs:
    case Nil{}:
      do IO<List<&2, List<&2, U32>>>:
        File.close(f)
        return acc
    case _:
      read_all(f, bs <> acc)

def concat_rev?(cs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case c <> t:
      concat_rev(t, List.append(&2, U32, c, acc))

def write?(f: File, s: String) -> IO(File):
  do IO<File>:
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, str_bytes(s))
    write.k(p)

def write.k?(p: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  match p:
    case (f, r):
      do IO<File>:
        u : Unit <- or_die(Unit, r, "cannot write")
        return f

def notes_text?(ns: List<&2, B.Note>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> t:
      B.Note.render(n) ++ notes_text(t)

# ---------------------------------------------------------------------------
# Answering a reference read
# ---------------------------------------------------------------------------

def answer.k?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, +a: Nat) -> IO(File & B.Ans):
  match p:
    case (fa, r):
      do IO<File & B.Ans>:
        +bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read the FASTA file")
        answer.check(has_blank(bs), fa, B.Known{n, a, letters(bs)})

def answer.check?(blank: Bool, fa: File, ans: B.Ans) -> IO(File & B.Ans):
  match blank:
    case True{}:
      IO.die(File & B.Ans, 2, "error: unsupported FASTA (spaces or tabs in sequence lines)\n")
    case False{}:
      IO.pure(File & B.Ans, (fa, ans))

def answer.go?(unknown: Bool, fa: File, +fe: Fai, +a: Nat, +b: Nat) -> IO(File & B.Ans):
  match unknown:
    case True{}:
      IO.pure(File & B.Ans, (fa, B.Unknown{}))
    case False{}:
      match fe:
        case Fai{+n, off, lb, lw}:
          +a2 = Nat.min(a, n)
          +b2 = Nat.min(Nat.max(a2, b), n)
          +o0 = fai_at(Fai{n, off, lb, lw}, a2)
          +o1 = fai_at(Fai{n, off, lb, lw}, b2)
          do IO<File & B.Ans>:
            p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(fa, U32.from_nat(o0), U32.from_nat(Nat.sub(o1, o0)))
            answer.k(p, n, a2)

def answer.got?(got: Map<&2, Fai> & Fai, fa: File, +a: Nat, +b: Nat) -> IO(Map<&2, Fai> & (File & B.Ans)):
  match got:
    case (m, +fe):
      match fe:
        case Fai{+n, off, +lb, lw}:
          do IO<Map<&2, Fai> & (File & B.Ans)>:
            q : File & B.Ans <- answer.go(Nat.is_eq(lb, 0n), fa, Fai{n, off, lb, lw}, a, b)
            return (m, q)

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

def loop?(io: Io, st: Norm.St, next: B.Next) -> IO(Unit):
  match io:
    case Io{vcf, fa, out, err, fai}:
      match next:
        case B.Finish{code}:
          do IO<Unit>:
            File.close(vcf)
            File.close(fa)
            File.close(out)
            File.close(err)
            IO.exit(U32.from_nat(code))
        case B.More{}:
          do IO<Unit>:
            p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(vcf, 65536)
            loop.more(p, fa, out, err, fai, st)
        case B.Ask{c, a, b}:
          do IO<Unit>:
            q : Map<&2, Fai> & (File & B.Ans) <- answer.got(Map.get(Fai, Fai{0n, 0n, 0n, 0n}, fai, c), fa, a, b)
            loop.ref(q, vcf, out, err, st)

def loop.ref?(q: Map<&2, Fai> & (File & B.Ans), vcf: File, out: File, err: File, st: Norm.St) -> IO(Unit):
  match q:
    case (fai, (fa, ans)):
      emit(Io{vcf, fa, out, err, fai}, Norm.step(st, B.Ref{ans}))

def loop.more?(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, fa: File, out: File, err: File, fai: Map<&2, Fai>, st: Norm.St) -> IO(Unit):
  match p:
    case (vcf, r):
      do IO<Unit>:
        +bs : List<&2, U32> <- or_die(List<&2, U32>, r, "cannot read the VCF file")
        emit(Io{vcf, fa, out, err, fai}, loop.input(bs, st))

def loop.input?(bs: List<&2, U32>, st: Norm.St) -> Norm.Step:
  match bs:
    case Nil{}:
      Norm.step(st, B.Eof{})
    case b <> t:
      Norm.step(st, B.Chunk{bytes_str(b <> t)})

# Write what a step wrote, then go on with what it wants next.
def emit?(io: Io, s: Norm.Step) -> IO(Unit):
  match io s:
    case Io{vcf, fa, out, err, fai} Norm.Step{st, o, ns, next}:
      do IO<Unit>:
        out2 : File <- write(out, o)
        err2 : File <- write(err, notes_text(ns))
        loop(Io{vcf, fa, out2, err2, fai}, st, next)

def run?(st: Norm.St, +ref: String, +vcf: String) -> IO(Unit):
  do IO<Unit>:
    fi : File <- open(ref ++ ".fai", "r")
    cs : List<&2, List<&2, U32>> <- read_all(fi, Nil{})
    +fai : Map<&2, Fai> = fai_load(String.lines(bytes_str(concat_rev(cs, Nil{}))), Map.new(&2, Fai))
    fa : File <- open(ref, "r")
    v : File <- open(vcf, "r")
    out : File <- open("/dev/stdout", "a")
    err : File <- open("/dev/stderr", "a")
    loop(Io{v, fa, out, err, fai}, st, B.More{})

def main.k?(b: Norm.Begin) -> IO(Unit):
  match b:
    case Norm.Usage{}:
      IO.die(Unit, 2, B.usage())
    case Norm.Begin{st, ref, vcf}:
      run(st, ref, vcf)

def main.args?(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.die(Unit, 2, B.usage())
    case prog <> rest:
      main.k(Norm.start(args_data(rest)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.args(args)
