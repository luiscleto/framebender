import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm.bend as Norm
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Phase C (notes/rewrite.md): pictures shared by the proofs of the rewrite
# path (norm_fix.bend). A buffer is its mirror C.BT(len, t) (lawful-bytes);
# xs is its view; n(x) is U32.to_nat(x).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# Alleles and bases
# ---------------------------------------------------------------------------

# A byte's base, as B.Base.of_fasta reads it (for A, C, G, T, N in either
# case, the base B.Base.of_letter reads).
def bf(+x: U32) -> B.Base:
  B.Base.of_fasta(Chr{x})

def BF(ys: List<&2, U32>) -> List<&2, B.Base>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      bf(y) <> BF(t)

# An allele's bytes in the buffer.
def SL(+ys: List<&2, U32>, +a: NX.Ap) -> List<&2, U32>:
  D.slice(ys, n(NX.Ap.st(a)), n(NX.Ap.ln(a)))

def BFS(+ys: List<&2, U32>, als: List<&2, NX.Ap>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case +a <> t:
      BF(SL(ys, a)) <> BFS(ys, t)

# The record's variant: POS p0, REF the first allele, then the ALTs.
def V0(+ys: List<&2, U32>, als: List<&2, NX.Ap>, +p0: U32) -> B.Var:
  match als:
    case Nil{}:
      B.Var{n(p0), Nil{}, Nil{}}
    case +a <> t:
      B.Var{n(p0), BF(SL(ys, a)), BFS(ys, t)}

# The k reference letters before POS p0 (contig indices p0-1-k .. p0-2), in
# the window ws read from contig index offu.
def RK(+ws: List<&2, U32>, +p0: U32, +offu: U32, +k: U32) -> List<&2, U32>:
  D.slice(ws, Nat.sub(Nat.sub(Nat.sub(n(p0), 1n), n(k)), n(offu)), n(k))

# Allele a after k shifts, tr right trims and d left trims:
# drop(take(R_k ++ a, L - tr), d).
def ALK(+bs: List<&2, U32>, +ws: List<&2, U32>, +p0: U32, +offu: U32, +a: NX.Ap, +k: U32, +tr: U32, +d: Nat) -> List<&2, U32>:
  List.drop(&2, U32, List.take(&2, U32, List.append(&2, U32, RK(ws, p0, offu, k), SL(bs, a)), Nat.sub(n(NX.Ap.ln(a)), n(tr))), d)

def ALKS(+bs: List<&2, U32>, +ws: List<&2, U32>, +p0: U32, +offu: U32, als: List<&2, NX.Ap>, +k: U32, +tr: U32, +d: Nat) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case +a <> t:
      BF(ALK(bs, ws, p0, offu, a, k, tr, d)) <> ALKS(bs, ws, p0, offu, t, k, tr, d)

# The normalized variant the counters stand for: POS p0 - k + d.
def VW(+bs: List<&2, U32>, +ws: List<&2, U32>, als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> B.Var:
  match als:
    case Nil{}:
      B.Var{Nat.add(Nat.sub(n(p0), n(k)), d), Nil{}, Nil{}}
    case +a <> t:
      B.Var{Nat.add(Nat.sub(n(p0), n(k)), d), BF(ALK(bs, ws, p0, offu, a, k, tr, d)), ALKS(bs, ws, p0, offu, t, k, tr, d)}

# Every allele has one byte or more and lies inside a buffer of len bytes.
def ALS_IN(+len: U32, als: List<&2, NX.Ap>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case +a <> t:
      Nat.is_le(1n, n(NX.Ap.ln(a))) && Nat.is_le(Nat.add(n(NX.Ap.st(a)), n(NX.Ap.ln(a))), n(len)) && ALS_IN(len, t)

# What the counters keep: the shifts read inside the window, and every
# allele keeps one base or more.
def KL(als: List<&2, NX.Ap>, +tr: U32, +d: Nat) -> Bool:
  match als:
    case Nil{}:
      True{}
    case +a <> t:
      Nat.is_lt(Nat.add(n(tr), d), n(NX.Ap.ln(a))) && KL(t, tr, d)

def KOK(+als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> Bool:
  Nat.is_le(Nat.add(Nat.add(n(k), n(offu)), 1n), n(p0)) && KL(als, tr, d)

# ---------------------------------------------------------------------------
# NX.norm without the buffers: the same steps, reading bytes as C.AT does
# ---------------------------------------------------------------------------

def EL.if(inw: Bool, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +iw: U32, +il: U32) -> U32:
  match inw:
    case True{}:
      C.AT(wl, wt, iw)
    case False{}:
      C.AT(bl, bt, il)

# NX.el's byte.
def EL(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +a: NX.Ap, +k: U32, +j: U32, +p0: U32, +offu: U32) -> U32:
  EL.if(U32.is_lt(j, k), bl, bt, wl, wt, ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32), ((NX.Ap.st(a) + j : U32) - k : U32))

type EB is Data:
  EB{eq: Bool, long: Bool}

def ENDS.go(als: List<&2, NX.Ap>, eq: Bool, long: Bool, +z: U32, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +k: U32, +tr: U32, +d: Nat, +last: Bool, +p0: U32, +offu: U32) -> EB:
  match als:
    case Nil{}:
      EB{eq, long}
    case +a <> t:
      ENDS.go(t, eq && U32.is_eq(NX.code(EL(bl, bt, wl, wt, a, k, NX.ends.ix(last, a, tr, d), p0, offu)), z), long && U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)), z, bl, bt, wl, wt, k, tr, d, last, p0, offu)

# NX.ends's flags.
def ENDS(als: List<&2, NX.Ap>, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +k: U32, +tr: U32, +d: Nat, +last: Bool, +p0: U32, +offu: U32) -> EB:
  match als:
    case Nil{}:
      EB{False{}, True{}}
    case +a <> t:
      ENDS.go(t, True{}, U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)), NX.code(EL(bl, bt, wl, wt, a, k, NX.ends.ix(last, a, tr, d), p0, offu)), bl, bt, wl, wt, k, tr, d, last, p0, offu)

def NEXT.k(+k: U32, +p0: U32, +offu: U32, e: EB) -> NX.Ak:
  match e:
    case EB{eq, long}:
      NX.act(eq, long, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32)))

# NX.next's step.
def NEXT(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32) -> NX.Ak:
  NEXT.k(k, p0, offu, ENDS(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu))

type K2 is Data:
  K2{k: U32, tr: U32}

type K3 is Data:
  K3{k: U32, tr: U32, d: Nat}

# NX.right's counters (None: NX.RNeed).
def RIGHT(fuel: Nat, a: NX.Ak, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32) -> Maybe<&2, K2>:
  match fuel a:
    case 0n _:
      Some{K2{k, tr}}
    case 1n+f NX.KStop{}:
      Some{K2{k, tr}}
    case 1n+f NX.KNeed{}:
      None{}
    case 1n+f NX.KTrim{}:
      RIGHT(f, NEXT(bl, bt, wl, wt, als, p0, offu, k, (tr + 1 : U32)), bl, bt, wl, wt, als, p0, offu, k, (tr + 1 : U32))
    case 1n+f NX.KShift{}:
      RIGHT(f, NEXT(bl, bt, wl, wt, als, p0, offu, (k + 1 : U32), tr), bl, bt, wl, wt, als, p0, offu, (k + 1 : U32), tr)

def FIRSTS.k(e: EB) -> Bool:
  match e:
    case EB{eq, +long}:
      eq && long

# NX.firsts's flag.
def FIRSTS(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> Bool:
  FIRSTS.k(ENDS(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu))

# NX.left's count.
def LEFT(fuel: Nat, go: Bool, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> Nat:
  match fuel go:
    case 0n _:
      d
    case 1n+f False{}:
      d
    case 1n+f True{}:
      LEFT(f, FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, 1n+d), bl, bt, wl, wt, als, p0, offu, k, tr, 1n+d)

def NZ.r(m: Maybe<&2, K2>, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32) -> Maybe<&2, K3>:
  match m:
    case None{}:
      None{}
    case Some{K2{+k, +tr}}:
      Some{K3{k, tr, LEFT(Nat.add(n((p0 - k : U32)), NX.tot(als, tr)), FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, 0n), bl, bt, wl, wt, als, p0, offu, k, tr, 0n)}}

# NX.norm's answer: the counters, or None (it needs a letter before the
# window).
def NZ(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32) -> Maybe<&2, K3>:
  NZ.r(RIGHT(Nat.add(n(p0), NX.tot(als, 0)), NEXT(bl, bt, wl, wt, als, p0, offu, 0, 0), bl, bt, wl, wt, als, p0, offu, 0, 0), bl, bt, wl, wt, als, p0, offu)

# NX.norm's result, with the buffers.
def NZB(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, m: Maybe<&2, K3>) -> NX.Nr:
  match m:
    case None{}:
      NX.Ng{C.BT(bl, bt), C.BT(wl, wt)}
    case Some{K3{k, tr, d}}:
      NX.Nd{C.BT(bl, bt), C.BT(wl, wt), k, tr, d}

# ---------------------------------------------------------------------------
# NX.line without the buffer
# ---------------------------------------------------------------------------

def Fr.p(r: NX.Fr) -> NX.Fp:
  match r:
    case NX.Fr{b, p}:
      p

def fx_of(+len: U32, +t: AT.Tree<U32>, +s: U32) -> NX.Fp:
  Fr.p(NX.line(C.BT(len, t), s))

# The text of bytes a .. b-1 (Norm.chars, one Char per byte).
def fld(+ys: List<&2, U32>, +a: Nat, +b: Nat) -> String:
  Norm.chars(D.slice(ys, a, Nat.sub(b, a)))

def nx(+e: U32) -> Nat:
  Nat.add(n(e), 1n)

# The alleles' texts.
def STRS(+ys: List<&2, U32>, als: List<&2, NX.Ap>) -> List<&2, String>:
  match als:
    case Nil{}:
      Nil{}
    case +a <> t:
      Norm.chars(SL(ys, a)) <> STRS(ys, t)

# Every byte of every allele is A, C, G, T or N in either case.
def lets(ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case +y <> t:
      NX.isl(y) && lets(t)

def ALS_L(+ys: List<&2, U32>, als: List<&2, NX.Ap>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case +a <> t:
      lets(SL(ys, a)) && ALS_L(ys, t)

# The ALT alleles (all but the first).
def TL(als: List<&2, NX.Ap>) -> List<&2, NX.Ap>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      t
