import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_budget_need.bend as BN
import ../lawful-bytes/defs.bend as D

# Phase E, area E2: the parallel machine's budget (notes/parallel_proofs_e2.md).
# The potential of a wrapper state is phase B's (BN.needS) for Q's state over
# the pieces still to come (the batch's held pieces, then the driver's), plus
# what the wrapper's own steps and reads cost:
#   - 12 for every piece of at least 256 bytes not given yet (a batched piece
#     costs its Chunk into the batch, its two reads, its share of the batch's
#     closing step and of the plan's Ask; the start bound has room for 12 per
#     256 bytes);
#   - 7 for every piece held while collecting, and 4 for the batch's closing
#     step and plan (the first piece's 12 pays its Chunk, 7 and 4);
#   - 1 while Q is in the middle of a batched piece (seq): the Ask{[]} that
#     follows it.
# A pending Ask (the plan's, Ask{[]} or Q's) is paid by RD(next) in needS.
# Q's end-of-file flag is the driver's with no batch, else False.

# The texts of the batch's buffers, in order.
def bts(xs: List<&1, D.Bytes>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case b <> t:
      NR.chars(D.view(b)) <> bts(t)

def plts(xs: List<&1, W.Pl>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case W.Pl{b, rs, ok, k, c0, l} <> t:
      NR.chars(D.view(b)) <> plts(t)

def tots(xs: List<&1, W.TOut>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case W.TOut{b, r} <> t:
      NR.chars(D.view(b)) <> tots(t)

# A piece a batch may take.
def big(+c: String) -> Bool:
  Nat.is_le(256n, String.length(c))

# 12 for each such piece.
def XK(+cs: List<&2, String>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +c <> t:
      Nat.add(BN.pick(big(c), 12n), XK(t))

# 7 for each piece held while collecting.
def kx(+k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      Nat.add(7n, kx(j))

def needB(+fa: List<&2, B.Contig>, +T: R.Report, q: Norm.St, b: W.Bat, +cs: List<&2, String>, +ef: Bool, +nx: Pr.Next, +O: String) -> Nat:
  match b:
    case W.BNone{}:
      Nat.add(BN.needS(fa, T, q, cs, ef, nx, O), XK(cs))
    case W.BCol{ps, +k}:
      Nat.add(Nat.add(BN.needS(fa, T, q, List.append(&2, String, List.reverse(&2, String, bts(ps)), cs), False{}, nx, O), Nat.add(kx(k), 4n)), XK(cs))
    case W.BAsk{pls, e}:
      Nat.add(BN.needS(fa, T, q, List.append(&2, String, plts(pls), cs), False{}, nx, O), XK(cs))
    case W.BComb{pcs, e, +s}:
      Nat.add(Nat.add(BN.needS(fa, T, q, List.append(&2, String, tots(pcs), cs), False{}, nx, O), BN.pick(s, 1n)), XK(cs))

# The potential of a wrapper state (the driver's More or Ask next nx, pieces
# not given cs, end-of-file flag ef, output collected O).
def needW(+fa: List<&2, B.Contig>, +T: R.Report, st: W.St, +cs: List<&2, String>, +ef: Bool, +nx: Pr.Next, +O: String) -> Nat:
  match st:
    case W.St{q, b}:
      needB(fa, T, q, b, cs, ef, nx, O)

# Phase B's budget invariant on Q's state, over the same pieces.
def biB(q: Norm.St, b: W.Bat, +cs: List<&2, String>) -> Bool:
  match b:
    case W.BNone{}:
      BN.biS(q, cs)
    case W.BCol{ps, k}:
      BN.biS(q, List.append(&2, String, List.reverse(&2, String, bts(ps)), cs))
    case W.BAsk{pls, e}:
      BN.biS(q, List.append(&2, String, plts(pls), cs))
    case W.BComb{pcs, e, s}:
      BN.biS(q, List.append(&2, String, tots(pcs), cs))

def biW(st: W.St, +cs: List<&2, String>) -> Bool:
  match st:
    case W.St{q, b}:
      biB(q, b, cs)

# What a wrapper step produces.
def sstW(s: W.Step) -> W.St:
  match s:
    case W.Step{st, b, ns, nx}:
      st

def snxW(s: W.Step) -> Pr.Next:
  match s:
    case W.Step{st, b, ns, nx}:
      nx

def snsW(s: W.Step) -> List<&2, B.Note>:
  match s:
    case W.Step{st, b, ns, nx}:
      ns

def soutW(s: W.Step) -> Maybe<&2, String>:
  match s:
    case W.Step{st, b, ns, nx}:
      E.out(b)
