import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_cachedefs.bend as PC

# The budget's per-step predicates (proof_b_budget_step.bend proves the
# steps with them; sub-lemmas stated with them can live in other files).

def HOL(+T: R.Report, +O: String) -> Nat:
  BN.HO(T, O)

# A step from a state whose WA is at most W0: bi holds after it, and for
# what it writes (within the report's output) HO + RD(next) + WA is at most
# HO + W0 before it.
def BudS(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +W0: Nat, -s: Norm.Step) -> Type:
  {BN.biS(BN.sst(s), cs) == True{} : Bool}
  & (@t: String -> {BN.sout(s) == Some{t} : Maybe<&2, String>} -> {Nat.is_le(String.length(String.append(O, t)), String.length(R.Report.out(T))) == True{} : Bool} ->
    @r: Nat -> {BN.RD(BN.snx(s)) == r : Nat} -> @w: Nat -> {BN.WAS(fa, BN.sst(s), cs) == w : Nat} ->
    {Nat.is_le(Nat.add(BN.HO(T, String.append(O, t)), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool})

# What advance does to WA: a Want pays its step and reads; a Yield leaves
# the state as it was, with the yield's test passed.
def AdvB(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, a: Norm.Adv) -> Type:
  match a:
    case Norm.Went{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}
    case Norm.Want{st, rs}:
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, rs), BN.WAS(fa, st, cs)), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}
    case Norm.Idle{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}
    case Norm.Ended{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}
    case Norm.Yield{st}:
      {st == S.mkSt(fa, p) : Norm.St} & {yc(p) == True{} : Bool}

# advance keeps bi.
def AdvBi(+cs: List<&2, String>, a: Norm.Adv) -> Type:
  match a:
    case Norm.Went{st}:
      {BN.biS(st, cs) == True{} : Bool}
    case Norm.Want{st, rs}:
      {BN.biS(st, cs) == True{} : Bool}
    case Norm.Idle{st}:
      {BN.biS(st, cs) == True{} : Bool}
    case Norm.Ended{st}:
      {BN.biS(st, cs) == True{} : Bool}
    case Norm.Yield{st}:
      {BN.biS(st, cs) == True{} : Bool}

# The yield's test (norm.bend's mb.rs, ms.full).
def yc(p: S.StP) -> Bool:
  match p:
    case S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}:
      U32.is_le(1073741824, P.RunP.ow(rp))
    case S.StP{o, S.MSP{s, qs, +ql, c}, src, pd, eof, back, wp, asked, fneed}:
      Nat.is_le(Norm.lim(), ql)

# ---------------------------------------------------------------------------
# Sub-lemmas (statements fixed here; see notes for who proves which)
# ---------------------------------------------------------------------------

def WP(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP) -> Nat:
  BN.WAS(fa, S.mkSt(fa, p), cs)

def FedG(+fa: List<&2, B.Contig>, +T: R.Report, +cs2: List<&2, String>, +O: String, +N: List<&2, B.Note>, +W: Nat, -st: Norm.St) -> Type:
  &q: S.StP -> ({st == S.mkSt(fa, q) : Norm.St} & ({S.WF(fa, q) == True{} : Bool} & ({S.report(fa, cs2, O, N, q) == T : R.Report}
    & ({S.guard(O, N, q) == True{} : Bool} & ({S.StP.asked(q) == None{} : Maybe<&2, List<&2, Pr.Req>>}
    & ({Nat.is_le(WP(fa, cs2, q), W) == True{} : Bool} & {BN.biS(S.mkSt(fa, q), cs2) == True{} : Bool}))))))

# A verdict that asks for reads.
def is_vwant(v: Norm.Vd) -> Bool:
  match v:
    case Norm.VWant{w, rs, b}:
      True{}
    case _:
      False{}

# serve found the read in the window.
def sv_hit(sv: Norm.Sv) -> Bool:
  match sv:
    case Norm.Sv{w, Some{a}, k}:
      True{}
    case _:
      False{}

# AdvB and AdvBi together (the walk proves both at once).
def AdvC(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, a: Norm.Adv) -> Type:
  match a:
    case Norm.Went{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool} & {BN.biS(st, cs) == True{} : Bool}
    case Norm.Want{st, rs}:
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, rs), BN.WAS(fa, st, cs)), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool} & {BN.biS(st, cs) == True{} : Bool}
    case Norm.Idle{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool} & {BN.biS(st, cs) == True{} : Bool}
    case Norm.Ended{st}:
      {Nat.is_le(BN.WAS(fa, st, cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool} & {BN.biS(st, cs) == True{} : Bool}
    case Norm.Yield{st}:
      {st == S.mkSt(fa, p) : Norm.St} & ({yc(p) == True{} : Bool} & {BN.biS(st, cs) == True{} : Bool})

# A picture by its fields.
def StM(+o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed}

# What a verdict's Want does to the line's share (both modes): its step and
# reads are paid by rem without the fast path's term, and bi holds after it.
def VB(+fa: List<&2, B.Contig>, +l: B.Line, +back: Nat, -w: Norm.Win, v: Norm.Vd) -> Type:
  match v:
    case Norm.VWant{w2, +reqs, +back2}:
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, reqs), BN.rem(fa, False{}, back2, w2, Some{reqs}, l)), BN.rem(fa, False{}, back, w, None{}, l)) == True{} : Bool}
      & {Bool.or(Nat.is_eq(back2, 0n), BN.heldZ(w2, Some{reqs}, BN.lchrom(l), BN.lend(l))) == True{} : Bool}
    case _:
      Unit

# The fast path's window test asked for the reads (WNeed).
def wo_need(w: Norm.Wo) -> Bool:
  match w:
    case Norm.Wo{win, b, Norm.WNeed{}}:
      True{}
    case _:
      False{}

# The fast path's window answer asks only with back = 0 (the threading of
# proof_b_budget_fast.bend).
def wr_ok(w: Norm.Wr, +back: Nat) -> Bool:
  match w:
    case Norm.WNeed{}:
      Nat.is_eq(back, 0n)
    case _:
      True{}
