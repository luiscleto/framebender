import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_num.bend as TN
import ./proof_c_tan_alk.bend as TA
import ./proof_c_tan_sim.bend as TS
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase C, area "tan": tan.bend's right and left on the closed form
# (alleles Q.ALKS at position pos - k) take the steps Q.RIGHT and Q.LEFT
# take (proof_c_defs.bend), one for one.

# The step tan.bend takes for the step NX.act chose.
def ACT(+wl: U32, +wt: AT.Tree<U32>, +p0: U32, +offu: U32, +k: U32, c: NX.Ak) -> V.Act:
  match c:
    case NX.KStop{}:
      V.AStop{}
    case NX.KTrim{}:
      V.ATrim{}
    case NX.KShift{}:
      V.AShift{TA.SB(wl, wt, p0, offu, k)}
    case NX.KNeed{}:
      V.ANeed{}

# tan.bend's right's result for the counters m.
def RL(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +p0: U32, +offu: U32, +als: List<&2, NX.Ap>, m: Maybe<&2, Q.K2>) -> Maybe<&2, V.Cur>:
  match m:
    case None{}:
      None{}
    case Some{Q.K2{+k, +tr}}:
      Some{V.Cur{Nat.sub(Q.n(p0), Q.n(k)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)}}

# What the counters keep after the right steps.
def OKM(+als: List<&2, NX.Ap>, +p0: U32, +offu: U32, m: Maybe<&2, Q.K2>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Q.K2{+k, +tr}}:
      Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) && Q.KL(als, tr, 0n)

def akT(c: NX.Ak) -> Type:
  match c:
    case NX.KTrim{}:
      Empty
    case _:
      Unit

def akS(c: NX.Ak) -> Type:
  match c:
    case NX.KShift{}:
      Empty
    case _:
      Unit

law kdT:
  for +c: NX.Ak
  for +e: {c == NX.KTrim{} : NX.Ak}
  for u: akT(c)
  Empty

def kdT(c, e, u):
  %e : akT(_)
  u

law kdS:
  for +c: NX.Ak
  for +e: {c == NX.KShift{} : NX.Ak}
  for u: akS(c)
  Empty

def kdS(c, e, u):
  %e : akS(_)
  u

law act_trim:
  for le: Bool
  for al: Bool
  for s: Bool
  for h: Bool
  for +e: {NX.act(le, al, s, h) == NX.KTrim{} : NX.Ak}
  {al == True{} : Bool}

def act_trim(le, al, s, h, e):
  match le:
    case False{}:
      Empty.absurd({al == True{} : Bool}, kdT(NX.KStop{}, e, Unit{}))
    case True{}:
      match al:
        case True{}:
          {==}
        case False{}:
          match s:
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, kdT(NX.KStop{}, e, Unit{}))
            case True{}:
              match h:
                case False{}:
                  Empty.absurd({False{} == True{} : Bool}, kdT(NX.KNeed{}, e, Unit{}))
                case True{}:
                  Empty.absurd({False{} == True{} : Bool}, kdT(NX.KShift{}, e, Unit{}))

law act_shift_s:
  for le: Bool
  for al: Bool
  for s: Bool
  for h: Bool
  for +e: {NX.act(le, al, s, h) == NX.KShift{} : NX.Ak}
  {s == True{} : Bool}

def act_shift_s(le, al, s, h, e):
  match le:
    case False{}:
      Empty.absurd({s == True{} : Bool}, kdS(NX.KStop{}, e, Unit{}))
    case True{}:
      match al:
        case True{}:
          Empty.absurd({s == True{} : Bool}, kdS(NX.KTrim{}, e, Unit{}))
        case False{}:
          match s:
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, kdS(NX.KStop{}, e, Unit{}))
            case True{}:
              {==}

law act_shift_h:
  for le: Bool
  for al: Bool
  for s: Bool
  for h: Bool
  for +e: {NX.act(le, al, s, h) == NX.KShift{} : NX.Ak}
  {h == True{} : Bool}

def act_shift_h(le, al, s, h, e):
  match le:
    case False{}:
      Empty.absurd({h == True{} : Bool}, kdS(NX.KStop{}, e, Unit{}))
    case True{}:
      match al:
        case True{}:
          Empty.absurd({h == True{} : Bool}, kdS(NX.KTrim{}, e, Unit{}))
        case False{}:
          match s:
            case False{}:
              Empty.absurd({h == True{} : Bool}, kdS(NX.KStop{}, e, Unit{}))
            case True{}:
              match h:
                case False{}:
                  Empty.absurd({False{} == True{} : Bool}, kdS(NX.KNeed{}, e, Unit{}))
                case True{}:
                  {==}

law u_le2:
  for +p0: U32
  for +k: U32
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  {U32.is_le(2, (p0 - k : U32)) == Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) : Bool}

def u_le2(p0, k, hk0):
  %Equal.sym(Bool, U32.is_le(2, (p0 - k : U32)), Nat.is_le(2n, Q.n((p0 - k : U32))), TL.u_le(2, (p0 - k : U32))) : {_ == Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) : Bool}
  %Equal.sym(Nat, Q.n((p0 - k : U32)), Nat.sub(Q.n(p0), Q.n(k)), TL.u_sub(p0, k, hk0)) : {Nat.is_le(2n, _) == Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) : Bool}
  {==}

law u_le3:
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  {U32.is_le(offu, ((p0 - k : U32) - 2 : U32)) == Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) : Bool}

def u_le3(p0, offu, k, hk0, hS):
  +u1 = (p0 - k : U32)
  +E1 = TL.u_sub(p0, k, hk0)
  +E2 = TL.u_sub(u1, 2,
    %Equal.sym(Nat, Q.n(u1), Nat.sub(Q.n(p0), Q.n(k)), E1) : {Nat.is_le(2n, _) == True{} : Bool}
    hS)
  %Equal.sym(Bool, U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), Nat.is_le(Q.n(offu), Q.n((u1 - 2 : U32))), TL.u_le(offu, (u1 - 2 : U32))) : {_ == Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) : Bool}
  %Equal.sym(Nat, Q.n((u1 - 2 : U32)), Nat.sub(Q.n(u1), 2n), E2) : {Nat.is_le(Q.n(offu), _) == Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) : Bool}
  %Equal.sym(Nat, Q.n(u1), Nat.sub(Q.n(p0), Q.n(k)), E1) : {Nat.is_le(Q.n(offu), Nat.sub(_, 2n)) == Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) : Bool}
  {==}

law kok_shift:
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Q.n((k + 1 : U32)), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}

def kok_shift(p0, offu, k, hk, hS, hH):
  %Equal.sym(Nat, Q.n((k + 1 : U32)), Nat.add(Q.n(k), 1n), TL.u_inc(k, p0, TN.kok_lt(Q.n(k), Q.n(offu), Q.n(p0), hk))) :
    {Nat.is_le(Nat.add(Nat.add(_, Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  TN.sh_kok(Q.n(p0), Q.n(k), Q.n(offu), hS, hH)

def stepy(+wl: U32, +wt: AT.Tree<U32>, +wd: Nat, +p0: U32, +offu: U32, +k: U32, h: Bool,
  +hh: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == h : Bool},
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool},
  +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool},
  +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}) ->
  {V.next_act.if(True{}, False{}, True{}, V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n))) == ACT(wl, wt, p0, offu, k, NX.act(True{}, False{}, True{}, h)) : V.Act}:
  match h:
    case True{}:
      %Equal.sym(Maybe<&2, B.Base>, V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)), Some{TA.SB(wl, wt, p0, offu, k)}, TA.win_sb(wl, wt, wd, p0, offu, k, hw, hk0, hS, hh, ho)) :
        {V.next_act.if(True{}, False{}, True{}, _) == V.AShift{TA.SB(wl, wt, p0, offu, k)} : V.Act}
      {==}
    case False{}:
      +i = Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)
      %Equal.sym(Bool, Nat.is_lt(i, Q.n(offu)), True{}, N.not_le_lt(Q.n(offu), i, hh)) :
        {V.next_act.if(True{}, False{}, True{}, V.Win.get.if(_, Q.BF(Q.xs(wl, wt)), Q.n(offu), i)) == V.ANeed{} : V.Act}
      {==}

law stepx:
  for le: Bool
  for al: Bool
  for s: Bool
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hs: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == s : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {V.next_act.if(le, al, s, V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n))) == ACT(wl, wt, p0, offu, k, NX.act(le, al, s, U32.is_le(offu, ((p0 - k : U32) - 2 : U32)))) : V.Act}

def stepx(le, al, s, wl, wt, wd, p0, offu, k, hs, hw, hk0, ho):
  match le al s:
    case False{} _ _:
      {==}
    case True{} True{} _:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      %Equal.sym(Bool, U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)), u_le3(p0, offu, k, hk0, hs)) :
        {V.next_act.if(True{}, False{}, True{}, V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n))) == ACT(wl, wt, p0, offu, k, NX.act(True{}, False{}, True{}, _)) : V.Act}
      stepy(wl, wt, wd, p0, offu, k, Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)), {==}, hw, hk0, hs, ho)

# NX.next's step is the one tan.bend's next_act takes.
law step:
  for +als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)) == ACT(wl, wt, p0, offu, k, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr)) : V.Act}

def step(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  +A = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)
  +LE = V.lasts_eq(A)
  +AL = V.all_long(A)
  +hk0 = TN.kok_le(Q.n(k), Q.n(offu), Q.n(p0), hk)
  %Equal.sym(Q.EB, Q.ENDS(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu), Q.EB{LE, AL}, TS.ends_last_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl)) :
    {V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), A) == ACT(wl, wt, p0, offu, k, Q.NEXT.k(k, p0, offu, _)) : V.Act}
  %Equal.sym(Bool, U32.is_le(2, (p0 - k : U32)), Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))), u_le2(p0, k, hk0)) :
    {V.next_act.if(LE, AL, Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))), V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n))) == ACT(wl, wt, p0, offu, k, NX.act(LE, AL, _, U32.is_le(offu, ((p0 - k : U32) - 2 : U32)))) : V.Act}
  stepx(LE, AL, Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))), wl, wt, wd, p0, offu, k, {==}, hw, hk0, ho)

law next_act_eq:
  for +als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr) == NX.act(V.lasts_eq(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)), V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)), U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32))) : NX.Ak}

def next_act_eq(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  +A = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)
  Equal.cong(Q.EB, NX.Ak, x => Q.NEXT.k(k, p0, offu, x), Q.ENDS(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu), Q.EB{V.lasts_eq(A), V.all_long(A)}, TS.ends_last_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl))

law right_sim:
  for fuel: Nat
  for c: NX.Ak
  for +als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hc: {Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr) == c : NX.Ak}
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {V.right(fuel, ACT(wl, wt, p0, offu, k, c), Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(fuel, c, bl, bt, wl, wt, als, p0, offu, k, tr)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(fuel, c, bl, bt, wl, wt, als, p0, offu, k, tr)) == True{} : Bool}

def right_sim(fuel, c, als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hc, hb, hw, ha, hk, ho, hkl):
  match fuel c:
    case 0n _:
      ({==}, TL.and_tt(Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)), Q.KL(als, tr, 0n), hk, hkl))
    case 1n+f NX.KStop{}:
      ({==}, TL.and_tt(Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)), Q.KL(als, tr, 0n), hk, hkl))
    case 1n+f NX.KNeed{}:
      ({==}, {==})
    case 1n+f NX.KTrim{}:
      +A = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)
      +t1 = (tr + 1 : U32)
      +A1 = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, t1, 0n)
      +LE = V.lasts_eq(A)
      +AL = V.all_long(A)
      +hc2 = Equal.trans(NX.Ak, NX.act(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32))), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr), NX.KTrim{},
        Equal.sym(NX.Ak, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr), NX.act(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32))), next_act_eq(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl)), hc)
      +hal = act_trim(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), hc2)
      +hkl1 = TS.kl_inc(als, tr, TS.kl_long(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, 0n, hb, hw, ha, hk, ho, hkl, hal))
      +c1 = Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, t1)
      %Equal.sym(List<&2, List<&2, B.Base>>, V.inits(A), A1, TS.alks_inits(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl)) :
        {V.right(f, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), _), Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), _) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k, t1)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k, t1)) == True{} : Bool}
      %Equal.sym(V.Act, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), A1), ACT(wl, wt, p0, offu, k, c1), step(als, bl, bt, bd, wl, wt, wd, p0, offu, k, t1, hb, hw, ha, hk, ho, hkl1)) :
        {V.right(f, _, Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k)), A1) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k, t1)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k, t1)) == True{} : Bool}
      right_sim(f, c1, als, bl, bt, bd, wl, wt, wd, p0, offu, k, t1, {==}, hb, hw, ha, hk, ho, hkl1)
    case 1n+f NX.KShift{}:
      +A = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)
      +k1 = (k + 1 : U32)
      +A1 = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr, 0n)
      +LE = V.lasts_eq(A)
      +AL = V.all_long(A)
      +hc2 = Equal.trans(NX.Ak, NX.act(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32))), Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr), NX.KShift{},
        Equal.sym(NX.Ak, Q.NEXT(bl, bt, wl, wt, als, p0, offu, k, tr), NX.act(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32))), next_act_eq(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl)), hc)
      +hk0 = TN.kok_le(Q.n(k), Q.n(offu), Q.n(p0), hk)
      +hS = Equal.trans(Bool, Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))), U32.is_le(2, (p0 - k : U32)), True{}, Equal.sym(Bool, U32.is_le(2, (p0 - k : U32)), Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))), u_le2(p0, k, hk0)),
        act_shift_s(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), hc2))
      +hH = Equal.trans(Bool, Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), True{}, Equal.sym(Bool, U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)), u_le3(p0, offu, k, hk0, hS)),
        act_shift_h(LE, AL, U32.is_le(2, (p0 - k : U32)), U32.is_le(offu, ((p0 - k : U32) - 2 : U32)), hc2))
      +hk1 = kok_shift(p0, offu, k, hk, hS, hH)
      +c1 = Q.NEXT(bl, bt, wl, wt, als, p0, offu, k1, tr)
      +p1 = Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 1n)
      %Equal.sym(List<&2, List<&2, B.Base>>, V.shifted(TA.SB(wl, wt, p0, offu, k), A), A1, TS.alks_shift(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl, hS, hH)) :
        {V.right(f, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), p1, _), Q.n(offu), Q.BF(Q.xs(wl, wt)), p1, _) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) == True{} : Bool}
      %Equal.sym(Nat, p1, Nat.sub(Q.n(p0), Nat.add(Q.n(k), 1n)), TL.sub_sub(Q.n(p0), Q.n(k), 1n)) :
        {V.right(f, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), _, A1), Q.n(offu), Q.BF(Q.xs(wl, wt)), _, A1) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) == True{} : Bool}
      %TL.u_inc(k, p0, TN.kok_lt(Q.n(k), Q.n(offu), Q.n(p0), hk)) :
        {V.right(f, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), _), A1), Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), _), A1) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) == True{} : Bool}
      %Equal.sym(V.Act, V.next_act(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k1)), A1), ACT(wl, wt, p0, offu, k1, c1), step(als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr, hb, hw, ha, hk1, ho, hkl)) :
        {V.right(f, _, Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Q.n(p0), Q.n(k1)), A1) == RL(bl, bt, wl, wt, p0, offu, als, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) : Maybe<&2, V.Cur>} & {OKM(als, p0, offu, Q.RIGHT(f, c1, bl, bt, wl, wt, als, p0, offu, k1, tr)) == True{} : Bool}
      right_sim(f, c1, als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr, {==}, hb, hw, ha, hk1, ho, hkl)

law left_sim:
  for fuel: Nat
  for go: Bool
  for +als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hg: {Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d) == go : Bool}
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, d) == True{} : Bool}
  {V.left(fuel, go, Nat.add(d, Nat.sub(Q.n(p0), Q.n(k))), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)) == V.Cur{Nat.add(Q.LEFT(fuel, go, bl, bt, wl, wt, als, p0, offu, k, tr, d), Nat.sub(Q.n(p0), Q.n(k))), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, Q.LEFT(fuel, go, bl, bt, wl, wt, als, p0, offu, k, tr, d))} : V.Cur} & {Q.KL(als, tr, Q.LEFT(fuel, go, bl, bt, wl, wt, als, p0, offu, k, tr, d)) == True{} : Bool}

def left_sim(fuel, go, als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hg, hb, hw, ha, hk, ho, hkl):
  match fuel go:
    case 0n _:
      ({==}, hkl)
    case 1n+f False{}:
      ({==}, hkl)
    case 1n+f True{}:
      +A = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)
      +d1 = Nat.add(1n, d)
      +A1 = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d1)
      +FE = V.firsts_eq(A)
      +AL = V.all_long(A)
      +Ef = Equal.cong(Q.EB, Bool, x => Q.FIRSTS.k(x), Q.ENDS(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu), Q.EB{FE, AL}, TS.ends_first_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl))
      +hal = TL.and_r(FE, AL, Equal.trans(Bool, Bool.and(FE, AL), Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d), True{}, Equal.sym(Bool, Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d), Bool.and(FE, AL), Ef), hg))
      +hkl1 = TS.kl_long(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl, hal)
      +g1 = Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k, tr, d1)
      +Ef1 = Equal.cong(Q.EB, Bool, x => Q.FIRSTS.k(x), Q.ENDS(als, bl, bt, wl, wt, k, tr, d1, False{}, p0, offu), Q.EB{V.firsts_eq(A1), V.all_long(A1)}, TS.ends_first_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d1, hb, hw, ha, hk, ho, hkl1))
      %Equal.sym(List<&2, List<&2, B.Base>>, V.tails(A), A1, TS.alks_tails(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d)) :
        {V.left(f, V.firsts_eq(_) && V.all_long(_), Nat.add(d1, Nat.sub(Q.n(p0), Q.n(k))), _) == V.Cur{Nat.add(Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1), Nat.sub(Q.n(p0), Q.n(k))), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1))} : V.Cur} & {Q.KL(als, tr, Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1)) == True{} : Bool}
      %Ef1 :
        {V.left(f, _, Nat.add(d1, Nat.sub(Q.n(p0), Q.n(k))), A1) == V.Cur{Nat.add(Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1), Nat.sub(Q.n(p0), Q.n(k))), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1))} : V.Cur} & {Q.KL(als, tr, Q.LEFT(f, g1, bl, bt, wl, wt, als, p0, offu, k, tr, d1)) == True{} : Bool}
      left_sim(f, g1, als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d1, {==}, hb, hw, ha, hk, ho, hkl1)

law tovar:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +x: Nat
  {V.to_var(V.Cur{Nat.add(x, Nat.sub(Q.n(p0), Q.n(k))), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, x)}) == Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k, tr, x) : B.Var}

def tovar(als, bl, bt, wl, wt, p0, offu, k, tr, x):
  match als:
    case Nil{}:
      %N.add_comm(Nat.sub(Q.n(p0), Q.n(k)), x) : {B.Var{_, Nil{}, Nil{}} == B.Var{Nat.add(Nat.sub(Q.n(p0), Q.n(k)), x), Nil{}, Nil{}} : B.Var}
      {==}
    case +a <> +t:
      +R = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, x))
      +T = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, x)
      %N.add_comm(Nat.sub(Q.n(p0), Q.n(k)), x) : {B.Var{_, R, T} == B.Var{Nat.add(Nat.sub(Q.n(p0), Q.n(k)), x), R, T} : B.Var}
      {==}

def K3k(m: Maybe<&2, Q.K3>) -> U32:
  match m:
    case None{}:
      0
    case Some{Q.K3{k, tr, d}}:
      k

def K3t(m: Maybe<&2, Q.K3>) -> U32:
  match m:
    case None{}:
      0
    case Some{Q.K3{k, tr, d}}:
      tr

def K3d(m: Maybe<&2, Q.K3>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Q.K3{k, tr, d}}:
      d

def mnone(m: Maybe<&2, Q.K3>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_some:
  for +x: Q.K3
  for +e: {None{} == Some{x} : Maybe<&2, Q.K3>}
  Empty

def none_some(x, e):
  %e : mnone(_)
  Unit{}

# NX.norm's answer Some{K3{k, tr, d}} is the counters left_of finds.
law fin:
  for m: Maybe<&2, Q.K2>
  for +als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hz: {Q.NZ.r(m, bl, bt, wl, wt, als, p0, offu) == Some{Q.K3{k, tr, d}} : Maybe<&2, Q.K3>}
  for +hok: {OKM(als, p0, offu, m) == True{} : Bool}
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {V.left_of(RL(bl, bt, wl, wt, p0, offu, als, m)) == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k, tr, d) == True{} : Bool}

def fin(m, als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hz, hok, hb, hw, ha, ho):
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k, tr, d) == True{} : Bool}, none_some(Q.K3{k, tr, d}, hz))
    case Some{Q.K2{+k1, +tr1}}:
      +fu = Nat.add(Q.n((p0 - k1 : U32)), NX.tot(als, tr1))
      +g = Q.FIRSTS(bl, bt, wl, wt, als, p0, offu, k1, tr1, 0n)
      +L = Q.LEFT(fu, g, bl, bt, wl, wt, als, p0, offu, k1, tr1, 0n)
      +S1 = {Some{Q.K3{k1, tr1, L}} : Maybe<&2, Q.K3>}
      +S2 = {Some{Q.K3{k, tr, d}} : Maybe<&2, Q.K3>}
      +ek = Equal.cong(Maybe<&2, Q.K3>, U32, x => K3k(x), S1, S2, hz)
      +et = Equal.cong(Maybe<&2, Q.K3>, U32, x => K3t(x), S1, S2, hz)
      +ed = Equal.cong(Maybe<&2, Q.K3>, Nat, x => K3d(x), S1, S2, hz)
      +LH = V.left_of(RL(bl, bt, wl, wt, p0, offu, als, Some{Q.K2{k1, tr1}}))
      +hk1 = TL.and_l(Nat.is_le(Nat.add(Nat.add(Q.n(k1), Q.n(offu)), 1n), Q.n(p0)), Q.KL(als, tr1, 0n), hok)
      +hkl1 = TL.and_r(Nat.is_le(Nat.add(Nat.add(Q.n(k1), Q.n(offu)), 1n), Q.n(p0)), Q.KL(als, tr1, 0n), hok)
      +A0 = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr1, 0n)
      +p1 = Nat.sub(Q.n(p0), Q.n(k1))
      +FE = V.firsts_eq(A0)
      +AL = V.all_long(A0)
      %ek : {LH == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, _, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, _, tr, d) == True{} : Bool}
      %et : {LH == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, _, d)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, _, d) == True{} : Bool}
      %ed : {LH == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, _)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, _) == True{} : Bool}
      %Equal.sym(Nat, V.total(A0), NX.tot(als, tr1), TS.alks_total(als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr1, hb, hw, ha, hk1, ho, hkl1)) :
        {Some{V.to_var(V.left(Nat.add(p1, _), FE && AL, p1, A0))} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, L) == True{} : Bool}
      %TL.u_sub(p0, k1, TN.kok_le(Q.n(k1), Q.n(offu), Q.n(p0), hk1)) :
        {Some{V.to_var(V.left(Nat.add(_, NX.tot(als, tr1)), FE && AL, p1, A0))} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, L) == True{} : Bool}
      %Equal.cong(Q.EB, Bool, x => Q.FIRSTS.k(x), Q.ENDS(als, bl, bt, wl, wt, k1, tr1, 0n, False{}, p0, offu), Q.EB{FE, AL}, TS.ends_first_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr1, 0n, hb, hw, ha, hk1, ho, hkl1)) :
        {Some{V.to_var(V.left(fu, _, p1, A0))} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, L) == True{} : Bool}
      %Equal.sym(V.Cur, V.left(fu, g, p1, A0), V.Cur{Nat.add(L, p1), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr1, L)},
          Pair.fst({V.left(fu, g, p1, A0) == V.Cur{Nat.add(L, p1), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr1, L)} : V.Cur}, {Q.KL(als, tr1, L) == True{} : Bool}, left_sim(fu, g, als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr1, 0n, {==}, hb, hw, ha, hk1, ho, hkl1))) :
        {Some{V.to_var(_)} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, L) == True{} : Bool}
      %Equal.sym(B.Var, V.to_var(V.Cur{Nat.add(L, p1), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr1, L)}), Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L), tovar(als, bl, bt, wl, wt, p0, offu, k1, tr1, L)) :
        {Some{_} == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k1, tr1, L)} : Maybe<&2, B.Var>} & {Q.KOK(als, p0, offu, k1, tr1, L) == True{} : Bool}
      ({==}, TL.and_tt(Nat.is_le(Nat.add(Nat.add(Q.n(k1), Q.n(offu)), 1n), Q.n(p0)), Q.KL(als, tr1, L), hk1,
        Pair.snd({V.left(fu, g, p1, A0) == V.Cur{Nat.add(L, p1), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k1, tr1, L)} : V.Cur}, {Q.KL(als, tr1, L) == True{} : Bool}, left_sim(fu, g, als, bl, bt, bd, wl, wt, wd, p0, offu, k1, tr1, 0n, {==}, hb, hw, ha, hk1, ho, hkl1))))
