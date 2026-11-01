import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_base.bend as PB
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_step.bend as ST

# Phase E, area E2: a step of Q while the batch is combined (W.seq_out):
# Q's budget (phase B's BudS over the batch's pieces left and the driver's)
# keeps the wrapper's within VQ + 1 (the 1: the Ask{[]} that follows, or Q
# in the middle of a piece).

# The Ask{[]} after Q asked for more: RD 1 on top of a step that ended in More.
def needs_ask.k(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +O: String, +W0: Nat, -st: Norm.St, +O2: String, +X: Nat, +w: Nat,
  k: @r: Nat -> {BN.RD(Pr.More{}) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  d: {BN.WAS(fa, st, L) == w : Nat} & {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, L, False{}, Pr.Ask{Nil{}}, O2), 0n), X), Nat.add(Nat.add(ST.VQ(T, L, False{}, O, W0), 1n), X)) == True{} : Bool}:
  (e1, e2) = d
  +a = Nat.add(List.length(&2, String, L), 1n)
  +Z2 = Nat.add(BN.HO(T, O2), w)
  +Z = Nat.add(BN.HO(T, O), W0)
  %Equal.sym(Nat, BN.WAS(fa, st, L), w, e1) : {Nat.is_le(Nat.add(Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(1n, _)))), 0n), X), Nat.add(Nat.add(Nat.add(a, Nat.add(2n, Z)), 1n), X)) == True{} : Bool}
  +e = Equal.trans(Nat, Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w))), 0n), Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w))), Nat.add(Nat.add(a, Nat.add(2n, Z2)), 1n),
    N.add_zero(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w)))),
    Equal.trans(Nat, Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w))), 1n+Nat.add(a, Nat.add(2n, Z2)), Nat.add(Nat.add(a, Nat.add(2n, Z2)), 1n),
      Equal.trans(Nat, Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w))), Nat.add(a, 1n+Nat.add(2n, Z2)), 1n+Nat.add(a, Nat.add(2n, Z2)),
        Equal.cong(Nat, Nat, z => Nat.add(a, Nat.add(2n, z)), Nat.add(BN.HO(T, O2), 1n+w), 1n+Z2, N.add_succ(BN.HO(T, O2), w)),
        N.add_succ(a, Nat.add(2n, Z2))),
      Equal.sym(Nat, Nat.add(Nat.add(a, Nat.add(2n, Z2)), 1n), 1n+Nat.add(a, Nat.add(2n, Z2)), N.add_one(Nat.add(a, Nat.add(2n, Z2))))))
  %Equal.sym(Nat, Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), 1n+w))), 0n), Nat.add(Nat.add(a, Nat.add(2n, Z2)), 1n), e) :
    {Nat.is_le(Nat.add(_, X), Nat.add(Nat.add(Nat.add(a, Nat.add(2n, Z)), 1n), X)) == True{} : Bool}
  N.le_add_mono_r(X, Nat.add(Nat.add(a, Nat.add(2n, Z2)), 1n), Nat.add(Nat.add(a, Nat.add(2n, Z)), 1n),
    N.le_add_mono_r(1n, Nat.add(a, Nat.add(2n, Z2)), Nat.add(a, Nat.add(2n, Z)),
      ST.vq_le(a, Z2, Z, k(0n, {==}, w, e2))))

def needs_ask(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +O: String, +W0: Nat, -st: Norm.St, +O2: String, +X: Nat,
  k: @r: Nat -> {BN.RD(Pr.More{}) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  ww: &w: Nat -> {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, L, False{}, Pr.Ask{Nil{}}, O2), 0n), X), Nat.add(Nat.add(ST.VQ(T, L, False{}, O, W0), 1n), X)) == True{} : Bool}:
  (+w, ew) = ww
  needs_ask.k(fa, T, L, O, W0, st, O2, X, w, k, ST.eq2(BN.WAS(fa, st, L), w, ew))

# needS within VQ + D, the wrapper adding X.
def needs_leD.k(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +D: Nat, +X: Nat, +w: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  d: {BN.WAS(fa, st, L) == w : Nat} & {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X), Nat.add(Nat.add(ST.VQ(T, L, e, O, W0), D), X)) == True{} : Bool}:
  (e1, e2) = d
  +a = Nat.add(List.length(&2, String, L), BN.pick(Bool.not(e), 1n))
  +V0 = ST.VQ(T, L, e, O, W0)
  +S2 = Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w))))
  %Equal.sym(Nat, BN.WAS(fa, st, L), w, e1) : {Nat.is_le(Nat.add(Nat.add(a, Nat.add(2n, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), _)))), X), Nat.add(Nat.add(V0, D), X)) == True{} : Bool}
  N.le_add_mono_r(X, S2, Nat.add(V0, D),
    N.le_trans(S2, V0, Nat.add(V0, D), ST.vq_le(a, Nat.add(BN.HO(T, O2), Nat.add(BN.RD(nx), w)), Nat.add(BN.HO(T, O), W0), k(BN.RD(nx), {==}, w, e2)), N.le_add_r(V0, D)))

def needs_leD(+fa: List<&2, B.Contig>, +T: R.Report, +L: List<&2, String>, +e: Bool, +O: String, +W0: Nat, -st: Norm.St, +nx: Pr.Next, +O2: String, +D: Nat, +X: Nat,
  k: @r: Nat -> {BN.RD(nx) == r : Nat} -> @w: Nat -> {BN.WAS(fa, st, L) == w : Nat} -> {Nat.is_le(Nat.add(BN.HO(T, O2), Nat.add(r, w)), Nat.add(BN.HO(T, O), W0)) == True{} : Bool},
  ww: &w: Nat -> {BN.WAS(fa, st, L) == w : Nat}) ->
  {Nat.is_le(Nat.add(BN.needS(fa, T, st, L, e, nx, O2), X), Nat.add(Nat.add(ST.VQ(T, L, e, O, W0), D), X)) == True{} : Bool}:
  (+w, ew) = ww
  needs_leD.k(fa, T, L, e, O, W0, st, nx, O2, D, X, w, k, ST.eq2(BN.WAS(fa, st, L), w, ew))

law tl_absurd:
  for +c: String
  for +t: List<&2, String>
  for +h: {Nil{} == c <> t : List<&2, String>}
  Empty

def tl_absurd(c, t, h):
  PB.true_ne_false(Equal.cong(List<&2, String>, Bool, z => List.is_empty(&2, String, z), Nil{}, c <> t, h))

law seq_bud:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +ef: Bool
  for +O: String
  for +W0: Nat
  for s: Norm.Step
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for +hts: {BD.tots(PT.mkTOuts(fa, ps, xs)) == PT.texts(ps) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  for h: BDs.BudS(fa, T, List.append(&2, String, PT.texts(ps), cs), O, W0, s)
  ST.BudW(fa, T, cs, ef, O, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs)), W.seq_out(s, PT.mkTOuts(fa, ps, xs), e))

def seq_bud(fa, T, cs, ef, O, W0, s, ps, xs, e, hts, he, h):
  match s ps xs e:
    case Norm.Step{st, b, +ns, Pr.More{}} Nil{} Nil{} False{}:
      (hbi, k) = h
      +V0 = ST.VQ(T, cs, False{}, O, W0)
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
        %Equal.sym(Bool, ef, False{}, he) : {Nat.is_le(Nat.add(BN.needS(fa, T, st, cs, _, Pr.More{}, String.append(O, t)), BD.XK(cs)), Nat.add(Nat.add(V0, 1n), BD.XK(cs))) == True{} : Bool};
        needs_leD(fa, T, cs, False{}, O, W0, st, Pr.More{}, String.append(O, t), 1n, BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, cs)))
    case Norm.Step{st, b, +ns, Pr.More{}} Nil{} Nil{} True{}:
      (hbi, k) = h
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
        needs_ask(fa, T, cs, O, W0, st, String.append(O, t), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, cs)))
    case Norm.Step{st, b, +ns, Pr.More{}} Nil{} Con{+x, +xt} False{}:
      (hbi, k) = h
      +V0 = ST.VQ(T, cs, False{}, O, W0)
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
        %Equal.sym(Bool, ef, False{}, he) : {Nat.is_le(Nat.add(BN.needS(fa, T, st, cs, _, Pr.More{}, String.append(O, t)), BD.XK(cs)), Nat.add(Nat.add(V0, 1n), BD.XK(cs))) == True{} : Bool};
        needs_leD(fa, T, cs, False{}, O, W0, st, Pr.More{}, String.append(O, t), 1n, BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, cs)))
    case Norm.Step{st, b, +ns, Pr.More{}} Nil{} Con{+x, +xt} True{}:
      (hbi, k) = h
      hnf => (hbi, +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
        needs_ask(fa, T, cs, O, W0, st, String.append(O, t), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, cs)))
    case Norm.Step{st, b, +ns, Pr.More{}} Con{+p, +pt} Con{+x, +xt} _:
      (hbi, k) = h
      +L = List.append(&2, String, PT.texts(p <> pt), cs)
      hnf => (%Equal.sym(List<&2, String>, BD.tots(PT.mkTOuts(fa, p <> pt, x <> xt)), PT.texts(p <> pt), hts) : {BN.biS(st, List.append(&2, String, _, cs)) == True{} : Bool}; hbi,
        +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
          %Equal.sym(List<&2, String>, BD.tots(PT.mkTOuts(fa, p <> pt, x <> xt)), PT.texts(p <> pt), hts) :
            {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, List.append(&2, String, _, cs), False{}, Pr.Ask{Nil{}}, String.append(O, t)), 0n), BD.XK(cs)), Nat.add(Nat.add(ST.VQ(T, L, False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
          needs_ask(fa, T, L, O, W0, st, String.append(O, t), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, L)))
    case Norm.Step{st, b, +ns, Pr.More{}} Con{+p, +pt} Nil{} _:
      Empty.absurd(ST.BudW(fa, T, cs, ef, O, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(p <> pt), cs), False{}, O, W0), 1n), BD.XK(cs)), W.seq_out(Norm.Step{st, b, ns, Pr.More{}}, PT.mkTOuts(fa, p <> pt, Nil{}), e)),
        tl_absurd(PT.Pc.c(p), PT.texts(pt), hts))
    case Norm.Step{st, b, +ns, Pr.Ask{+r}} _ _ _:
      (hbi, k) = h
      +L = List.append(&2, String, PT.texts(ps), cs)
      hnf => (%Equal.sym(List<&2, String>, BD.tots(PT.mkTOuts(fa, ps, xs)), PT.texts(ps), hts) : {BN.biS(st, List.append(&2, String, _, cs)) == True{} : Bool}; hbi,
        +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
          %Equal.sym(List<&2, String>, BD.tots(PT.mkTOuts(fa, ps, xs)), PT.texts(ps), hts) :
            {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, List.append(&2, String, _, cs), False{}, Pr.Ask{r}, String.append(O, t)), 1n), BD.XK(cs)), Nat.add(Nat.add(ST.VQ(T, L, False{}, O, W0), 1n), BD.XK(cs))) == True{} : Bool};
          ST.needs_le2(fa, T, L, False{}, O, W0, st, Pr.Ask{r}, String.append(O, t), 1n, BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, L)))
    case Norm.Step{st, b, +ns, Pr.Finish{+c}} _ _ _:
      hnf => Empty.absurd(ST.BudC(fa, T, cs, ef, O, Nat.add(Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, W0), 1n), BD.XK(cs)), W.seq_out(Norm.Step{st, b, ns, Pr.Finish{c}}, PT.mkTOuts(fa, ps, xs), e)), PB.true_ne_false(hnf))
