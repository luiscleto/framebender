import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ./proof_c_tan_pair.bend as TP
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_sim.bend as TS
import ./proof_c_tan_run.bend as TR
import ../lawful-words/proof_nat.bend as N

# Phase C, area "tan": Tan et al.'s algorithm on bytes (norm_fix.bend's
# NX.norm) is tan.bend's var_in. Notes: notes/rewrite_tan.md; the plan and
# the closed form: notes/rewrite.md.
#
# Notation (proof_c_defs.bend): the line is the mirror C.BT(bl, bt), the
# window C.BT(wl, wt) (the reference letters from contig index offu); Q.xs
# is a mirror's view; Q.NZ is NX.norm with C.AT for its byte reads; Q.V0 is
# the record's variant (bases as B.Base.of_fasta reads them); Q.VW the
# variant the counters stand for.

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# NX.norm hands both buffers back, with the counters Q.NZ computes.
def norm_pair(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +als: List<&2, NX.Ap>, +p0: U32, +offu: U32) ->
  {NX.norm(C.BT(bl, bt), C.BT(wl, wt), als, p0, offu) == Q.NZB(bl, bt, wl, wt, Q.NZ(bl, bt, wl, wt, als, p0, offu)) : NX.Nr}:
  TP.norm_pair_t(bl, bt, wl, wt, als, p0, offu)

# When it answers, the counters are var_in's normalized variant on the
# window, and they keep the shifts inside the window and every allele one
# base or more long.
def norm_var(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +wd: Nat,
  +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat,
  +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +ha: {Q.ALS_IN(bl, als) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, NX.Ap, als)) == True{} : Bool},
  +ho1: {Nat.is_lt(Q.n(offu), Q.n(p0)) == True{} : Bool},
  +ho2: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool},
  +hz: {Q.NZ(bl, bt, wl, wt, als, p0, offu) == Some{Q.K3{k, tr, d}} : Maybe<&2, Q.K3>}) ->
  {V.var_in(Q.n(offu), Q.BF(Q.xs(wl, wt)), Q.V0(Q.xs(bl, bt), als, p0)) == Some{Q.VW(Q.xs(bl, bt), Q.xs(wl, wt), als, p0, offu, k, tr, d)} : Maybe<&2, B.Var>}
  & {Q.KOK(als, p0, offu, k, tr, d) == True{} : Bool}:
  match als:
    case Nil{}:
      +ys = Q.xs(bl, bt)
      +ws = Q.xs(wl, wt)
      Empty.absurd({V.var_in(Q.n(offu), Q.BF(ws), Q.V0(ys, Nil{}, p0)) == Some{Q.VW(ys, ws, Nil{}, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(Nil{}, p0, offu, k, tr, d) == True{} : Bool}, N.false_ne_true(hn))
    case +a <> +t:
      +L = {a <> t : List<&2, NX.Ap>}
      +ys = Q.xs(bl, bt)
      +ws = Q.xs(wl, wt)
      +np = Q.n(p0)
      +off = Q.n(offu)
      +bases = Q.BF(ws)
      +A0 = Q.ALKS(ys, ws, p0, offu, L, 0, 0, 0n)
      +fu = Nat.add(np, NX.tot(L, 0))
      +hk0 = TL.lt_succ_le(off, np, ho1)
      +hkl0 = TS.kl0(L, bl, ha)
      +c0 = Q.NEXT(bl, bt, wl, wt, L, p0, offu, 0, 0)
      +M = Q.RIGHT(fu, c0, bl, bt, wl, wt, L, p0, offu, 0, 0)
      %Equal.sym(List<&2, List<&2, B.Base>>, Q.BFS(ys, L), A0, TS.bfs_init(L, bl, bt, wl, wt, p0, offu)) :
        {V.left_of(V.right(Nat.add(np, V.total(_)), V.next_act(off, bases, np, _), off, bases, np, _)) == Some{Q.VW(ys, ws, L, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(L, p0, offu, k, tr, d) == True{} : Bool}
      %N.sub_zero(np) :
        {V.left_of(V.right(Nat.add(np, V.total(A0)), V.next_act(off, bases, _, A0), off, bases, _, A0)) == Some{Q.VW(ys, ws, L, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(L, p0, offu, k, tr, d) == True{} : Bool}
      %Equal.sym(Nat, V.total(A0), NX.tot(L, 0), TS.alks_total(L, bl, bt, bd, wl, wt, wd, p0, offu, 0, 0, hb, hw, ha, hk0, ho2, hkl0)) :
        {V.left_of(V.right(Nat.add(np, _), V.next_act(off, bases, Nat.sub(np, 0n), A0), off, bases, Nat.sub(np, 0n), A0)) == Some{Q.VW(ys, ws, L, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(L, p0, offu, k, tr, d) == True{} : Bool}
      %Equal.sym(V.Act, V.next_act(off, bases, Nat.sub(np, 0n), A0), TR.ACT(wl, wt, p0, offu, 0, c0), TR.step(L, bl, bt, bd, wl, wt, wd, p0, offu, 0, 0, hb, hw, ha, hk0, ho2, hkl0)) :
        {V.left_of(V.right(fu, _, off, bases, Nat.sub(np, 0n), A0)) == Some{Q.VW(ys, ws, L, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(L, p0, offu, k, tr, d) == True{} : Bool}
      %Equal.sym(Maybe<&2, V.Cur>, V.right(fu, TR.ACT(wl, wt, p0, offu, 0, c0), off, bases, Nat.sub(np, 0n), A0), TR.RL(bl, bt, wl, wt, p0, offu, L, M),
          Pair.fst({V.right(fu, TR.ACT(wl, wt, p0, offu, 0, c0), off, bases, Nat.sub(np, 0n), A0) == TR.RL(bl, bt, wl, wt, p0, offu, L, M) : Maybe<&2, V.Cur>}, {TR.OKM(L, p0, offu, M) == True{} : Bool}, TR.right_sim(fu, c0, L, bl, bt, bd, wl, wt, wd, p0, offu, 0, 0, {==}, hb, hw, ha, hk0, ho2, hkl0))) :
        {V.left_of(_) == Some{Q.VW(ys, ws, L, p0, offu, k, tr, d)} : Maybe<&2, B.Var>} & {Q.KOK(L, p0, offu, k, tr, d) == True{} : Bool}
      TR.fin(M, L, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hz, Pair.snd({V.right(fu, TR.ACT(wl, wt, p0, offu, 0, c0), off, bases, Nat.sub(np, 0n), A0) == TR.RL(bl, bt, wl, wt, p0, offu, L, M) : Maybe<&2, V.Cur>}, {TR.OKM(L, p0, offu, M) == True{} : Bool}, TR.right_sim(fu, c0, L, bl, bt, bd, wl, wt, wd, p0, offu, 0, 0, {==}, hb, hw, ha, hk0, ho2, hkl0)), hb, hw, ha, ho2)
