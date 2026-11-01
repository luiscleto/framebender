import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PR
import ./proof_b_simdefs.bend as S
import ./proof_e_defs.bend as SD
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_b_run_inv.bend as PI
import ./proof_e_merge_lem.bend as ML
import ./proof_e_merge_ok.bend as OK
import ./proof_e_merge_inv.bend as MI
import ./proof_e_merge_seg.bend as MG
import ./proof_e_merge_spec.bend as MP

# Phase E, area "merge": norm_par.bend's merge on pictured runs
# (notes/parallel_proofs.md). merge.ok on the byte runs gives SD.segok on the
# states they stand for; the run merge.if builds is good and stands for
# SD.shiftS, with S's whole output buffer and its messages handed out (T's,
# renumbered, stay in the merged run).

# merge.ok on two pictured runs (s: the true run, t: the task's).
def okP(+l: Nat, +w: Nat, +c0: String, +s: P.RunP, +t: P.RunP) -> Bool:
  match s t:
    case P.RunP{sn, +si, sh, +sc, scbl, scbt, +se, +sl, +sf, +sb, +sbn, +stl, sk, sobl, sobt, sow, sns, +sx} P.RunP{+tn, +ti, th, +tc, tcbl, tcbt, +te, +tl, +tf, +tb, tbn, ttl, tk, tobl, tobt, tow, +tns, +tx}:
      W.merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx)

# The run merge.if builds, pictured.
def mergeP(+c0: String, +s: P.RunP, +t: P.RunP) -> P.RunP:
  match s t:
    case P.RunP{+sn, si, +sh, +sc, scbl, scbt, +se, +sl, +sf, +sb, sbn, stl, +sk, sobl, sobt, sow, sns, sx} P.RunP{+tn, ti, th, +tc, +tcbl, +tcbt, +te, +tl, +tf, +tb, +tbn, +ttl, +tk, +tobl, +tobt, +tow, +tns, tx}:
      +same = R.is_cur(sc, c0)
      P.RunP{Nat.add(sn, tn), True{}, sh, tc, tcbl, tcbt, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, NR.push_cur(sc, se))), W.last_of(tl, same, sl, W.buf_last(sf, sb), sn), W.cks_shift(sn, tf), W.cks_shift(sn, tb), tbn, ttl, W.cnt_add(sk, tk), tobl, tobt, tow, W.notes_shift(sn, tns), False{}}

def RunP.ns(p: P.RunP) -> List<&2, B.Note>:
  match p:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      ns

def RunP.obt(p: P.RunP) -> AT.Tree<U32>:
  match p:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      obt

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# merge computes: MOk when merge.ok holds ...
law merge_yes:
  for +l: Nat
  for +w: Nat
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  for +hok: {okP(l, w, c0, s, t) == True{} : Bool}
  {W.merge(P.mkRun(s), P.mkRun(t), l, w, c0) == W.MOk{C.BT(P.RunP.obl(s), RunP.obt(s)), List.reverse(&2, B.Note, RunP.ns(s)), P.mkRun(mergeP(c0, s, t))} : W.Mg}

def merge_yes(l, w, c0, s, t, hok):
  match s t:
    case P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx} P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}:
      %Equal.sym(Bool, W.merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx), True{}, hok) : {W.merge.if(_, NR.Run{sn, si, sh, sc, C.BT(scbl, scbt), se, sl, sf, sb, sbn, stl, sk, C.BT(sobl, sobt), sow, sns, sx}, NR.Run{tn, ti, th, tc, C.BT(tcbl, tcbt), te, tl, tf, tb, tbn, ttl, tk, C.BT(tobl, tobt), tow, tns, tx}, R.is_cur(sc, c0)) == W.MOk{C.BT(sobl, sobt), List.reverse(&2, B.Note, sns), P.mkRun(mergeP(c0, P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx}, P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}))} : W.Mg}
      {==}

# ... else MNo, the true run unchanged.
law merge_no:
  for +l: Nat
  for +w: Nat
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  for +hok: {okP(l, w, c0, s, t) == False{} : Bool}
  {W.merge(P.mkRun(s), P.mkRun(t), l, w, c0) == W.MNo{P.mkRun(s)} : W.Mg}

def merge_no(l, w, c0, s, t, hok):
  match s t:
    case P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx} P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}:
      %Equal.sym(Bool, W.merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx), False{}, hok) : {W.merge.if(_, NR.Run{sn, si, sh, sc, C.BT(scbl, scbt), se, sl, sf, sb, sbn, stl, sk, C.BT(sobl, sobt), sow, sns, sx}, NR.Run{tn, ti, th, tc, C.BT(tcbl, tcbt), te, tl, tf, tb, tbn, ttl, tk, C.BT(tobl, tobt), tow, tns, tx}, R.is_cur(sc, c0)) == W.MNo{NR.Run{sn, si, sh, sc, C.BT(scbl, scbt), se, sl, sf, sb, sbn, stl, sk, C.BT(sobl, sobt), sow, sns, sx}} : W.Mg}
      {==}

# The merged run is good.
law merge_inv:
  for +l: Nat
  for +w: Nat
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  for +hs: {PR.RunInv(s) == True{} : Bool}
  for +ht: {PR.RunInv(t) == True{} : Bool}
  for +hok: {okP(l, w, c0, s, t) == True{} : Bool}
  {PR.RunInv(mergeP(c0, s, t)) == True{} : Bool}

def merge_inv(l, w, c0, s, t, hs, ht, hok):
  match s t:
    case P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx} P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}:
      MI.inv_w(sh, ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, tx, sn,
        PI.pr9(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx, hs), ht,
        ML.not_t(tx, OK.ok4(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx, hok)))

# merge.ok gives the segment lemma's condition on the states they stand for.
law merge_segok:
  for +l: Nat
  for +w: Nat
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  for +hs: {PR.RunInv(s) == True{} : Bool}
  for +ht: {PR.RunInv(t) == True{} : Bool}
  for +hok: {okP(l, w, c0, s, t) == True{} : Bool}
  {SD.segok(w, c0, l, P.specRun(s), P.specRun(t)) == True{} : Bool}

def merge_segok(l, w, c0, s, t, hs, ht, hok):
  match s t:
    case P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx} P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}:
      MG.segok_w(w, c0, l, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx,
        Maybe.default(&2, String, sc, ""), String.drop(P.obtext(P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx}), U32.to_nat(sow)),
        Maybe.default(&2, String, tc, ""), String.drop(P.obtext(P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}), U32.to_nat(tow)),
        hok,
        PI.pr6(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx, hs),
        PI.pr7(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx, hs),
        PI.pr8(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx, hs))

# The merged run, with S's whole buffer (its output, then its buffered
# texts) and S's messages handed out before it, stands for SD.shiftS.
law merge_spec:
  for +l: Nat
  for +w: Nat
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  for +hs: {PR.RunInv(s) == True{} : Bool}
  for +ht: {PR.RunInv(t) == True{} : Bool}
  for +hok: {okP(l, w, c0, s, t) == True{} : Bool}
  {P.settle(S.pre(P.obtext(s), List.reverse(&2, B.Note, RunP.ns(s)), P.specRun(mergeP(c0, s, t)))) == P.settle(SD.shiftS(c0, P.specRun(s), P.specRun(t))) : R.RunSt}

def merge_spec(l, w, c0, s, t, hs, ht, hok):
  match s t:
    case P.RunP{sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx} P.RunP{tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx}:
      MP.spec_w(l, w, c0, sn, si, sh, sc, scbl, scbt, se, sl, sf, sb, sbn, stl, sk, sobl, sobt, sow, sns, sx, tn, ti, th, tc, tcbl, tcbt, te, tl, tf, tb, tbn, ttl, tk, tobl, tobt, tow, tns, tx, hs, hok)
