import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_text.bend as TX
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_c_txt_lem.bend as XL

# Phase C, area "txt": the letters norm_fix.bend writes for the normalized
# alleles (NX.al, NX.as.go; their texts without the buffers are
# proof_c_text.bend's ALA and ACC) are B.Allele.show of the closed form
# (Q.ALK), and the new POS word (TX.QQ) is VW's POS. Notes:
# notes/rewrite_tan.md (same agent). Hypotheses as norm_var's, with Q.KOK's
# facts.

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# One allele's letters: bases d .. L - tr - 1 of R_k ++ a, as Allele.show
# writes them.
def ala_show(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +wd: Nat,
  +a: NX.Ap, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat,
  +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool},
  +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool},
  +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool},
  +hl: {Nat.is_lt(Nat.add(Q.n(tr), d), Q.n(NX.Ap.ln(a))) == True{} : Bool}) ->
  {TX.ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu) == B.Allele.show(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) : String}:
  XL.ala_show_t(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hl)

# The ALTs' letters, commas between: the join of their Allele.show.
def acc_join(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +wd: Nat,
  +als: List<&2, NX.Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat,
  +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +ha: {Q.ALS_IN(bl, als) == True{} : Bool},
  +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool},
  +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool},
  +hkl: {Q.KL(als, tr, d) == True{} : Bool}) ->
  {TX.ACC(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu) == String.join(B.Alleles.show(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)), ",") : String}:
  XL.acc_join_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl)

# The new POS as the code computes it (a word, then a Nat) is VW's.
def qq_pos(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +p0: U32, +offu: U32, +k: U32, +d: Nat,
  +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool},
  +hps: {U32.is_lt(p0, 1000000000) == True{} : Bool},
  +hd: {Nat.is_lt(d, Q.n(bl)) == True{} : Bool}) ->
  {TX.QQ(p0, k, d) == Nat.add(Nat.sub(Q.n(p0), Q.n(k)), d) : Nat}:
  XL.qq_pos_t(bl, bt, bd, p0, offu, k, d, hb, hk, hps, hd)
