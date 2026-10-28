import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_c_bud_k.bend as BK
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Phase C: the budget on the rewrite path (norm.bend fix): a rewritten line
# is one Went that asks nothing; the declined cases are the decoded path's.
# Every variable is reusable.

def fix_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  BK.fix_ok(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs)
