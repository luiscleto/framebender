import Base
import ./types.bend as B
import ./run.bend as R
import ./norm.bend as Norm
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv.bend as AD

# The simulation's per-line lemma (definitions: proof_b_simdefs.bend). Its
# proof is the adv area's (proof_b_adv*.bend, which import the definitions
# file); this body calls it.

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# Handling the next line keeps a good state standing for the same report.
def adv_ok(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, p, Norm.advance(S.mkSt(fa, p))):
  AD.adv(fa, T, cs, O, N, p, hb, hw, hr, hg)
