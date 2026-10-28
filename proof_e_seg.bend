import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as P
import ./proof_e_defs.bend as SD
import ./proof_e_seg_main.bend as SM

# Phase E, area "seg": the segment lemma (notes/parallel_proofs.md). A task
# runs a piece's lines ls from SD.rs0(c0, l); when SD.segok holds of the true
# run S and the task's run, the true run over ls is SD.shiftS of the two (up
# to P.settle: the last item's text, which nothing reads).

# ---------------------------------------------------------------------------
# Deliverable (the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

law seg:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +S: R.RunSt
  for +ls: List<&2, B.Line>
  for +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}
  for +hk: {SD.segok(R.Opts.w(o), c0, l, S, L.run.go(ls, fa, o, SD.rs0(c0, l))) == True{} : Bool}
  {P.settle(L.run.go(ls, fa, o, S)) == P.settle(SD.shiftS(c0, S, L.run.go(ls, fa, o, SD.rs0(c0, l)))) : R.RunSt}

# The true run over ls is exactly shiftS of S and T (proof_e_seg_main.bend);
# settle both sides.
def seg(fa, o, c0, l, S, ls, hc, hk):
  Equal.cong(R.RunSt, R.RunSt, st => P.settle(st), L.run.go(ls, fa, o, S), SD.shiftS(c0, S, L.run.go(ls, fa, o, SD.rs0(c0, l))),
    SM.segx(fa, o, c0, l, S, ls, hc, hk))
