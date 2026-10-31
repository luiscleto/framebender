import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as P
import ./proof_b_simdefs.bend as S
import ./proof_b_frame_fr.bend as F
import ./proof_b_frame_bl.bend as BL

# Spec-level facts the simulation needs (run.bend and LAWS.bend only):
# what nothing reads any more does not change a report (P.settle), and the
# spec goes on the same with what the driver already collected in front
# (S.pre). The old String machine's proofs have most of this:
# proof_fast_run.bend (inv: blanking last) and proof_machine_frame.bend
# (fr_*: run.bend's functions commute with pre).

# The helpers' pre (proof_b_frame_fr.bend) is S.pre.
law pre_eq:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {F.pre(O, N, st) == S.pre(O, N, st) : R.RunSt}

def pre_eq(O, N, st):
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}


# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# A report does not depend on what settle forgets.
def settle_inv(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt) ->
  {R.finish(L.run.go(ls, fa, dfs, o, P.settle(st))) == R.finish(L.run.go(ls, fa, dfs, o, st)) : R.Report}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, False{}}:
      BL.inv(dfs, ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, so, ns, False{}})
    case R.RunSt{+n, True{}, +h, +c, +e, +l, +b, +k, +so, +ns, True{}}:
      +S1 = {R.RunSt{n, True{}, h, c, e, None{}, Nil{}, k, so, ns, True{}} : R.RunSt}
      +S0 = {R.RunSt{n, True{}, h, c, e, l, b, k, so, ns, True{}} : R.RunSt}
      Equal.trans(R.Report, R.finish(L.run.go(ls, fa, dfs, o, S1)), R.finish(S1), R.finish(L.run.go(ls, fa, dfs, o, S0)),
        Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, dfs, o, S1), S1, F.run_halted(dfs, ls, fa, o, S1, {==})),
        Equal.sym(R.Report, R.finish(L.run.go(ls, fa, dfs, o, S0)), R.finish(S0),
          Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, dfs, o, S0), S0, F.run_halted(dfs, ls, fa, o, S0, {==}))))
    case R.RunSt{+n, False{}, +h, +c, +e, +l, +b, +k, +so, +ns, True{}}:
      +S1 = {R.RunSt{n, False{}, h, c, e, None{}, Nil{}, k, so, ns, True{}} : R.RunSt}
      +S0 = {R.RunSt{n, False{}, h, c, e, l, b, k, so, ns, True{}} : R.RunSt}
      Equal.trans(R.Report, R.finish(L.run.go(ls, fa, dfs, o, S1)), R.finish(S1), R.finish(L.run.go(ls, fa, dfs, o, S0)),
        Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, dfs, o, S1), S1, F.run_halted(dfs, ls, fa, o, S1, {==})),
        Equal.sym(R.Report, R.finish(L.run.go(ls, fa, dfs, o, S0)), R.finish(S0),
          Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, dfs, o, S0), S0, F.run_halted(dfs, ls, fa, o, S0, {==}))))

# One line of the spec with O and N in front: the same line, then O and N in
# front (before the #CHROM line nothing has been written or noted).
def step_pre(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +O: String, +N: List<&2, B.Note>, +st: R.RunSt, +l: B.Line,
  hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}) ->
  {L.line_step(fa, dfs, o, S.pre(O, N, st), l) == S.pre(O, N, L.line_step(fa, dfs, o, st, l)) : R.RunSt}:
  %pre_eq(O, N, st) : {L.line_step(fa, dfs, o, _, l) == S.pre(O, N, L.line_step(fa, dfs, o, st, l)) : R.RunSt}
  %pre_eq(O, N, L.line_step(fa, dfs, o, st, l)) : {L.line_step(fa, dfs, o, F.pre(O, N, st), l) == _ : R.RunSt}
  F.step_pre(dfs, fa, o, O, N, st, l, hg)

# The whole rest of the run likewise.
def run_pre(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +O: String, +N: List<&2, B.Note>, +st: R.RunSt,
  hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}) ->
  {L.run.go(ls, fa, dfs, o, S.pre(O, N, st)) == S.pre(O, N, L.run.go(ls, fa, dfs, o, st)) : R.RunSt}:
  %pre_eq(O, N, st) : {L.run.go(ls, fa, dfs, o, _) == S.pre(O, N, L.run.go(ls, fa, dfs, o, st)) : R.RunSt}
  %pre_eq(O, N, L.run.go(ls, fa, dfs, o, st)) : {L.run.go(ls, fa, dfs, o, F.pre(O, N, st)) == _ : R.RunSt}
  F.run_pre(dfs, ls, fa, o, O, N, st, hg)

# The end of the run with O and N in front.
def finish_pre(+O: String, +N: List<&2, B.Note>, +st: R.RunSt,
  hg: {R.RunSt.inbody(st) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}) ->
  {R.finish(S.pre(O, N, st)) == R.Report{String.append(O, R.Report.out(R.finish(st))), List.append(&2, B.Note, N, R.Report.notes(R.finish(st))), R.Report.code(R.finish(st))} : R.Report}:
  %pre_eq(O, N, st) : {R.finish(_) == R.Report{String.append(O, R.Report.out(R.finish(st))), List.append(&2, B.Note, N, R.Report.notes(R.finish(st))), R.Report.code(R.finish(st))} : R.Report}
  F.finish_pre(O, N, st, hg)

# settle and pre commute.
def settle_pre(+O: String, +N: List<&2, B.Note>, +st: R.RunSt) ->
  {P.settle(S.pre(O, N, st)) == S.pre(O, N, P.settle(st)) : R.RunSt}:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, False{}}:
      {==}
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, True{}}:
      {==}

# A stopped run stays as it is.
def run_halted(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt,
  hh: {R.RunSt.halt(st) == True{} : Bool}) ->
  {L.run.go(ls, fa, dfs, o, st) == st : R.RunSt}:
  F.run_halted(dfs, ls, fa, o, st, hh)
