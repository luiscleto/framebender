import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as P
import ./proof_b_frame.bend as FR
import ./proof_b_frame_bl.bend as BLF

# Phase E, area D (task): the spec side of a task's loop. What a run reads of
# a state is its settled form, so states equal once settled stay so after
# more lines; and lines handled one batch after another are handled at once.

def settle_bl(+st: R.RunSt) -> {P.settle(P.blank_st(st)) == P.settle(st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      %Equal.sym(Maybe<&2, R.Item>, P.blank(P.blank(l)), P.blank(l), BLF.blank_blank(l)) : {R.RunSt{n, i, h, c, e, _, b, k, o, ns, False{}} == R.RunSt{n, i, h, c, e, P.blank(l), b, k, o, ns, False{}} : R.RunSt}
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      {==}

# Blanking the last item's text changes nothing that settle keeps, line
# after line.
def go_bl(+ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt) ->
  {P.settle(L.run.go(ls, fa, o, P.blank_st(st))) == P.settle(L.run.go(ls, fa, o, st)) : R.RunSt}:
  match ls:
    case Nil{}:
      settle_bl(st)
    case +l <> +t:
      +A = L.line_step(fa, o, P.blank_st(st), l)
      +Bs = L.line_step(fa, o, st, l)
      Equal.trans(R.RunSt, P.settle(L.run.go(t, fa, o, A)), P.settle(L.run.go(t, fa, o, P.blank_st(A))), P.settle(L.run.go(t, fa, o, Bs)),
        Equal.sym(R.RunSt, P.settle(L.run.go(t, fa, o, P.blank_st(A))), P.settle(L.run.go(t, fa, o, A)), go_bl(t, fa, o, A)),
        Equal.trans(R.RunSt, P.settle(L.run.go(t, fa, o, P.blank_st(A))), P.settle(L.run.go(t, fa, o, P.blank_st(Bs))), P.settle(L.run.go(t, fa, o, Bs)),
          Equal.cong(R.RunSt, R.RunSt, z => P.settle(L.run.go(t, fa, o, z)), P.blank_st(A), P.blank_st(Bs), BLF.step_bl(fa, o, st, l)),
          go_bl(t, fa, o, Bs)))

# A run from a settled state settles as the run from the state.
def go_settle(+ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt) ->
  {P.settle(L.run.go(ls, fa, o, P.settle(st))) == P.settle(L.run.go(ls, fa, o, st)) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, False{}}:
      go_bl(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, so, ns, False{}})
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, True{}}:
      +S1 = {R.RunSt{n, i, h, c, e, None{}, Nil{}, k, so, ns, True{}} : R.RunSt}
      +S0 = {R.RunSt{n, i, h, c, e, l, b, k, so, ns, True{}} : R.RunSt}
      %Equal.sym(R.RunSt, L.run.go(ls, fa, o, S1), S1, FR.run_halted(ls, fa, o, S1, {==})) :
        {P.settle(_) == P.settle(L.run.go(ls, fa, o, S0)) : R.RunSt}
      %Equal.sym(R.RunSt, L.run.go(ls, fa, o, S0), S0, FR.run_halted(ls, fa, o, S0, {==})) :
        {P.settle(S1) == P.settle(_) : R.RunSt}
      {==}

# States equal once settled stay so after more lines.
def go_cong(+ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +A: R.RunSt, +Bs: R.RunSt,
  +h: {P.settle(A) == P.settle(Bs) : R.RunSt}) ->
  {P.settle(L.run.go(ls, fa, o, A)) == P.settle(L.run.go(ls, fa, o, Bs)) : R.RunSt}:
  Equal.trans(R.RunSt, P.settle(L.run.go(ls, fa, o, A)), P.settle(L.run.go(ls, fa, o, P.settle(A))), P.settle(L.run.go(ls, fa, o, Bs)),
    Equal.sym(R.RunSt, P.settle(L.run.go(ls, fa, o, P.settle(A))), P.settle(L.run.go(ls, fa, o, A)), go_settle(ls, fa, o, A)),
    Equal.trans(R.RunSt, P.settle(L.run.go(ls, fa, o, P.settle(A))), P.settle(L.run.go(ls, fa, o, P.settle(Bs))), P.settle(L.run.go(ls, fa, o, Bs)),
      Equal.cong(R.RunSt, R.RunSt, z => P.settle(L.run.go(ls, fa, o, z)), P.settle(A), P.settle(Bs), h),
      go_settle(ls, fa, o, Bs)))

# Lines handled one batch after another.
def go_app(+xs: List<&2, B.Line>, +ys: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt) ->
  {L.run.go(List.append(&2, B.Line, xs, ys), fa, o, st) == L.run.go(ys, fa, o, L.run.go(xs, fa, o, st)) : R.RunSt}:
  match xs:
    case Nil{}:
      {==}
    case +l <> +t:
      go_app(t, ys, fa, o, L.line_step(fa, o, st, l))

# One more step of a task's loop: lines ls1 took S0 to a state settling as
# rp1's, lines ls2 took rp1's to rp2's; so ls1 ++ ls2 take S0 to rp2's.
def go_step(+ls1: List<&2, B.Line>, +ls2: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +S0: R.RunSt, +s1: R.RunSt, +s2: R.RunSt,
  +h1: {P.settle(s1) == P.settle(L.run.go(ls1, fa, o, S0)) : R.RunSt},
  +h2: {P.settle(s2) == P.settle(L.run.go(ls2, fa, o, s1)) : R.RunSt}) ->
  {P.settle(s2) == P.settle(L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o, S0)) : R.RunSt}:
  %Equal.sym(R.RunSt, L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o, S0), L.run.go(ls2, fa, o, L.run.go(ls1, fa, o, S0)), go_app(ls1, ls2, fa, o, S0)) : {P.settle(s2) == P.settle(_) : R.RunSt}
  Equal.trans(R.RunSt, P.settle(s2), P.settle(L.run.go(ls2, fa, o, s1)), P.settle(L.run.go(ls2, fa, o, L.run.go(ls1, fa, o, S0))),
    h2, go_cong(ls2, fa, o, s1, L.run.go(ls1, fa, o, S0), h1))
