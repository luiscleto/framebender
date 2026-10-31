import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as PD
import ./proof_b_simdefs.bend as S
import ./proof_b_frame_bl.bend as BL
import ./proof_b_frame_fr.bend as FF
import ./proof_b_frame.bend as FR

# The records' steps (proof_b_simdefs.bend's rstep, rgo, RG) do not see the
# last item's text (blank_st); and a settled state stands for the same report
# through them. Every variable is reusable.

def Ls() -> Data:
  List<&2, B.Line>

def Ps() -> Data:
  List<&2, PD.SrcP>

def ut_bl(+st: R.RunSt) -> {Norm.rs_untick(PD.blank_st(st)) == PD.blank_st(Norm.rs_untick(st)) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

def halt_bl(+st: R.RunSt) -> {R.RunSt.halt(PD.blank_st(st)) == R.RunSt.halt(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

def bl_bl(+st: R.RunSt) -> {PD.blank_st(PD.blank_st(st)) == PD.blank_st(st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), BL.blank_blank(la)) :
        {R.RunSt{n, i, h, c, e, _, b, k, so, ns, x} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, x} : R.RunSt}
      {==}

def rstep_bl.k(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line, +hx: Bool, +e: {R.RunSt.halt(st) == hx : Bool}) ->
  {PD.blank_st(S.rstep.if(hx, fa, dfs, o, PD.blank_st(st), l)) == PD.blank_st(S.rstep.if(hx, fa, dfs, o, st, l)) : R.RunSt}:
  match hx:
    case True{}:
      bl_bl(st)
    case False{}:
      %Equal.sym(R.RunSt, Norm.rs_untick(PD.blank_st(st)), PD.blank_st(Norm.rs_untick(st)), ut_bl(st)) : {PD.blank_st(L.line_step(fa, dfs, o, _, l)) == PD.blank_st(L.line_step(fa, dfs, o, Norm.rs_untick(st), l)) : R.RunSt}
      BL.step_bl(dfs, fa, o, Norm.rs_untick(st), l)

law rstep_bl:
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  {PD.blank_st(S.rstep(fa, dfs, o, PD.blank_st(st), l)) == PD.blank_st(S.rstep(fa, dfs, o, st, l)) : R.RunSt}

def rstep_bl(fa, dfs, o, st, l):
  %Equal.sym(Bool, R.RunSt.halt(PD.blank_st(st)), R.RunSt.halt(st), halt_bl(st)) :
    {PD.blank_st(S.rstep.if(_, fa, dfs, o, PD.blank_st(st), l)) == PD.blank_st(S.rstep(fa, dfs, o, st, l)) : R.RunSt}
  rstep_bl.k(fa, dfs, o, st, l, R.RunSt.halt(st), {==})

law rgo_bl:
  for +ls: Ls()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  {PD.blank_st(S.rgo(ls, fa, dfs, o, PD.blank_st(st))) == PD.blank_st(S.rgo(ls, fa, dfs, o, st)) : R.RunSt}

def rgo_bl(ls, fa, dfs, o, st):
  match ls:
    case Nil{}:
      bl_bl(st)
    case Con{+l, +t}:
      +A = S.rstep(fa, dfs, o, PD.blank_st(st), l)
      +Bs = S.rstep(fa, dfs, o, st, l)
      Equal.trans(R.RunSt, PD.blank_st(S.rgo(t, fa, dfs, o, A)), PD.blank_st(S.rgo(t, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.rgo(t, fa, dfs, o, Bs)),
        Equal.sym(R.RunSt, PD.blank_st(S.rgo(t, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.rgo(t, fa, dfs, o, A)), rgo_bl(t, fa, dfs, o, A)),
        Equal.trans(R.RunSt, PD.blank_st(S.rgo(t, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.rgo(t, fa, dfs, o, PD.blank_st(Bs))), PD.blank_st(S.rgo(t, fa, dfs, o, Bs)),
          Equal.cong(R.RunSt, R.RunSt, z => PD.blank_st(S.rgo(t, fa, dfs, o, z)), PD.blank_st(A), PD.blank_st(Bs), rstep_bl(fa, dfs, o, st, l)),
          rgo_bl(t, fa, dfs, o, Bs)))

law rg_bl:
  for +rs: Ps()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  {PD.blank_st(S.RG(rs, fa, dfs, o, PD.blank_st(st))) == PD.blank_st(S.RG(rs, fa, dfs, o, st)) : R.RunSt}

def rg_bl(rs, fa, dfs, o, st):
  match rs:
    case Nil{}:
      bl_bl(st)
    case Con{PD.SPP{+len, +t, +d, +at}, +r}:
      +LS = B.Text.lines(PD.srctext(PD.SPP{len, t, d, at}))
      +A = S.rgo(LS, fa, dfs, o, PD.blank_st(st))
      +Bs = S.rgo(LS, fa, dfs, o, st)
      Equal.trans(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, A)), PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, Bs)),
        Equal.sym(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, A)), rg_bl(r, fa, dfs, o, A)),
        Equal.trans(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(Bs))), PD.blank_st(S.RG(r, fa, dfs, o, Bs)),
          Equal.cong(R.RunSt, R.RunSt, z => PD.blank_st(S.RG(r, fa, dfs, o, z)), PD.blank_st(A), PD.blank_st(Bs), rgo_bl(LS, fa, dfs, o, st)),
          rg_bl(r, fa, dfs, o, Bs)))
    case Con{PD.SRP{+l}, +r}:
      +A = S.rstep(fa, dfs, o, PD.blank_st(st), l)
      +Bs = S.rstep(fa, dfs, o, st, l)
      Equal.trans(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, A)), PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, Bs)),
        Equal.sym(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, A)), rg_bl(r, fa, dfs, o, A)),
        Equal.trans(R.RunSt, PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(A))), PD.blank_st(S.RG(r, fa, dfs, o, PD.blank_st(Bs))), PD.blank_st(S.RG(r, fa, dfs, o, Bs)),
          Equal.cong(R.RunSt, R.RunSt, z => PD.blank_st(S.RG(r, fa, dfs, o, z)), PD.blank_st(A), PD.blank_st(Bs), rstep_bl(fa, dfs, o, st, l)),
          rg_bl(r, fa, dfs, o, Bs)))
    case Con{PD.SBP{+len, +t, +d, +at}, +r}:
      bl_bl(st)
    case Con{PD.SLP{+q}, +r}:
      bl_bl(st)

# A stopped run goes through the records as it is.
law rgo_halted:
  for +ls: Ls()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +hh: {R.RunSt.halt(st) == True{} : Bool}
  {S.rgo(ls, fa, dfs, o, st) == st : R.RunSt}

def rgo_halted(ls, fa, dfs, o, st, hh):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      %Equal.sym(Bool, R.RunSt.halt(st), True{}, hh) : {S.rgo(t, fa, dfs, o, S.rstep.if(_, fa, dfs, o, st, l)) == st : R.RunSt}
      rgo_halted(t, fa, dfs, o, st, hh)

law rg_halted:
  for +rs: Ps()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +hh: {R.RunSt.halt(st) == True{} : Bool}
  {S.RG(rs, fa, dfs, o, st) == st : R.RunSt}

def rg_halted(rs, fa, dfs, o, st, hh):
  match rs:
    case Nil{}:
      {==}
    case Con{PD.SPP{+len, +t, +d, +at}, +r}:
      %Equal.sym(R.RunSt, S.rgo(B.Text.lines(PD.srctext(PD.SPP{len, t, d, at})), fa, dfs, o, st), st, rgo_halted(B.Text.lines(PD.srctext(PD.SPP{len, t, d, at})), fa, dfs, o, st, hh)) :
        {S.RG(r, fa, dfs, o, _) == st : R.RunSt}
      rg_halted(r, fa, dfs, o, st, hh)
    case Con{PD.SRP{+l}, +r}:
      %Equal.sym(Bool, R.RunSt.halt(st), True{}, hh) : {S.RG(r, fa, dfs, o, S.rstep.if(_, fa, dfs, o, st, l)) == st : R.RunSt}
      rg_halted(r, fa, dfs, o, st, hh)
    case Con{PD.SBP{+len, +t, +d, +at}, +r}:
      {==}
    case Con{PD.SLP{+q}, +r}:
      {==}

def REP(+ls: Ls(), +fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rs: Ps(), +st: R.RunSt) -> R.Report:
  R.finish(L.run.go(ls, fa, dfs, o, S.RG(rs, fa, dfs, o, st)))

# The report through the records, then the lines, from a settled run.
law rep_settle:
  for +ls: Ls()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +rs: Ps()
  for +st: R.RunSt
  {REP(ls, fa, dfs, o, rs, PD.settle(st)) == REP(ls, fa, dfs, o, rs, st) : R.Report}

def rep_settle(ls, fa, dfs, o, rs, st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case False{}:
          +s0 = {R.RunSt{n, i, h, c, e, la, b, k, so, ns, False{}} : R.RunSt}
          +A = S.RG(rs, fa, dfs, o, PD.blank_st(s0))
          +Bs = S.RG(rs, fa, dfs, o, s0)
          Equal.trans(R.Report, R.finish(L.run.go(ls, fa, dfs, o, A)), R.finish(L.run.go(ls, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(ls, fa, dfs, o, Bs)),
            Equal.sym(R.Report, R.finish(L.run.go(ls, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(ls, fa, dfs, o, A)), BL.inv(dfs, ls, fa, o, A)),
            Equal.trans(R.Report, R.finish(L.run.go(ls, fa, dfs, o, PD.blank_st(A))), R.finish(L.run.go(ls, fa, dfs, o, PD.blank_st(Bs))), R.finish(L.run.go(ls, fa, dfs, o, Bs)),
              Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(ls, fa, dfs, o, z)), PD.blank_st(A), PD.blank_st(Bs), rg_bl(rs, fa, dfs, o, s0)),
              BL.inv(dfs, ls, fa, o, Bs)))
        case True{}:
          +s0 = {R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}} : R.RunSt}
          +s1 = {R.RunSt{n, i, h, c, e, None{}, Nil{}, k, so, ns, True{}} : R.RunSt}
          %Equal.sym(R.RunSt, S.RG(rs, fa, dfs, o, s1), s1, rg_halted(rs, fa, dfs, o, s1, {==})) : {R.finish(L.run.go(ls, fa, dfs, o, _)) == REP(ls, fa, dfs, o, rs, s0) : R.Report}
          %Equal.sym(R.RunSt, S.RG(rs, fa, dfs, o, s0), s0, rg_halted(rs, fa, dfs, o, s0, {==})) : {R.finish(L.run.go(ls, fa, dfs, o, s1)) == R.finish(L.run.go(ls, fa, dfs, o, _)) : R.Report}
          FR.settle_inv(dfs, ls, fa, o, s0)

# settle ignores the last item's text.
def settle_bl(+st: R.RunSt) -> {PD.settle(PD.blank_st(st)) == PD.settle(st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case False{}:
          %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), BL.blank_blank(la)) :
            {R.RunSt{n, i, h, c, e, _, b, k, so, ns, False{}} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, False{}} : R.RunSt}
          {==}
        case True{}:
          {==}

def settle_settle(+st: R.RunSt) -> {PD.settle(PD.settle(st)) == PD.settle(st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case False{}:
          %Equal.sym(Maybe<&2, R.Item>, PD.blank(PD.blank(la)), PD.blank(la), BL.blank_blank(la)) :
            {R.RunSt{n, i, h, c, e, _, b, k, so, ns, False{}} == R.RunSt{n, i, h, c, e, PD.blank(la), b, k, so, ns, False{}} : R.RunSt}
          {==}
        case True{}:
          {==}

# The records' steps, settled, from a settled run.
law rg_settle:
  for +rs: Ps()
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  {PD.settle(S.RG(rs, fa, dfs, o, PD.settle(st))) == PD.settle(S.RG(rs, fa, dfs, o, st)) : R.RunSt}

def rg_settle(rs, fa, dfs, o, st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      match x:
        case False{}:
          +s0 = {R.RunSt{n, i, h, c, e, la, b, k, so, ns, False{}} : R.RunSt}
          +A = S.RG(rs, fa, dfs, o, PD.blank_st(s0))
          +Bs = S.RG(rs, fa, dfs, o, s0)
          Equal.trans(R.RunSt, PD.settle(A), PD.settle(PD.blank_st(A)), PD.settle(Bs),
            Equal.sym(R.RunSt, PD.settle(PD.blank_st(A)), PD.settle(A), settle_bl(A)),
            Equal.trans(R.RunSt, PD.settle(PD.blank_st(A)), PD.settle(PD.blank_st(Bs)), PD.settle(Bs),
              Equal.cong(R.RunSt, R.RunSt, z => PD.settle(z), PD.blank_st(A), PD.blank_st(Bs), rg_bl(rs, fa, dfs, o, s0)),
              settle_bl(Bs)))
        case True{}:
          +s0 = {R.RunSt{n, i, h, c, e, la, b, k, so, ns, True{}} : R.RunSt}
          +s1 = {R.RunSt{n, i, h, c, e, None{}, Nil{}, k, so, ns, True{}} : R.RunSt}
          %Equal.sym(R.RunSt, S.RG(rs, fa, dfs, o, s1), s1, rg_halted(rs, fa, dfs, o, s1, {==})) : {PD.settle(_) == PD.settle(S.RG(rs, fa, dfs, o, s0)) : R.RunSt}
          %Equal.sym(R.RunSt, S.RG(rs, fa, dfs, o, s0), s0, rg_halted(rs, fa, dfs, o, s0, {==})) : {PD.settle(s1) == PD.settle(_) : R.RunSt}
          {==}
