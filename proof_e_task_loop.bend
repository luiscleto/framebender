import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PR
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SIM
import ./proof_b_adv_msx.bend as MSX
import ./proof_e_defs.bend as SD
import ./proof_e_task_buf.bend as BUF
import ./proof_e_task_ms.bend as MS
import ./proof_e_task_run.bend as RN
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# Phase E, area D (task): a task's loop (norm_par.bend's task.loop), run
# with adv_ok from a good state. Invariant: Q's state is a good picture p
# standing for the report T, outside the end of the file, with the batch's
# options; while in the byte mode, the lines LA still to come at the start
# are the lines ls it handled followed by the lines still to come at p, and
# its run settles as the spec's run of ls from the phantom state. The spare
# windows are good pictures.

# ---------------------------------------------------------------------------
# Pictures
# ---------------------------------------------------------------------------

def mkWins(+fa: List<&2, B.Contig>, +sp: List<&2, PC.WP>) -> List<&1, Q.Win>:
  match sp:
    case Nil{}:
      Nil{}
    case +wp <> t:
      PC.mkWin(fa, wp) <> mkWins(fa, t)

def wins_ok(+fa: List<&2, B.Contig>, +sp: List<&2, PC.WP>) -> Bool:
  match sp:
    case Nil{}:
      True{}
    case +wp <> t:
      PC.wp_ok(fa, wp) && S.mb_win.k(wp) && wins_ok(fa, t)

def Trk.md(+m: S.MdP, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP) -> Type:
  match m:
    case S.MBP{+rp}:
      &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(S.intext(p, cs))) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt})
    case S.MSP{s, qs, ql, code}:
      Unit

def Trk(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP) -> Type:
  Trk.md(S.StP.md(p), fa, o, cs, c0, l, LA, p)

def Inv(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +T: R.Report, +p: S.StP) -> Type:
  {S.WF(fa, p) == True{} : Bool} & ({S.report(fa, cs, "", Nil{}, p) == T : R.Report} & ({S.guard("", Nil{}, p) == True{} : Bool}
    & ({S.StP.eof(p) == False{} : Bool} & ({S.StP.o(p) == o : B.Opts} & Trk(fa, o, cs, c0, l, LA, p)))))

# A task's result, pictured.
type LR is Data:
  LDirty{}
  LClean{rp: P.RunP, pd: P.PdP, wp: PC.WP}

def mkLR(+fa: List<&2, B.Contig>, +k: U32, +c0: String, +l: Nat, +x: LR) -> W.TRes:
  match x:
    case LDirty{}:
      W.TDirty{}
    case LClean{+rp, +pd, +wp}:
      W.TClean{W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}}

# proof_e_task.bend's TcOK, with LA for the lines of the piece after k and
# the text after it.
def LRok(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +x: LR) -> Type:
  match x:
    case LDirty{}:
      Unit
    case LClean{+rp, +pd, +wp}:
      {PR.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool}
        & (&ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pd), String.concat(cs)))) : List<&2, B.Line>}
          & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt}))

def LoopG(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, -r: W.TRes) -> Type:
  &x: LR -> ({r == mkLR(fa, k, c0, l, x) : W.TRes} & LRok(fa, o, cs, c0, l, LA, x))

# ---------------------------------------------------------------------------
# One advance: the lines handled compose
# ---------------------------------------------------------------------------

def app_assoc(+xs: List<&2, B.Line>, +ys: List<&2, B.Line>, +zs: List<&2, B.Line>) ->
  {List.append(&2, B.Line, List.append(&2, B.Line, xs, ys), zs) == List.append(&2, B.Line, xs, List.append(&2, B.Line, ys, zs)) : List<&2, B.Line>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, B.Line>, List.append(&2, B.Line, List.append(&2, B.Line, t, ys), zs), List.append(&2, B.Line, t, List.append(&2, B.Line, ys, zs)), app_assoc(t, ys, zs)) :
        {x <> _ == x <> List.append(&2, B.Line, t, List.append(&2, B.Line, ys, zs)) : List<&2, B.Line>}
      {==}

def trk_mb(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>,
  +rp: P.RunP, +rp2: P.RunP, +X1: String, +X2: String,
  t1: &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(X1)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt}),
  t2: &ls: List<&2, B.Line> -> ({B.Text.lines(X1) == List.append(&2, B.Line, ls, B.Text.lines(X2)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, o, P.specRun(rp))) : R.RunSt})) ->
  &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(X2)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt}):
  (+ls1, a1) = t1
  (e1, s1) = a1
  (+ls2, a2) = t2
  (e2, s2) = a2
  +L2 = B.Text.lines(X2)
  (List.append(&2, B.Line, ls1, ls2),
    (Equal.trans(List<&2, B.Line>, LA, List.append(&2, B.Line, ls1, B.Text.lines(X1)), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), e1,
      Equal.trans(List<&2, B.Line>, List.append(&2, B.Line, ls1, B.Text.lines(X1)), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2),
        Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => List.append(&2, B.Line, ls1, z), B.Text.lines(X1), List.append(&2, B.Line, ls2, L2), e2),
        Equal.sym(List<&2, B.Line>, List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), app_assoc(ls1, ls2, L2)))),
    RN.go_step(ls1, ls2, fa, o, SD.rs0(c0, l), P.specRun(rp), P.specRun(rp2), s1, s2)))

# The invariant's lines and run after one advance from p to p2 (String mode
# stays String mode).
def trk_md(+m: S.MdP, +m2: S.MdP, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP, +p2: S.StP,
  t: Trk.md(m, fa, o, cs, c0, l, LA, p),
  mv: S.Moved.md(m, m2, fa, cs, p, p2),
  +ho: {S.StP.o(p) == o : B.Opts},
  hms: {MS.md_ms_p(m) == True{} : Bool} -> {MS.md_ms_p(m2) == True{} : Bool}) ->
  Trk.md(m2, fa, o, cs, c0, l, LA, p2):
  match m m2:
    case S.MBP{+rp} S.MBP{+rp2}:
      trk_mb(fa, o, cs, c0, l, LA, rp, rp2, S.intext(p, cs), S.intext(p2, cs), t,
        %ho : &ls: List<&2, B.Line> -> ({B.Text.lines(S.intext(p, cs)) == List.append(&2, B.Line, ls, B.Text.lines(S.intext(p2, cs))) : List<&2, B.Line>}
          & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, _, P.specRun(rp))) : R.RunSt})
        mv)
    case S.MBP{+rp} S.MSP{+s, +qs, +ql, +code}:
      Unit{}
    case S.MSP{+s, +qs, +ql, +code} S.MBP{+rp2}:
      Empty.absurd(Trk.md(S.MBP{rp2}, fa, o, cs, c0, l, LA, p2), N.false_ne_true(hms({==})))
    case S.MSP{+s, +qs, +ql, +code} S.MSP{+s2, +qs2, +ql2, +code2}:
      Unit{}

# ---------------------------------------------------------------------------
# The end of a task (Idle)
# ---------------------------------------------------------------------------

# Once in the body, the run stays there.
def go_ib(+ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt,
  +hi: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {R.RunSt.inbody(L.run.go(ls, fa, o, st)) == True{} : Bool}:
  match ls:
    case Nil{}:
      hi
    case +x <> +t:
      go_ib(t, fa, o, L.line_step(fa, o, st, x), MSX.ib_step(fa, o, st, x, hi))

def ib_settle(+st: R.RunSt) -> {R.RunSt.inbody(P.settle(st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, False{}}:
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, True{}}:
      {==}

def i_spec(+rp: P.RunP) -> {P.RunP.i(rp) == R.RunSt.inbody(P.specRun(rp)) : Bool}:
  match rp:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      {==}

# A run that settles as the spec's run from the phantom state is in the body.
def i_of(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +rp: P.RunP, +ls: List<&2, B.Line>,
  +h: {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt}) ->
  {P.RunP.i(rp) == True{} : Bool}:
  +G = L.run.go(ls, fa, o, SD.rs0(c0, l))
  Equal.trans(Bool, P.RunP.i(rp), R.RunSt.inbody(P.specRun(rp)), True{}, i_spec(rp),
    Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), R.RunSt.inbody(P.settle(P.specRun(rp))), True{}, Equal.sym(Bool, R.RunSt.inbody(P.settle(P.specRun(rp))), R.RunSt.inbody(P.specRun(rp)), ib_settle(P.specRun(rp))),
      Equal.trans(Bool, R.RunSt.inbody(P.settle(P.specRun(rp))), R.RunSt.inbody(P.settle(G)), True{}, Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.settle(P.specRun(rp)), P.settle(G), h),
        Equal.trans(Bool, R.RunSt.inbody(P.settle(G)), R.RunSt.inbody(G), True{}, ib_settle(G), go_ib(ls, fa, o, SD.rs0(c0, l), {==})))))

# The parts of a good state's WF (in its order).
def wf9(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool,
  +h: {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(a1, a2), a3), a4), a5), a6), a7), a8), a9) == True{} : Bool}) ->
  {a1 == True{} : Bool} & ({a3 == True{} : Bool} & ({a4 == True{} : Bool} & ({a7 == True{} : Bool} & {a8 == True{} : Bool}))):
  +X2 = Bool.and(a1, a2)
  +X3 = Bool.and(X2, a3)
  +X4 = Bool.and(X3, a4)
  +X5 = Bool.and(X4, a5)
  +X6 = Bool.and(X5, a6)
  +X7 = Bool.and(X6, a7)
  +X8 = Bool.and(X7, a8)
  +h8 = BUF.andl(X8, a9, h)
  +h7 = BUF.andl(X7, a8, h8)
  +h6 = BUF.andl(X6, a7, h7)
  +h5 = BUF.andl(X5, a6, h6)
  +h4 = BUF.andl(X4, a5, h5)
  +h3 = BUF.andl(X3, a4, h4)
  +h2 = BUF.andl(X2, a3, h3)
  (BUF.andl(a1, a2, h2), (BUF.andr(X2, a3, h3), (BUF.andr(X3, a4, h4), (BUF.andr(X6, a7, h7), BUF.andr(X7, a8, h8)))))

def idle_mb(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +o2: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  w: {PR.RunInv(rp) == True{} : Bool} & ({P.pd_ok(pd) == True{} : Bool} & ({P.nolf(P.pdtext(pd)) == True{} : Bool} & ({PC.wp_ok(fa, wp) == True{} : Bool} & {S.mb_win(S.MBP{rp}, wp) == True{} : Bool}))),
  +hx: {P.RunP.x(rp) == False{} : Bool},
  t: Trk(fa, o, cs, c0, l, LA, S.StP{o2, S.MBP{rp}, Nil{}, pd, False{}, back, wp, asked, fneed})) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Nil{}, pd, False{}, back, wp, asked, fneed}), k, c0, l)):
  (hinv, w1) = w
  (hpd, w2) = w1
  (hnl, w3) = w2
  (hwp, hmb) = w3
  (+ls, t1) = t
  (e, +s) = t1
  +hi = i_of(fa, o, c0, l, rp, ls, s)
  +hb = {
    %Equal.sym(Bool, PR.RunInv(rp), True{}, hinv) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(_, P.RunP.i(rp)), Bool.not(P.RunP.x(rp))), P.pd_ok(pd)), P.nolf(P.pdtext(pd))), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, P.RunP.i(rp), True{}, hi) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, _), Bool.not(P.RunP.x(rp))), P.pd_ok(pd)), P.nolf(P.pdtext(pd))), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, P.RunP.x(rp), False{}, hx) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), Bool.not(_)), P.pd_ok(pd)), P.nolf(P.pdtext(pd))), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, P.pd_ok(pd), True{}, hpd) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), _), P.nolf(P.pdtext(pd))), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, P.nolf(P.pdtext(pd)), True{}, hnl) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), True{}), _), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, PC.wp_ok(fa, wp), True{}, hwp) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), True{}), True{}), _), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}
    %Equal.sym(Bool, S.mb_win(S.MBP{rp}, wp), True{}, hmb) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), True{}), True{}), True{}), _) == True{} : Bool}
    {==} : {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(PR.RunInv(rp), P.RunP.i(rp)), Bool.not(P.RunP.x(rp))), P.pd_ok(pd)), P.nolf(P.pdtext(pd))), PC.wp_ok(fa, wp)), S.mb_win(S.MBP{rp}, wp)) == True{} : Bool}}
  (LClean{rp, pd, wp}, ({==}, (hb, (ls, (e, s)))))

def idle_done(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +p2: S.StP,
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +hsrc: {S.src_empty(S.StP.src(p2)) == True{} : Bool},
  +hstop: {S.stopped(S.StP.md(p2)) == False{} : Bool},
  t: Trk(fa, o, cs, c0, l, LA, p2)) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, p2), k, c0, l)):
  match p2:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      match md:
        case S.MSP{+s, +qs, +ql, +code}:
          (LDirty{}, ({==}, Unit{}))
        case S.MBP{+rp}:
          match src:
            case Con{+sp, +rest}:
              Empty.absurd(LoopG(fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Con{sp, rest}, pd, eof, back, wp, asked, fneed}), k, c0, l)), N.false_ne_true(hsrc))
            case Nil{}:
              match eof:
                case True{}:
                  Empty.absurd(LoopG(fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Nil{}, pd, True{}, back, wp, asked, fneed}), k, c0, l)), N.true_ne_false(heof))
                case False{}:
                  idle_mb(fa, o, cs, c0, l, LA, k, o2, rp, pd, back, wp, asked, fneed,
                    wf9(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))),
                      Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), E.all_bytes(S.opts_args(o2)), hwf),
                    hstop, t)

# ---------------------------------------------------------------------------
# A read the window does not answer (Want): the next spare window
# ---------------------------------------------------------------------------

def wf_swap(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +b7: Bool, +b8: Bool,
  +h: {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(a1, a2), a3), a4), a5), a6), a7), a8), a9) == True{} : Bool},
  +h7: {b7 == True{} : Bool},
  +h8: {b8 == True{} : Bool}) ->
  {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(a1, a2), a3), a4), a5), a6), b7), b8), a9) == True{} : Bool}:
  +X6 = Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(a1, a2), a3), a4), a5), a6)
  +X7 = Bool.and(X6, a7)
  +X8 = Bool.and(X7, a8)
  +h8x = BUF.andl(X8, a9, h)
  +h9 = BUF.andr(X8, a9, h)
  +h6 = BUF.andl(X6, a7, BUF.andl(X7, a8, h8x))
  %Equal.sym(Bool, X6, True{}, h6) : {Bool.and(Bool.and(Bool.and(_, b7), b8), a9) == True{} : Bool}
  %Equal.sym(Bool, b7, True{}, h7) : {Bool.and(Bool.and(Bool.and(True{}, _), b8), a9) == True{} : Bool}
  %Equal.sym(Bool, b8, True{}, h8) : {Bool.and(Bool.and(Bool.and(True{}, True{}), _), a9) == True{} : Bool}
  %Equal.sym(Bool, a9, True{}, h9) : {Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), _) == True{} : Bool}
  {==}

def mbw(+md: S.MdP, +wp: PC.WP, +h: {S.mb_win.k(wp) == True{} : Bool}) -> {S.mb_win(md, wp) == True{} : Bool}:
  match md:
    case S.MBP{+rp}:
      h
    case S.MSP{+s, +qs, +ql, +code}:
      {==}

def rep_swap(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o2: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat,
  +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) ->
  {S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed}) == S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed}) : R.Report}:
  match md:
    case S.MBP{+rp}:
      {==}
    case S.MSP{+s, +qs, +ql, None{}}:
      {==}
    case S.MSP{+s, +qs, +ql, Some{+cd}}:
      {==}

def trk_swap(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>,
  +o2: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat,
  +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  t: Trk(fa, o, cs, c0, l, LA, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed})) ->
  Trk(fa, o, cs, c0, l, LA, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed}):
  match md:
    case S.MBP{+rp}:
      t
    case S.MSP{+s, +qs, +ql, +code}:
      Unit{}

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

def IH(+g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report) -> Type:
  @p2: S.StP -> @sp2: List<&2, PC.WP> -> Inv(fa, o, cs, c0, l, LA, T, p2) -> {wins_ok(fa, sp2) == True{} : Bool} ->
    LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.TGo{S.mkSt(fa, p2), mkWins(fa, sp2)}, k, c0, l))

def end_r(+g: Nat, r: W.TRes, +k: U32, +c0: String, +l: Nat) -> {W.task.loop(g, W.TEnd{r}, k, c0, l) == r : W.TRes}:
  match g:
    case 0n:
      {==}
    case 1n+h:
      {==}

def swap_go(+g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +p2: S.StP, +wp2: PC.WP, +sp2: List<&2, PC.WP>,
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +hrep: {S.report(fa, cs, "", Nil{}, p2) == T : R.Report},
  +hgd: {S.guard("", Nil{}, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +ho: {S.StP.o(p2) == o : B.Opts},
  t: Trk(fa, o, cs, c0, l, LA, p2),
  +hw: {Bool.and(PC.wp_ok(fa, wp2), S.mb_win.k(wp2)) == True{} : Bool},
  +hsp2: {wins_ok(fa, sp2) == True{} : Bool},
  ih: IH(g, fa, o, cs, c0, l, LA, k, T)) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.TGo{W.swap_win(S.mkSt(fa, p2), PC.mkWin(fa, wp2)), mkWins(fa, sp2)}, k, c0, l)):
  match p2:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      +wf3 = wf_swap(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
        Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o2)),
        PC.wp_ok(fa, wp2), S.mb_win(md, wp2), hwf, BUF.andl(PC.wp_ok(fa, wp2), S.mb_win.k(wp2), hw), mbw(md, wp2, BUF.andr(PC.wp_ok(fa, wp2), S.mb_win.k(wp2), hw)))
      +rep3 = Equal.trans(R.Report, S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed}), S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed}), T,
        rep_swap(fa, cs, o2, md, src, pd, eof, back, wp, wp2, asked, fneed), hrep)
      ih(S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed}, sp2,
        (wf3, (rep3, (hgd, (heof, (ho, trk_swap(fa, o, cs, c0, l, LA, o2, md, src, pd, eof, back, wp, wp2, asked, fneed, t)))))), hsp2)

def hms2(+fa: List<&2, B.Contig>, -st: Q.St, +p: S.StP, +p2: S.StP,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  hms: {MS.md_ms_p(S.StP.md(p)) == True{} : Bool} -> {MS.st_ms(st) == True{} : Bool},
  +h: {MS.md_ms_p(S.StP.md(p)) == True{} : Bool}) ->
  {MS.md_ms_p(S.StP.md(p2)) == True{} : Bool}:
  Equal.trans(Bool, MS.md_ms_p(S.StP.md(p2)), MS.st_ms(S.mkSt(fa, p2)), True{}, Equal.sym(Bool, MS.st_ms(S.mkSt(fa, p2)), MS.md_ms_p(S.StP.md(p2)), MS.st_ms_p(fa, p2)),
    AB.subst(Q.St, z => {MS.st_ms(z) == True{} : Bool}, st, S.mkSt(fa, p2), est, hms(h)))

def want_go(+sp: List<&2, PC.WP>, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  -st: Q.St, +p2: S.StP,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +hrep: {S.report(fa, cs, "", Nil{}, p2) == T : R.Report},
  +hgd: {S.guard("", Nil{}, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +ho: {S.StP.o(p2) == o : B.Opts},
  t: Trk(fa, o, cs, c0, l, LA, p2),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(g, fa, o, cs, c0, l, LA, k, T)) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.task.want(st, mkWins(fa, sp)), k, c0, l)):
  match sp:
    case Nil{}:
      %Equal.sym(W.TRes, W.task.loop(g, W.TEnd{W.TDirty{}}, k, c0, l), W.TDirty{}, end_r(g, W.TDirty{}, k, c0, l)) : LoopG(fa, o, cs, c0, l, LA, k, _)
      (LDirty{}, ({==}, Unit{}))
    case +wp2 <> +sp2:
      +X = Bool.and(PC.wp_ok(fa, wp2), S.mb_win.k(wp2))
      %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) : LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.TGo{W.swap_win(_, PC.mkWin(fa, wp2)), mkWins(fa, sp2)}, k, c0, l))
      swap_go(g, fa, o, cs, c0, l, LA, k, T, p2, wp2, sp2, hwf, hrep, hgd, heof, ho, t, BUF.andl(X, wins_ok(fa, sp2), hsp), BUF.andr(X, wins_ok(fa, sp2), hsp), ih)

# One advance a from p (adv_ok's guarantee hadv), then the rest of the loop.
def step(+g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +p: S.StP, +sp: List<&2, PC.WP>, a: Q.Adv,
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  +heof: {S.StP.eof(p) == False{} : Bool},
  +ho: {S.StP.o(p) == o : B.Opts},
  t: Trk(fa, o, cs, c0, l, LA, p),
  hadv: S.AdvG(fa, T, cs, "", Nil{}, p, a),
  hms: {MS.md_ms_p(S.StP.md(p)) == True{} : Bool} -> {MS.adv_ms(a) == True{} : Bool},
  ih: IH(g, fa, o, cs, c0, l, LA, k, T)) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.task.adv(a, mkWins(fa, sp), k, c0, l), k, c0, l)):
  match a:
    case Q.Went{st}:
      (+p2, h1) = hadv
      (+est, h2) = h1
      (+hwf2, h3) = h2
      (+hrep2, h4) = h3
      (hmeas, h5) = h4
      (hask, h6) = h5
      (+heof2, h7) = h6
      (+hgd2, h8) = h7
      (+ho2, mv) = h8
      t2 = trk_md(S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, h => hms2(fa, st, p, p2, est, hms, h))
      %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) : LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(g, W.TGo{_, mkWins(fa, sp)}, k, c0, l))
      ih(p2, sp, (hwf2, (hrep2, (hgd2, (Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), (Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(p), o, ho2, ho), t2))))), hsp)
    case Q.Want{st, reqs}:
      (+p2, h1) = hadv
      (+est, h2) = h1
      (+hwf2, h3) = h2
      (+hrep2, h4) = h3
      (hrok, h5) = h4
      (hrq, h6) = h5
      (hask, h7) = h6
      (hstop, h8) = h7
      (hmbr, h9) = h8
      (+heof2, h10) = h9
      (+hgd2, h11) = h10
      (+ho2, mv) = h11
      t2 = trk_md(S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, h => hms2(fa, st, p, p2, est, hms, h))
      want_go(sp, g, fa, o, cs, c0, l, LA, k, T, st, p2, est, hwf2, hrep2, hgd2,
        Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(p), o, ho2, ho), t2, hsp, ih)
    case Q.Idle{st}:
      (+p2, h1) = hadv
      (+est, h2) = h1
      (+hwf2, h3) = h2
      (+hrep2, h4) = h3
      (+hsrc, h5) = h4
      (hask, h6) = h5
      (+heof2, h7) = h6
      (+hstop, h8) = h7
      (+hgd2, h9) = h8
      (+ho2, mv) = h9
      t2 = trk_md(S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, h => hms2(fa, st, p, p2, est, hms, h))
      %Equal.sym(W.TRes, W.task.loop(g, W.TEnd{W.task.done(st, k, c0, l)}, k, c0, l), W.task.done(st, k, c0, l), end_r(g, W.task.done(st, k, c0, l), k, c0, l)) :
        LoopG(fa, o, cs, c0, l, LA, k, _)
      %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) : LoopG(fa, o, cs, c0, l, LA, k, W.task.done(_, k, c0, l))
      idle_done(fa, o, cs, c0, l, LA, k, p2, hwf2, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), hsrc, hstop, t2)
    case Q.Ended{st}:
      %Equal.sym(W.TRes, W.task.loop(g, W.TEnd{W.TDirty{}}, k, c0, l), W.TDirty{}, end_r(g, W.TDirty{}, k, c0, l)) : LoopG(fa, o, cs, c0, l, LA, k, _)
      (LDirty{}, ({==}, Unit{}))
    case Q.Yield{st}:
      %Equal.sym(W.TRes, W.task.loop(g, W.TEnd{W.TDirty{}}, k, c0, l), W.TDirty{}, end_r(g, W.TDirty{}, k, c0, l)) : LoopG(fa, o, cs, c0, l, LA, k, _)
      (LDirty{}, ({==}, Unit{}))

# The task's loop from a good state: its result is dirty, or clean with the
# lines it handled.
def loop_ok(+f: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +p: S.StP, +sp: List<&2, PC.WP>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  hinv: Inv(fa, o, cs, c0, l, LA, T, p),
  +hsp: {wins_ok(fa, sp) == True{} : Bool}) ->
  LoopG(fa, o, cs, c0, l, LA, k, W.task.loop(f, W.TGo{S.mkSt(fa, p), mkWins(fa, sp)}, k, c0, l)):
  match f:
    case 0n:
      (LDirty{}, ({==}, Unit{}))
    case 1n+g:
      (+hwf, i1) = hinv
      (+hrep, i2) = i1
      (+hgd, i3) = i2
      (+heof, i4) = i3
      (+ho, t) = i4
      step(g, fa, o, cs, c0, l, LA, k, T, p, sp, Q.advance(S.mkSt(fa, p)), hsp, heof, ho, t,
        SIM.adv_ok(fa, T, cs, "", Nil{}, p, hb, hwf, hrep, hgd),
        h => MS.ms_stays(fa, p, h),
        p2 => sp2 => j2 => w2 => loop_ok(g, fa, o, cs, c0, l, LA, k, T, p2, sp2, hb, j2, w2))
