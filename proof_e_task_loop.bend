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
import ./proof_b_adv_wf.bend as AW
import ./proof_e_task_piece.bend as PI
import ./proof_e_task_tail.bend as TL
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area D (task): a task's loop (norm_par.bend's task.loop), run
# with adv_ok from a good state. Invariant: Q's state is a good picture p
# standing for the report T, outside the end of the file, with the batch's
# options; while in the byte mode, the lines LA still to come at the start
# are the lines ls it handled followed by the lines still to come at p, and
# its run settles as the spec's run of ls from the phantom state. The spare
# windows are good pictures.
#
# Phase F: the task runs on its piece C.BT(len, tr) itself (no copy) and
# hands it back with its result. The piece is Q's only source, from some at
# on (while its text from at holds an LF, Q keeps it: S.Kept), or held by the
# task, after Q's source became a copy of the piece's bytes from at
# (proof_e_task_tail.bend).

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

def Trk.md(+dfs: B.Defs, +m: S.MdP, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP) -> Type:
  match m:
    case S.MBP{+rp}:
      &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(S.intext(p, cs))) : List<&2, B.Line>}
        & ({S.DEFS(p, cs) == dfs : B.Defs}
        & {P.settle(S.RG(S.recs(S.StP.src(p)), fa, dfs, o, P.specRun(rp))) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}))
    case S.MSP{s, qs, ql, code}:
      Unit

def Trk(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP) -> Type:
  Trk.md(dfs, S.StP.md(p), fa, o, cs, c0, l, LA, p)

def Inv(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +T: R.Report, +p: S.StP) -> Type:
  {S.WF(fa, p) == True{} : Bool} & ({S.report(fa, cs, "", Nil{}, p) == T : R.Report} & ({S.guard("", Nil{}, p) == True{} : Bool}
    & ({S.StP.eof(p) == False{} : Bool} & ({S.StP.o(p) == o : B.Opts} & Trk(dfs, fa, o, cs, c0, l, LA, p)))))

# A task's result, pictured: dirty, clean, or stopped against the phantom
# (to run again from l2, with the window wp and the spare ones sp).
type LR is Data:
  LDirty{}
  LClean{rp: P.RunP, pd: P.PdP, wp: PC.WP}
  LAgain{l2: Nat, wp: PC.WP, sp: List<&2, PC.WP>}

def mkLR(+fa: List<&2, B.Contig>, +k: U32, +c0: String, +l: Nat, +x: LR) -> W.TRes:
  match x:
    case LDirty{}:
      W.TDirty{}
    case LClean{+rp, +pd, +wp}:
      W.TClean{W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}}
    case LAgain{+l2, +wp, +sp}:
      W.TAgain{l2, PC.mkWin(fa, wp), mkWins(fa, sp)}

# proof_e_task.bend's TcOK, with LA for the lines of the piece after k and
# the text after it.
def LRok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +x: LR) -> Type:
  match x:
    case LDirty{}:
      Unit
    case LClean{+rp, +pd, +wp}:
      {PR.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool}
        & (&ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pd), String.concat(cs)))) : List<&2, B.Line>}
          & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}))
    case LAgain{l2, +wp, +sp}:
      {wins_ok(fa, wp <> sp) == True{} : Bool}

# A task's result, pictured (the piece aside).
def ResG(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, -r: W.TRes) -> Type:
  &x: LR -> ({r == mkLR(fa, k, c0, l, x) : W.TRes} & LRok(dfs, fa, o, cs, c0, l, LA, x))

# What the loop gives: the piece and the result.
def LoopG(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +len: U32, +tr: AT.Tree<U32>, -r: W.TOut) -> Type:
  &x: LR -> ({r == W.TOut{C.BT(len, tr), mkLR(fa, k, c0, l, x)} : W.TOut} & LRok(dfs, fa, o, cs, c0, l, LA, x))

# Where the piece is (norm.bend's Ph): Q's input, or held by the task.
type PhP is Data:
  PInP{}
  PHeldP{}

def mkPh(+len: U32, +tr: AT.Tree<U32>, +x: PhP) -> W.Ph:
  match x:
    case PInP{}:
      W.PIn{}
    case PHeldP{}:
      W.PHeld{C.BT(len, tr)}

# The piece as Q's input: its only source, from some at on (Hold0); and, at
# the loop's states, its text from at holds an LF (Hold).
def Hold0(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP, +p: S.StP) -> Type:
  match x:
    case PInP{}:
      &at: U32 -> {S.plain(S.StP.src(p)) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>}
    case PHeldP{}:
      Unit

# The first source holds records (of a line split on its bytes, -m).
def front_rec(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Con{P.SPP{len, t, d, at}, r}:
      True{}
    case Con{P.SRP{l}, r}:
      True{}
    case _:
      False{}

def Hold(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP, +p: S.StP) -> Type:
  match x:
    case PInP{}:
      &at: U32 -> ({S.plain(S.StP.src(p)) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>}
        & ({front_rec(S.StP.src(p)) == False{} : Bool} -> {P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool}))
    case PHeldP{}:
      Unit

def isMB(+m: S.MdP) -> Bool:
  match m:
    case S.MBP{rp}:
      True{}
    case S.MSP{s, qs, ql, code}:
      False{}

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

def trk_mb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>,
  +rp: P.RunP, +rp2: P.RunP, +X1: String, +X2: String,
  t1: &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(X1)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}),
  t2: &ls: List<&2, B.Line> -> ({B.Text.lines(X1) == List.append(&2, B.Line, ls, B.Text.lines(X2)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, dfs, o, P.specRun(rp))) : R.RunSt})) ->
  &ls: List<&2, B.Line> -> ({LA == List.append(&2, B.Line, ls, B.Text.lines(X2)) : List<&2, B.Line>}
        & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}):
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
    RN.go_step(dfs, ls1, ls2, fa, o, SD.rs0(c0, l), P.specRun(rp), P.specRun(rp2), s1, s2)))

# The invariant's lines and run after one advance from p to p2 (String mode
# stays String mode).
def trk_md(+dfs: B.Defs, +m: S.MdP, +m2: S.MdP, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +p: S.StP, +p2: S.StP,
  t: Trk.md(dfs, m, fa, o, cs, c0, l, LA, p),
  mv: S.Moved.md(m, m2, fa, cs, p, p2),
  +ho: {S.StP.o(p) == o : B.Opts},
  hms: {MS.md_ms_p(m) == True{} : Bool} -> {MS.md_ms_p(m2) == True{} : Bool}) ->
  Trk.md(dfs, m2, fa, o, cs, c0, l, LA, p2):
  match m m2:
    case S.MBP{+rp} S.MBP{+rp2}:
      (+ls1, a1) = t
      (e1, a2) = a1
      (+d1, s1) = a2
      (+ls2, b1) = mv
      (e2, b2) = b1
      (s2, d2) = b2
      +R1 = S.RG(S.recs(S.StP.src(p)), fa, dfs, o, P.specRun(rp))
      +R2 = S.RG(S.recs(S.StP.src(p2)), fa, dfs, o, P.specRun(rp2))
      +s2b = {%d1 :
          {P.settle(S.RG(S.recs(S.StP.src(p2)), fa, _, o, P.specRun(rp2))) == P.settle(L.run.go(ls2, fa, _, o, S.RG(S.recs(S.StP.src(p)), fa, _, o, P.specRun(rp)))) : R.RunSt};
        %ho :
          {P.settle(S.RG(S.recs(S.StP.src(p2)), fa, S.DEFS(p, cs), _, P.specRun(rp2))) == P.settle(L.run.go(ls2, fa, S.DEFS(p, cs), _, S.RG(S.recs(S.StP.src(p)), fa, S.DEFS(p, cs), _, P.specRun(rp)))) : R.RunSt};
        s2 : {P.settle(R2) == P.settle(L.run.go(ls2, fa, dfs, o, R1)) : R.RunSt}}
      +L2 = B.Text.lines(S.intext(p2, cs))
      (List.append(&2, B.Line, ls1, ls2),
        (Equal.trans(List<&2, B.Line>, LA, List.append(&2, B.Line, ls1, B.Text.lines(S.intext(p, cs))), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), e1,
          Equal.trans(List<&2, B.Line>, List.append(&2, B.Line, ls1, B.Text.lines(S.intext(p, cs))), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2),
            Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => List.append(&2, B.Line, ls1, z), B.Text.lines(S.intext(p, cs)), List.append(&2, B.Line, ls2, L2), e2),
            Equal.sym(List<&2, B.Line>, List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), app_assoc(ls1, ls2, L2)))),
        (Equal.trans(B.Defs, S.DEFS(p2, cs), S.DEFS(p, cs), dfs, d2, d1),
          RN.go_step(dfs, ls1, ls2, fa, o, SD.rs0(c0, l), R1, R2, s1, s2b))))
    case S.MBP{+rp} S.MSP{+s, +qs, +ql, +code}:
      Unit{}
    case S.MSP{+s, +qs, +ql, +code} S.MBP{+rp2}:
      Empty.absurd(Trk.md(dfs, S.MBP{rp2}, fa, o, cs, c0, l, LA, p2), N.false_ne_true(hms({==})))
    case S.MSP{+s, +qs, +ql, +code} S.MSP{+s2, +qs2, +ql2, +code2}:
      Unit{}


# ---------------------------------------------------------------------------
# The end of a task (Idle)
# ---------------------------------------------------------------------------

# Once in the body, the run stays there.
def go_ib(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt,
  +hi: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {R.RunSt.inbody(L.run.go(ls, fa, dfs, o, st)) == True{} : Bool}:
  match ls:
    case Nil{}:
      hi
    case +x <> +t:
      go_ib(dfs, t, fa, o, L.line_step(fa, dfs, o, st, x), MSX.ib_step(dfs, fa, o, st, x, hi))

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
def i_of(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +rp: P.RunP, +ls: List<&2, B.Line>,
  +h: {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}) ->
  {P.RunP.i(rp) == True{} : Bool}:
  +G = L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))
  Equal.trans(Bool, P.RunP.i(rp), R.RunSt.inbody(P.specRun(rp)), True{}, i_spec(rp),
    Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), R.RunSt.inbody(P.settle(P.specRun(rp))), True{}, Equal.sym(Bool, R.RunSt.inbody(P.settle(P.specRun(rp))), R.RunSt.inbody(P.specRun(rp)), ib_settle(P.specRun(rp))),
      Equal.trans(Bool, R.RunSt.inbody(P.settle(P.specRun(rp))), R.RunSt.inbody(P.settle(G)), True{}, Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.settle(P.specRun(rp)), P.settle(G), h),
        Equal.trans(Bool, R.RunSt.inbody(P.settle(G)), R.RunSt.inbody(G), True{}, ib_settle(G), go_ib(dfs, ls, fa, o, SD.rs0(c0, l), {==})))))

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

def idle_mb2(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +o2: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  w: {PR.RunInv(rp) == True{} : Bool} & ({P.pd_ok(pd) == True{} : Bool} & ({P.nolf(P.pdtext(pd)) == True{} : Bool} & ({PC.wp_ok(fa, wp) == True{} : Bool} & {S.mb_win(S.MBP{rp}, wp) == True{} : Bool}))),
  +hx: {P.RunP.x(rp) == False{} : Bool},
  t: Trk(dfs, fa, o, cs, c0, l, LA, S.StP{o2, S.MBP{rp}, Nil{}, pd, False{}, back, wp, asked, fneed, dfs2})) ->
  ResG(dfs, fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Nil{}, pd, False{}, back, wp, asked, fneed, dfs2}), k, c0, l)):
  (hinv, w1) = w
  (hpd, w2) = w1
  (hnl, w3) = w2
  (hwp, hmb) = w3
  (+ls, t1) = t
  (e, t2) = t1
  (dd, s0) = t2
  +s = {s0 : {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}}
  +hi = i_of(dfs, fa, o, c0, l, rp, ls, s)
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

def idle_done(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +p2: S.StP,
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +hsrc: {S.src_empty(S.StP.src(p2)) == True{} : Bool},
  +hstop: {S.stopped(S.StP.md(p2)) == False{} : Bool},
  t: Trk(dfs, fa, o, cs, c0, l, LA, p2)) ->
  ResG(dfs, fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, p2), k, c0, l)):
  match p2:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs2}:
      match md:
        case S.MSP{+s, +qs, +ql, +code}:
          (LDirty{}, ({==}, Unit{}))
        case S.MBP{+rp}:
          match src:
            case Con{+sp, +rest}:
              Empty.absurd(ResG(dfs, fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Con{sp, rest}, pd, eof, back, wp, asked, fneed, dfs2}), k, c0, l)), N.false_ne_true(hsrc))
            case Nil{}:
              match eof:
                case True{}:
                  Empty.absurd(ResG(dfs, fa, o, cs, c0, l, LA, k, W.task.done(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Nil{}, pd, True{}, back, wp, asked, fneed, dfs2}), k, c0, l)), N.true_ne_false(heof))
                case False{}:
                  idle_mb2(dfs, dfs2, fa, o, cs, c0, l, LA, k, o2, rp, pd, back, wp, asked, fneed,
                    wf9(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))),
                      Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o2)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{})), hwf),
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

def rep_swap(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o2: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat,
  +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) ->
  {S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed, dfs2}) == S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed, dfs2}) : R.Report}:
  match md:
    case S.MBP{+rp}:
      {==}
    case S.MSP{+s, +qs, +ql, None{}}:
      {==}
    case S.MSP{+s, +qs, +ql, Some{+cd}}:
      {==}

def trk_swap(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>,
  +o2: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat,
  +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  t: Trk(dfs, fa, o, cs, c0, l, LA, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed, dfs2})) ->
  Trk(dfs, fa, o, cs, c0, l, LA, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed, dfs2}):
  match md:
    case S.MBP{+rp}:
      t
    case S.MSP{+s, +qs, +ql, +code}:
      Unit{}

# ---------------------------------------------------------------------------
# The piece: back from Q's input, kept by Q, its end copied
# ---------------------------------------------------------------------------

def end_r(+g: Nat, -r: W.TOut, +el: U32, +len: U32, +k: U32, +c0: String, +l: Nat) -> {W.task.loop(g, W.TEnd{r}, el, len, k, c0, l) == r : W.TOut}:
  match g:
    case 0n:
      {==}
    case 1n+h:
      {==}

# The piece is Q's input: the task takes it back.
# The task takes its piece back past the records in front (norm.bend's
# src_b): what it finds depends only on the plain sources.
def srcb_plain(+sps: List<&2, P.SrcP>) -> {W.src_b(P.mkSrcs(sps)) == W.src_b(P.mkSrcs(S.plain(sps))) : D.Bytes}:
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      {==}
    case Con{P.SLP{+q}, +r}:
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      srcb_plain(r)
    case Con{P.SRP{+l}, +r}:
      srcb_plain(r)

# A list's head and tail (for equations between lists).
def hd(+sps: List<&2, P.SrcP>) -> P.SrcP:
  match sps:
    case Con{+h, t}:
      h
    case Nil{}:
      P.SLP{""}

def tl(+sps: List<&2, P.SrcP>) -> List<&2, P.SrcP>:
  match sps:
    case Con{h, +t}:
      t
    case Nil{}:
      Nil{}

def is_sb(+sp: P.SrcP) -> Bool:
  match sp:
    case P.SBP{len, t, d, at}:
      True{}
    case _:
      False{}

def with_at(+sp: P.SrcP, +x: U32) -> P.SrcP:
  match sp:
    case P.SBP{+len, +t, +d, at}:
      P.SBP{len, t, d, x}
    case _:
      sp

def not_sb(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +sp: P.SrcP, +r: List<&2, P.SrcP>, +r2: List<&2, P.SrcP>, +hn: {is_sb(sp) == False{} : Bool}, +h: {Con{sp, r} == Con{P.SBP{len, tr, d, at}, r2} : List<&2, P.SrcP>}) -> Empty:
  N.false_ne_true(Equal.trans(Bool, False{}, is_sb(sp), True{}, Equal.sym(Bool, is_sb(sp), False{}, hn),
    Equal.cong(List<&2, P.SrcP>, Bool, z => is_sb(hd(z)), Con{sp, r}, Con{P.SBP{len, tr, d, at}, r2}, h)))

def back_in(+fa: List<&2, B.Contig>, +len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +p: S.StP,
  +h: {S.plain(S.StP.src(p)) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>}) ->
  {W.st_b(S.mkSt(fa, p)) == C.BT(len, tr) : D.Bytes}:
  match p:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      %Equal.sym(D.Bytes, W.src_b(P.mkSrcs(src)), W.src_b(P.mkSrcs(S.plain(src))), srcb_plain(src)) : {_ == C.BT(len, tr) : D.Bytes}
      %Equal.sym(List<&2, P.SrcP>, S.plain(src), [P.SBP{len, tr, d, at}], h) : {W.src_b(P.mkSrcs(_)) == C.BT(len, tr) : D.Bytes}
      {==}

def back_x(+fa: List<&2, B.Contig>, +len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP, +p: S.StP,
  h: Hold0(len, tr, d, x, p)) ->
  {W.task.back(S.mkSt(fa, p), mkPh(len, tr, x)) == C.BT(len, tr) : D.Bytes}:
  match x:
    case PInP{}:
      (+at, hs) = h
      back_in(fa, len, tr, d, at, p, hs)
    case PHeldP{}:
      {==}

def hold0_of(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP, +p: S.StP,
  h: Hold(len, tr, d, x, p)) -> Hold0(len, tr, d, x, p):
  match x:
    case PInP{}:
      (+at, h1) = h
      (hs, hn) = h1
      (at, hs)
    case PHeldP{}:
      Unit{}

# A dirty end, with the piece.
def dirty_g(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +el: U32, -st: Q.St, -ph: W.Ph,
  +hb: {W.task.back(st, ph) == C.BT(len, tr) : D.Bytes}) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.dirty(st, ph), el, len, k, c0, l)):
  %Equal.sym(W.TOut, W.task.loop(g, W.TEnd{W.TOut{W.task.back(st, ph), W.TDirty{}}}, el, len, k, c0, l), W.TOut{W.task.back(st, ph), W.TDirty{}}, end_r(g, W.TOut{W.task.back(st, ph), W.TDirty{}}, el, len, k, c0, l)) :
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, _)
  (LDirty{}, (Equal.cong(D.Bytes, W.TOut, z => W.TOut{z, W.TDirty{}}, W.task.back(st, ph), C.BT(len, tr), hb), Unit{}))

def dirty_st(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32, -st: Q.St, +x: PhP, +p2: S.StP,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  h: Hold0(len, tr, d, x, p2)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.dirty(st, mkPh(len, tr, x)), el, len, k, c0, l)):
  dirty_g(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, el, st, mkPh(len, tr, x),
    Equal.trans(D.Bytes, W.task.back(st, mkPh(len, tr, x)), W.task.back(S.mkSt(fa, p2), mkPh(len, tr, x)), C.BT(len, tr),
      Equal.cong(Q.St, D.Bytes, z => W.task.back(z, mkPh(len, tr, x)), st, S.mkSt(fa, p2), est), back_x(fa, len, tr, d, x, p2, h)))

# Q kept the piece (S.Kept): from the byte mode, while its text from at holds
# an LF.
def kept_sb2(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +l2: U32, +t2: AT.Tree<U32>, +d2: Nat, +a2: U32, +rest: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>,
  +eh: {P.SBP{l2, t2, d2, a2} == P.SBP{len, tr, d, at} : P.SrcP},
  +et: {rest == Nil{} : List<&2, P.SrcP>},
  r: &at2: U32 -> {S.plain(s2) == Con{P.SBP{l2, t2, d2, at2}, rest} : List<&2, P.SrcP>}) ->
  &at2: U32 -> {S.plain(s2) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}:
  (+at2, e) = r
  (at2,
    Equal.trans(List<&2, P.SrcP>, S.plain(s2), Con{with_at(P.SBP{l2, t2, d2, a2}, at2), rest}, [P.SBP{len, tr, d, at2}], e,
      Equal.trans(List<&2, P.SrcP>, Con{with_at(P.SBP{l2, t2, d2, a2}, at2), rest}, Con{with_at(P.SBP{len, tr, d, at}, at2), rest}, [P.SBP{len, tr, d, at2}],
        Equal.cong(P.SrcP, List<&2, P.SrcP>, z => Con{with_at(z, at2), rest}, P.SBP{l2, t2, d2, a2}, P.SBP{len, tr, d, at}, eh),
        Equal.cong(List<&2, P.SrcP>, List<&2, P.SrcP>, z => Con{P.SBP{len, tr, d, at2}, z}, rest, Nil{}, et))))

def kept_sb(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +l2: U32, +t2: AT.Tree<U32>, +d2: Nat, +a2: U32, +rest: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>,
  +hs: {Con{P.SBP{l2, t2, d2, a2}, rest} == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  +hn: {P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool},
  kp: S.Kept.sp(P.SBP{l2, t2, d2, a2}, rest, s2)) ->
  &at2: U32 -> {S.plain(s2) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}:
  +eh = Equal.cong(List<&2, P.SrcP>, P.SrcP, z => hd(z), Con{P.SBP{l2, t2, d2, a2}, rest}, [P.SBP{len, tr, d, at}], hs)
  +et = Equal.cong(List<&2, P.SrcP>, List<&2, P.SrcP>, z => tl(z), Con{P.SBP{l2, t2, d2, a2}, rest}, [P.SBP{len, tr, d, at}], hs)
  +hn2 = AB.subst(P.SrcP, z => {P.nolf(P.srctext(z)) == False{} : Bool}, P.SBP{len, tr, d, at}, P.SBP{l2, t2, d2, a2}, Equal.sym(P.SrcP, P.SBP{l2, t2, d2, a2}, P.SBP{len, tr, d, at}, eh), hn)
  kept_sb2(len, tr, d, at, l2, t2, d2, a2, rest, s2, eh, et, kp(hn2))


def kept_src(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +src: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>,
  +hs: {S.plain(src) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  hn: {front_rec(src) == False{} : Bool} -> {P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool},
  kp: S.Kept.s(src, s2)) ->
  &at2: U32 -> {S.plain(s2) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}:
  match src:
    case Nil{}:
      Empty.absurd(&at2: U32 -> {S.plain(s2) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>},
        N.true_ne_false(Equal.cong(List<&2, P.SrcP>, Bool, z => List.is_empty(&2, P.SrcP, z), Nil{}, [P.SBP{len, tr, d, at}], hs)))
    case Con{P.SBP{+l2, +t2, +d2, +a2}, +rest}:
      kept_sb(len, tr, d, at, l2, t2, d2, a2, rest, s2, hs, hn({==}), kp)
    case Con{P.SLP{+q}, +rest}:
      Empty.absurd(&at2: U32 -> {S.plain(s2) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}, not_sb(len, tr, d, at, P.SLP{q}, rest, Nil{}, {==}, hs))
    case Con{P.SPP{+l2, +t2, +d2, +a2}, +rest}:
      (at, Equal.trans(List<&2, P.SrcP>, S.plain(s2), S.plain(rest), [P.SBP{len, tr, d, at}], kp, hs))
    case Con{P.SRP{+l}, +rest}:
      (at, Equal.trans(List<&2, P.SrcP>, S.plain(s2), S.plain(rest), [P.SBP{len, tr, d, at}], kp, hs))

def kept_in(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +p: S.StP, +p2: S.StP,
  +hmb: {isMB(S.StP.md(p)) == True{} : Bool},
  +hs: {S.plain(S.StP.src(p)) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  hn: {front_rec(S.StP.src(p)) == False{} : Bool} -> {P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool},
  kp: S.Kept(p, p2)) ->
  &at2: U32 -> {S.plain(S.StP.src(p2)) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}:
  match p:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      match md:
        case S.MBP{+rp}:
          kept_src(len, tr, d, at, src, S.StP.src(p2), hs, hn, kp)
        case S.MSP{+s, +qs, +ql, +code}:
          Empty.absurd(&at2: U32 -> {S.plain(S.StP.src(p2)) == [P.SBP{len, tr, d, at2}] : List<&2, P.SrcP>}, N.false_ne_true(hmb))


def kept_hold(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP, +p: S.StP, +p2: S.StP,
  +hmb: {isMB(S.StP.md(p)) == True{} : Bool},
  h: Hold(len, tr, d, x, p),
  kp: S.Kept(p, p2)) -> Hold0(len, tr, d, x, p2):
  match x:
    case PHeldP{}:
      Unit{}
    case PInP{}:
      (+at, h1) = h
      (hs, hn) = h1
      kept_in(len, tr, d, at, p, p2, hmb, hs, hn, kp)

# A state whose one source (a buffer) is replaced by one with the same text.
def intext_sw(+dfs: B.Defs, +dfs2: B.Defs, +cs: List<&2, String>, +o2: B.Opts, +md: S.MdP, +l1: U32, +t1: AT.Tree<U32>, +d1: Nat, +a1: U32, +l2: U32, +t2: AT.Tree<U32>, +d2: Nat, +a2: U32,
  +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ht: {P.srctext(P.SBP{l2, t2, d2, a2}) == P.srctext(P.SBP{l1, t1, d1, a1}) : String}) ->
  {S.intext(S.StP{o2, md, [P.SBP{l2, t2, d2, a2}], pd, eof, back, wp, asked, fneed, dfs2}, cs) == S.intext(S.StP{o2, md, [P.SBP{l1, t1, d1, a1}], pd, eof, back, wp, asked, fneed, dfs2}, cs) : String}:
  %Equal.sym(String, P.srctext(P.SBP{l2, t2, d2, a2}), P.srctext(P.SBP{l1, t1, d1, a1}), ht) :
    {String.append(String.append(_, ""), String.append(P.pdtext(pd), S.concat_if(eof, cs))) == S.intext(S.StP{o2, md, [P.SBP{l1, t1, d1, a1}], pd, eof, back, wp, asked, fneed, dfs2}, cs) : String}
  {==}

def inv_sw(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +T: R.Report,
  +o2: B.Opts, +rp: P.RunP, +l1: U32, +t1: AT.Tree<U32>, +d1: Nat, +a1: U32, +l2: U32, +t2: AT.Tree<U32>, +d2: Nat, +a2: U32,
  +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +ht: {P.srctext(P.SBP{l2, t2, d2, a2}) == P.srctext(P.SBP{l1, t1, d1, a1}) : String},
  +hok2: {P.src_ok(P.SBP{l2, t2, d2, a2}) == True{} : Bool},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{l1, t1, d1, a1}], pd, eof, back, wp, asked, fneed, dfs2})) ->
  Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{l2, t2, d2, a2}], pd, eof, back, wp, asked, fneed, dfs2}):
  (+hwf, i1) = hinv
  (+hrep, i2) = i1
  (+hgd, i3) = i2
  (+heof, i4) = i3
  (+ho, t) = i4
  (+ls, t1x) = t
  (e, t2x) = t1x
  (+dd, st) = t2x
  +s1 = {P.SBP{l1, t1, d1, a1} : P.SrcP}
  +s2 = {P.SBP{l2, t2, d2, a2} : P.SrcP}
  +p1 = {S.StP{o2, S.MBP{rp}, [s1], pd, eof, back, wp, asked, fneed, dfs2} : S.StP}
  +p2 = {S.StP{o2, S.MBP{rp}, [s2], pd, eof, back, wp, asked, fneed, dfs2} : S.StP}
  +m0 = S.md_ok(S.MBP{rp})
  +hi = intext_sw(dfs, dfs2, cs, o2, S.MBP{rp}, l1, t1, d1, a1, l2, t2, d2, a2, pd, eof, back, wp, asked, fneed, ht)
  +h5 = {%Equal.sym(String, P.srctext(s2), P.srctext(s1), ht) :
      {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(_, "")))) == True{} : Bool};
    AW.c9_5(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf) : {AW.W5(fa, p2) == True{} : Bool}}
  +hwf2 = AW.c9_mk(m0, AW.W1(fa, p2), AW.W2(fa, p2), AW.W3(fa, p2), AW.W4(fa, p2), AW.W5(fa, p2), AW.W6(fa, p2), AW.W7(fa, p2), AW.W8(fa, p2),
    AW.c9_0(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf), hok2,
    AW.c9_2(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf),
    AW.c9_3(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf),
    AW.c9_4(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf), h5,
    AW.c9_6(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf),
    AW.c9_7(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf),
    AW.c9_8(m0, AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf))
  +er = {%Equal.sym(String, S.intext(p2, cs), S.intext(p1, cs), hi) :
      {R.finish(L.run.go(B.Text.lines(_), fa, L.defs.go(B.Text.lines(_), R.RunSt.inbody(P.specRun(rp)), dfs2), o2, S.pre("", Nil{}, P.specRun(rp)))) == S.report(fa, cs, "", Nil{}, p1) : R.Report};
    {==} : {S.report(fa, cs, "", Nil{}, p2) == S.report(fa, cs, "", Nil{}, p1) : R.Report}}
  +e2 = Equal.trans(List<&2, B.Line>, LA, List.append(&2, B.Line, ls, B.Text.lines(S.intext(p1, cs))), List.append(&2, B.Line, ls, B.Text.lines(S.intext(p2, cs))), e,
    Equal.cong(String, List<&2, B.Line>, z => List.append(&2, B.Line, ls, B.Text.lines(z)), S.intext(p1, cs), S.intext(p2, cs), Equal.sym(String, S.intext(p2, cs), S.intext(p1, cs), hi)))
  +dd2 = Equal.trans(B.Defs, S.DEFS(p2, cs), S.DEFS(p1, cs), dfs, AW.defs_keep(p1, p2, cs, hi, {==}, {==}), dd)
  (hwf2, (Equal.trans(R.Report, S.report(fa, cs, "", Nil{}, p2), S.report(fa, cs, "", Nil{}, p1), T, er, hrep), (hgd, (heof, (ho, (ls, (e2, (dd2, st))))))))


def not_f(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, N.true_ne_false(h))

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

def IH(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32) -> Type:
  @p2: S.StP -> @sp2: List<&2, PC.WP> -> @x: PhP -> Inv(dfs, fa, o, cs, c0, l, LA, T, p2) -> {isMB(S.StP.md(p2)) == True{} : Bool} -> Hold(len, tr, d, x, p2) -> {wins_ok(fa, sp2) == True{} : Bool} ->
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.TGo{S.mkSt(fa, p2), mkWins(fa, sp2), mkPh(len, tr, x)}, el, len, k, c0, l))

# The swap test said: copy the piece's bytes from at; the task holds it.
def tail_k(+dfs: B.Defs, +dfs2: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  +hle: {U32.is_le(at, len) == True{} : Bool},
  pb: &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(0, G.tnew(TL.TE(len, at), 0), len, tr, at, (len - at : U32), l2, t2),
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.if(True{}, o2, Q.MB{P.mkRun(rp)}, C.BT(len, tr), at, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l)):
  (+L2, q1) = pb
  (+T2, q2) = q1
  (+epb, q3) = q2
  (+ok2, q4) = q3
  (+v2, eln) = q4
  +E0 = TL.TE(len, at)
  +s2 = {P.SBP{L2, T2, RD.tdepth(T2), 0} : P.SrcP}
  +hok2 = {%Equal.sym(Bool, D.ok(C.BT(L2, T2), RD.tdepth(T2)), True{}, ok2) : {Bool.and(_, U32.is_le(0, L2)) == True{} : Bool};
    %Equal.sym(Bool, U32.is_le(0, L2), True{}, PI.u_le0(L2)) : {Bool.and(True{}, _) == True{} : Bool};
    {==} : {P.src_ok(s2) == True{} : Bool}}
  +ht = TL.tail_text(len, tr, d, at, L2, T2, RD.tdepth(T2), G.tnew(E0, 0), hok, hle, v2)
  %Equal.sym(D.Bytes, BY.empty(E0), C.BT(0, G.tnew(E0, 0)), G.empty_eq(E0)) :
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.put(o2, Q.MB{P.mkRun(rp)}, NR.put_bytes(_, C.BT(len, tr), at, (len - at : U32)), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l))
  %Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(0, G.tnew(E0, 0)), C.BT(len, tr), at, (len - at : U32)), (C.BT(L2, T2), C.BT(len, tr)), epb) :
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.put(o2, Q.MB{P.mkRun(rp)}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l))
  ih(S.StP{o2, S.MBP{rp}, [s2], pd, eof, back, wp, asked, fneed, dfs2}, sp, PHeldP{},
    inv_sw(dfs, dfs2, fa, o, cs, c0, l, LA, T, o2, rp, len, tr, d, at, L2, T2, RD.tdepth(T2), 0, pd, eof, back, wp, asked, fneed, ht, hok2, hinv), {==}, Unit{}, hsp)

def tail_ok(+dfs: B.Defs, +dfs2: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.if(True{}, o2, Q.MB{P.mkRun(rp)}, C.BT(len, tr), at, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l)):
  (+hwf, i1) = hinv
  +p1 = {S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2} : S.StP}
  +h1 = AW.c9_1(S.md_ok(S.MBP{rp}), AW.W1(fa, p1), AW.W2(fa, p1), AW.W3(fa, p1), AW.W4(fa, p1), AW.W5(fa, p1), AW.W6(fa, p1), AW.W7(fa, p1), AW.W8(fa, p1), hwf)
  +hle = AW.and_r(D.ok(C.BT(len, tr), d), U32.is_le(at, len), h1)
  tail_k(dfs, dfs2, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, o2, rp, at, pd, eof, back, wp, asked, fneed, sp, hle,
    TL.tail_put(len, tr, d, at, hok, hle, hL), (hwf, i1), hsp, ih)

# The swap test on the byte at el (el < len).
def if_ok(+dfs: B.Defs, +dfs2: B.Defs, +c: Bool, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  +hlt: {U32.is_lt(el, len) == True{} : Bool},
  +hc: {Bool.not(Bool.and(U32.is_le(at, el), U32.is_eq(C.AT(len, tr, el), 10))) == c : Bool},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.if(c, o2, Q.MB{P.mkRun(rp)}, C.BT(len, tr), at, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l)):
  match c:
    case True{}:
      tail_ok(dfs, dfs2, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, o2, rp, at, pd, eof, back, wp, asked, fneed, sp, hinv, hsp, ih)
    case False{}:
      +A = U32.is_le(at, el)
      +Bx = U32.is_eq(C.AT(len, tr, el), 10)
      +hab = not_f(Bool.and(A, Bx), hc)
      ih(S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2}, sp, PInP{}, hinv, {==},
        (at, ({==}, hf => TL.nolf_at(len, tr, d, at, el, hok, BUF.andl(A, Bx, hab), hlt, BUF.andr(A, Bx, hab)))), hsp)

def lt_ok(+dfs: B.Defs, +dfs2: B.Defs, +b: Bool, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  +hb: {U32.is_lt(el, len) == b : Bool},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, [P.SBP{len, tr, d, at}], pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.lt(b, C.BT(len, tr), at, el, o2, Q.MB{P.mkRun(rp)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l)):
  match b:
    case False{}:
      tail_ok(dfs, dfs2, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, o2, rp, at, pd, eof, back, wp, asked, fneed, sp, hinv, hsp, ih)
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, tr), el), (C.BT(len, tr), C.AT(len, tr, el)), C.at_pair_t(len, tr, el)) :
        LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.tgo(W.swap.at(_, at, el, o2, Q.MB{P.mkRun(rp)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2), mkWins(fa, sp)), el, len, k, c0, l))
      if_ok(dfs, dfs2, Bool.not(Bool.and(U32.is_le(at, el), U32.is_eq(C.AT(len, tr, el), 10))), g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL,
        o2, rp, at, pd, eof, back, wp, asked, fneed, sp, hb, {==}, hinv, hsp, ih)

# The piece Q's input from at: the swap test.
def next_sb(+dfs: B.Defs, +dfs2: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  +at: U32,
  +hs: {src == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l)):
  +S1 = {[P.SBP{len, tr, d, at}] : List<&2, P.SrcP>}
  %Equal.sym(List<&2, P.SrcP>, src, S1, hs) :
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, S.StP{o2, S.MBP{rp}, _, pd, eof, back, wp, asked, fneed, dfs2}), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l))
  lt_ok(dfs, dfs2, U32.is_lt(el, len), g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, o2, rp, at, pd, eof, back, wp, asked, fneed, sp, {==},
    AB.subst(List<&2, P.SrcP>, z => Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, z, pd, eof, back, wp, asked, fneed, dfs2}), src, S1, hs, hinv), hsp, ih)

# The piece Q's input from at, behind any records (-m): the swap test when it
# is the first source; with records in front, the loop goes on as it is.
def next_in(+dfs: B.Defs, +dfs2: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +o2: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +sp: List<&2, PC.WP>,
  +at: U32,
  +hs: {S.plain(src) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l)):
  match src:
    case Nil{}:
      Empty.absurd(LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed, dfs2}), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l)),
        N.true_ne_false(Equal.cong(List<&2, P.SrcP>, Bool, z => List.is_empty(&2, P.SrcP, z), Nil{}, [P.SBP{len, tr, d, at}], hs)))
    case Con{P.SBP{+l2, +t2, +d2, +a2}, +rest}:
      next_sb(dfs, dfs2, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, o2, rp, Con{P.SBP{l2, t2, d2, a2}, rest}, pd, eof, back, wp, asked, fneed, sp, at, hs, hinv, hsp, ih)
    case Con{P.SLP{+q}, +rest}:
      Empty.absurd(LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, S.StP{o2, S.MBP{rp}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed, dfs2}), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l)),
        not_sb(len, tr, d, at, P.SLP{q}, rest, Nil{}, {==}, hs))
    case Con{P.SPP{+l2, +t2, +d2, +a2}, +rest}:
      ih(S.StP{o2, S.MBP{rp}, Con{P.SPP{l2, t2, d2, a2}, rest}, pd, eof, back, wp, asked, fneed, dfs2}, sp, PInP{}, hinv, {==},
        (at, (hs, hf => Empty.absurd({P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool}, N.true_ne_false(hf)))), hsp)
    case Con{P.SRP{+lx}, +rest}:
      ih(S.StP{o2, S.MBP{rp}, Con{P.SRP{lx}, rest}, pd, eof, back, wp, asked, fneed, dfs2}, sp, PInP{}, hinv, {==},
        (at, (hs, hf => Empty.absurd({P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool}, N.true_ne_false(hf)))), hsp)

# From a state p (the piece as Hold0 says), the loop goes on after the
# swap test (norm.bend's task.next).
def next_ok(+g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report, +dfs: B.Defs,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +p: S.StP, +sp: List<&2, PC.WP>, +x: PhP,
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, p),
  h0: Hold0(len, tr, d, x, p),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(S.mkSt(fa, p), mkPh(len, tr, x), mkWins(fa, sp), el, len), el, len, k, c0, l)):
  match p:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs2}:
      match md:
        case S.MSP{+s, +qs, +ql, +code}:
          dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, S.mkSt(fa, S.StP{o2, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs2}), x,
            S.StP{o2, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs2}, {==}, h0)
        case S.MBP{+rp}:
          match x:
            case PHeldP{}:
              ih(S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}, sp, PHeldP{}, hinv, {==}, Unit{}, hsp)
            case PInP{}:
              (+at, hs) = h0
              next_in(dfs, dfs2, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, o2, rp, src, pd, eof, back, wp, asked, fneed, sp, at, hs, hinv, hsp, ih)


# Hold0 only looks at the sources: a new window keeps it.
def hold0_win(+dfs: B.Defs, +dfs2: B.Defs, +len: U32, +tr: AT.Tree<U32>, +d: Nat, +x: PhP,
  +o2: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  h: Hold0(len, tr, d, x, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed, dfs2})) ->
  Hold0(len, tr, d, x, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed, dfs2}):
  match x:
    case PInP{}:
      h
    case PHeldP{}:
      Unit{}

def ms_mb(+m: S.MdP, +h1: {isMB(m) == True{} : Bool}, +h2: {MS.md_ms_p(m) == True{} : Bool}) -> Empty:
  match m:
    case S.MBP{+rp}:
      N.false_ne_true(h2)
    case S.MSP{+s, +qs, +ql, +code}:
      N.false_ne_true(h1)

# A read the window does not answer: the next spare window, or dirty.
def want_go(+sp: List<&2, PC.WP>, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report, +dfs: B.Defs,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  -st: Q.St, +p2: S.StP, +x: PhP,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +hrep: {S.report(fa, cs, "", Nil{}, p2) == T : R.Report},
  +hgd: {S.guard("", Nil{}, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +ho: {S.StP.o(p2) == o : B.Opts},
  t: Trk(dfs, fa, o, cs, c0, l, LA, p2),
  h0: Hold0(len, tr, d, x, p2),
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.want(st, mkWins(fa, sp), mkPh(len, tr, x), el, len), el, len, k, c0, l)):
    match sp:
    case Nil{}:
      dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, st, x, p2, est, h0)
    case +wp2 <> +sp2:
      match p2:
        case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs2}:
          +X = Bool.and(PC.wp_ok(fa, wp2), S.mb_win.k(wp2))
          +hw = BUF.andl(X, wins_ok(fa, sp2), hsp)
          +hsp2 = BUF.andr(X, wins_ok(fa, sp2), hsp)
          %Equal.sym(Q.St, st, S.mkSt(fa, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed, dfs2}), est) :
            LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(W.swap_win(_, PC.mkWin(fa, wp2)), mkPh(len, tr, x), mkWins(fa, sp2), el, len), el, len, k, c0, l))
          +wf3 = wf_swap(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
            Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o2)), S.recs_first(src)), S.recs_run(md, src)),
            PC.wp_ok(fa, wp2), S.mb_win(md, wp2), hwf, BUF.andl(PC.wp_ok(fa, wp2), S.mb_win.k(wp2), hw), mbw(md, wp2, BUF.andr(PC.wp_ok(fa, wp2), S.mb_win.k(wp2), hw)))
          +rep3 = Equal.trans(R.Report, S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed, dfs2}), S.report(fa, cs, "", Nil{}, S.StP{o2, md, src, pd, eof, back, wp, asked, fneed, dfs2}), T,
            rep_swap(dfs, dfs2, fa, cs, o2, md, src, pd, eof, back, wp, wp2, asked, fneed), hrep)
          next_ok(g, fa, o, cs, c0, l, LA, k, T, dfs, len, tr, d, el, hok, hL, S.StP{o2, md, src, pd, eof, back, wp2, None{}, fneed, dfs2}, sp2, x,
            (wf3, (rep3, (hgd, (heof, (ho, trk_swap(dfs, dfs2, fa, o, cs, c0, l, LA, o2, md, src, pd, eof, back, wp, wp2, asked, fneed, t)))))),
            hold0_win(dfs, dfs2, len, tr, d, x, o2, md, src, pd, eof, back, wp, wp2, asked, fneed, h0), hsp2, ih)


def res_out(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +len: U32, +tr: AT.Tree<U32>,
  -r0: W.TRes, rg: ResG(dfs, fa, o, cs, c0, l, LA, k, r0)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.TOut{C.BT(len, tr), r0}):
  (+r, g1) = rg
  (e, h) = g1
  (r, (Equal.cong(W.TRes, W.TOut, z => W.TOut{C.BT(len, tr), z}, r0, mkLR(fa, k, c0, l, r), e), h))

# Idle: with the piece held, the result as before; else (not reached) dirty.
def idle_go(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  -st: Q.St, +p2: S.StP, +x: PhP,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +heof: {S.StP.eof(p2) == False{} : Bool},
  +hsrc: {S.src_empty(S.StP.src(p2)) == True{} : Bool},
  +hstop: {S.stopped(S.StP.md(p2)) == False{} : Bool},
  t: Trk(dfs, fa, o, cs, c0, l, LA, p2),
  h0: Hold0(len, tr, d, x, p2)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.idle(st, mkPh(len, tr, x), k, c0, l), el, len, k, c0, l)):
  match x:
    case PInP{}:
      dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, st, PInP{}, p2, est, h0)
    case PHeldP{}:
      %Equal.sym(W.TOut, W.task.loop(g, W.TEnd{W.TOut{C.BT(len, tr), W.task.done(st, k, c0, l)}}, el, len, k, c0, l), W.TOut{C.BT(len, tr), W.task.done(st, k, c0, l)}, end_r(g, W.TOut{C.BT(len, tr), W.task.done(st, k, c0, l)}, el, len, k, c0, l)) :
        LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, _)
      %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) : LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.TOut{C.BT(len, tr), W.task.done(_, k, c0, l)})
      res_out(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.done(S.mkSt(fa, p2), k, c0, l), idle_done(dfs, fa, o, cs, c0, l, LA, k, p2, hwf, heof, hsrc, hstop, t))

# ---------------------------------------------------------------------------
# Ended: stopped against the phantom (the task runs again), or dirty
# ---------------------------------------------------------------------------

# The key again.run reads from a run (W.again.run's pair law).
def AGM(+rp: P.RunP) -> Maybe<&2, Nat>:
  match rp:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, +obl, +obt, +ow, +ns, x}:
      Bool.pick(Maybe<&2, Nat>, Bool.and(W.again.ph(ns), U32.is_lt(BUF.CF(obl, obt, ow, obl), obl)),
        Some{BUF.CP(U32.is_lt(BUF.CF(obl, obt, ow, obl), obl), obl, obt, BUF.CF(obl, obt, ow, obl), obl)}, None{})

# again.run hands the run back.
def ag_run(+rp: P.RunP) -> {W.again.run(P.mkRun(rp)) == (P.mkRun(rp), AGM(rp)) : NR.Run & Maybe<&2, Nat>}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +tb = BUF.CF(obl, obt, ow, obl)
      %Equal.sym(W.Cp, W.cp(C.BT(obl, obt), ow, obl), W.Cp{C.BT(obl, obt), U32.is_lt(tb, obl), BUF.CC(U32.is_lt(tb, obl), obl, obt, ow, tb), BUF.CP(U32.is_lt(tb, obl), obl, obt, tb, obl)}, BUF.cp_b(obl, obt, ow, obl)) :
        {W.again.run.k(W.again.key(W.again.ph(ns), _), n, i, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, ow, ns, x) == (P.mkRun(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), AGM(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x})) : NR.Run & Maybe<&2, Nat>}
      {==}

# The piece back from a state whose window was set aside.
def back_wn(+fa: List<&2, B.Contig>, +len: U32, +tr: AT.Tree<U32>, +x: PhP, +o2: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP,
  +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +dfs2: B.Defs) ->
  {W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)) == W.task.back(S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), mkPh(len, tr, x)) : D.Bytes}:
  match x:
    case PInP{}:
      {==}
    case PHeldP{}:
      {==}

def and3(+a: Bool, +b: Bool, +c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool}) -> {Bool.and(Bool.and(a, b), c) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(Bool.and(_, b), c) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(Bool.and(True{}, _), c) == True{} : Bool}
  hc

# A stop against the phantom below it (go): the piece back, and the
# windows for the second run; else dirty.
def again_go(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32, +x: PhP, +sp: List<&2, PC.WP>, +l2: Nat, +go: Bool,
  +o2: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +dfs2: B.Defs,
  +hw: {wins_ok(fa, wp <> sp) == True{} : Bool},
  h0: Hold0(len, tr, d, x, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2})) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.again.if(go, l2, o2, P.mkRun(rp), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2, mkWins(fa, sp), mkPh(len, tr, x)), el, len, k, c0, l)):
  match go:
    case False{}:
      dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), x, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}, {==}, h0)
    case True{}:
      %Equal.sym(W.TOut, W.task.loop(g, W.TEnd{W.TOut{W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)), W.TAgain{l2, PC.mkWin(fa, wp), mkWins(fa, sp)}}}, el, len, k, c0, l), W.TOut{W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)), W.TAgain{l2, PC.mkWin(fa, wp), mkWins(fa, sp)}}, end_r(g, W.TOut{W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)), W.TAgain{l2, PC.mkWin(fa, wp), mkWins(fa, sp)}}, el, len, k, c0, l)) :
        LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, _)
      (LAgain{l2, wp, sp}, (Equal.cong(D.Bytes, W.TOut, z => W.TOut{z, W.TAgain{l2, PC.mkWin(fa, wp), mkWins(fa, sp)}}, W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)), C.BT(len, tr),
        Equal.trans(D.Bytes, W.task.back(Q.St{o2, Q.MB{P.mkRun(rp)}, P.mkSrcs(src), P.mkPd(pd), eof, back, Q.WNone{}, asked, fneed, dfs2}, mkPh(len, tr, x)), W.task.back(S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), mkPh(len, tr, x)), C.BT(len, tr),
          back_wn(fa, len, tr, x, o2, rp, src, pd, eof, back, wp, asked, fneed, dfs2),
          back_x(fa, len, tr, d, x, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}, h0))), hw))

def again_m(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32, +x: PhP, +sp: List<&2, PC.WP>, +m: Maybe<&2, Nat>,
  +o2: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +dfs2: B.Defs,
  +hw: {wins_ok(fa, wp <> sp) == True{} : Bool},
  h0: Hold0(len, tr, d, x, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2})) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.again((P.mkRun(rp), m), l, o2, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2, mkWins(fa, sp), mkPh(len, tr, x)), el, len, k, c0, l)):
  match m:
    case None{}:
      dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, S.mkSt(fa, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}), x, S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2}, {==}, h0)
    case Some{+l2}:
      again_go(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, x, sp, l2, Nat.is_lt(l2, l), o2, rp, src, pd, eof, back, wp, asked, fneed, dfs2, hw, h0)

# Ended: in the byte mode, a stop against the phantom hands back the piece
# and the windows; anything else is dirty.
def ended_p(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32, +x: PhP, +p2: S.StP, +sp: List<&2, PC.WP>,
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  h0: Hold0(len, tr, d, x, p2)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.ended(S.mkSt(fa, p2), mkWins(fa, sp), mkPh(len, tr, x), l), el, len, k, c0, l)):
  match p2:
    case S.StP{+o2, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs2}:
      match md:
        case S.MSP{+s, +qs, +ql, +code}:
          dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, S.mkSt(fa, S.StP{o2, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs2}), x, S.StP{o2, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs2}, {==}, h0)
        case S.MBP{+rp}:
          +p3 = {S.StP{o2, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs2} : S.StP}
          +m0 = S.md_ok(S.MBP{rp})
          +h6 = AW.c9_6(m0, AW.W1(fa, p3), AW.W2(fa, p3), AW.W3(fa, p3), AW.W4(fa, p3), AW.W5(fa, p3), AW.W6(fa, p3), AW.W7(fa, p3), AW.W8(fa, p3), hwf)
          +h7 = AW.c9_7(m0, AW.W1(fa, p3), AW.W2(fa, p3), AW.W3(fa, p3), AW.W4(fa, p3), AW.W5(fa, p3), AW.W6(fa, p3), AW.W7(fa, p3), AW.W8(fa, p3), hwf)
          %Equal.sym(NR.Run & Maybe<&2, Nat>, W.again.run(P.mkRun(rp)), (P.mkRun(rp), AGM(rp)), ag_run(rp)) :
            LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.again(_, l, o2, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs2, mkWins(fa, sp), mkPh(len, tr, x)), el, len, k, c0, l))
          again_m(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, x, sp, AGM(rp), o2, rp, src, pd, eof, back, wp, asked, fneed, dfs2,
            and3(PC.wp_ok(fa, wp), S.mb_win.k(wp), wins_ok(fa, sp), h6, h7, hsp), h0)

def ended_go(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32, -st: Q.St, +x: PhP, +p2: S.StP, +sp: List<&2, PC.WP>,
  +est: {st == S.mkSt(fa, p2) : Q.St},
  +hwf: {S.WF(fa, p2) == True{} : Bool},
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  h0: Hold0(len, tr, d, x, p2)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.ended(st, mkWins(fa, sp), mkPh(len, tr, x), l), el, len, k, c0, l)):
  %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) :
    LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.ended(_, mkWins(fa, sp), mkPh(len, tr, x), l), el, len, k, c0, l))
  ended_p(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, x, p2, sp, hwf, hsp, h0)

# One advance a from p (adv_ok's guarantee hadv), then the rest of the loop.
def step(+dfs: B.Defs, +g: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +p: S.StP, +sp: List<&2, PC.WP>, +x: PhP, a: Q.Adv,
  +hsp: {wins_ok(fa, sp) == True{} : Bool},
  +heof: {S.StP.eof(p) == False{} : Bool},
  +ho: {S.StP.o(p) == o : B.Opts},
  t: Trk(dfs, fa, o, cs, c0, l, LA, p),
  +hmb: {isMB(S.StP.md(p)) == True{} : Bool},
  h: Hold(len, tr, d, x, p),
  hadv: S.AdvG(fa, T, cs, "", Nil{}, p, a),
  ih: IH(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el)) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.adv(a, mkWins(fa, sp), mkPh(len, tr, x), el, len, k, c0, l), el, len, k, c0, l)):
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
      (+ho2, h9) = h8
      (mv, kp) = h9
      t2 = trk_md(dfs, S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, hh => Empty.absurd({MS.md_ms_p(S.StP.md(p2)) == True{} : Bool}, ms_mb(S.StP.md(p), hmb, hh)))
      %Equal.sym(Q.St, st, S.mkSt(fa, p2), est) :
        LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(g, W.task.next(_, mkPh(len, tr, x), mkWins(fa, sp), el, len), el, len, k, c0, l))
      next_ok(g, fa, o, cs, c0, l, LA, k, T, dfs, len, tr, d, el, hok, hL, p2, sp, x,
        (hwf2, (hrep2, (hgd2, (Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), (Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(p), o, ho2, ho), t2))))),
        kept_hold(len, tr, d, x, p, p2, hmb, h, kp), hsp, ih)
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
      (+ho2, h12) = h11
      (mv, kp) = h12
      t2 = trk_md(dfs, S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, hh => Empty.absurd({MS.md_ms_p(S.StP.md(p2)) == True{} : Bool}, ms_mb(S.StP.md(p), hmb, hh)))
      want_go(sp, g, fa, o, cs, c0, l, LA, k, T, dfs, len, tr, d, el, hok, hL, st, p2, x, est, hwf2, hrep2, hgd2,
        Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(p), o, ho2, ho), t2,
        kept_hold(len, tr, d, x, p, p2, hmb, h, kp), hsp, ih)
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
      (+ho2, h10) = h9
      (mv, kp) = h10
      t2 = trk_md(dfs, S.StP.md(p), S.StP.md(p2), fa, o, cs, c0, l, LA, p, p2, t, mv, ho, hh => Empty.absurd({MS.md_ms_p(S.StP.md(p2)) == True{} : Bool}, ms_mb(S.StP.md(p), hmb, hh)))
      idle_go(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, st, p2, x, est, hwf2, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, heof2, heof), hsrc, hstop, t2,
        kept_hold(len, tr, d, x, p, p2, hmb, h, kp))
    case Q.Ended{st}:
      (+p2, h1) = hadv
      (+est, h2) = h1
      (+hwf2, h3) = h2
      (+hrep2, h4) = h3
      (hask, h5) = h4
      (hstop, h6) = h5
      (+heof2, h7) = h6
      (+hgd2, h8) = h7
      (+ho2, dkp) = h8
      (hdd, kp) = dkp
      ended_go(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, st, x, p2, sp, est, hwf2, hsp, kept_hold(len, tr, d, x, p, p2, hmb, h, kp))
    case Q.Yield{st}:
      (+p2, h1) = hadv
      (+est, h2) = h1
      (+hwf2, h3) = h2
      (+hrep2, h4) = h3
      (hask, h5) = h4
      (hstop, h6) = h5
      (+heof2, h7) = h6
      (+hgd2, h8) = h7
      (+ho2, dkp) = h8
      (hdd, kp) = dkp
      dirty_st(dfs, g, fa, o, cs, c0, l, LA, k, len, tr, d, el, st, x, p2, est, kept_hold(len, tr, d, x, p, p2, hmb, h, kp))

# The task's loop from a good state: the piece back, and a result that is
# dirty, or clean with the lines it handled.
def loop_ok(+dfs: B.Defs, +f: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +p: S.StP, +sp: List<&2, PC.WP>, +x: PhP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, p),
  +hmb: {isMB(S.StP.md(p)) == True{} : Bool},
  h: Hold(len, tr, d, x, p),
  +hsp: {wins_ok(fa, sp) == True{} : Bool}) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(f, W.TGo{S.mkSt(fa, p), mkWins(fa, sp), mkPh(len, tr, x)}, el, len, k, c0, l)):
  match f:
    case 0n:
      (LDirty{}, (Equal.cong(D.Bytes, W.TOut, z => W.TOut{z, W.TDirty{}}, W.task.back(S.mkSt(fa, p), mkPh(len, tr, x)), C.BT(len, tr), back_x(fa, len, tr, d, x, p, hold0_of(len, tr, d, x, p, h))), Unit{}))
    case 1n+g:
      (+hwf, i1) = hinv
      (+hrep, i2) = i1
      (+hgd, i3) = i2
      (+heof, i4) = i3
      (+ho, t) = i4
      step(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, p, sp, x, Q.advance(S.mkSt(fa, p)), hsp, heof, ho, t, hmb, h,
        SIM.adv_ok(fa, T, cs, "", Nil{}, p, hb, hwf, hrep, hgd),
        p2 => sp2 => x2 => j2 => m2 => h2 => w2 => loop_ok(dfs, g, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, p2, sp2, x2, hb, j2, m2, h2, w2))

# The task from its start state p0 (the piece Q's only source, from k + 1).
def start_ok(+dfs: B.Defs, +f: Nat, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA: List<&2, B.Line>, +k: U32, +T: R.Report,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +p0: S.StP, +sp: List<&2, PC.WP>, +at: U32,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  hinv: Inv(dfs, fa, o, cs, c0, l, LA, T, p0),
  +hs: {S.StP.src(p0) == [P.SBP{len, tr, d, at}] : List<&2, P.SrcP>},
  +hsp: {wins_ok(fa, sp) == True{} : Bool}) ->
  LoopG(dfs, fa, o, cs, c0, l, LA, k, len, tr, W.task.loop(f, W.task.next(S.mkSt(fa, p0), W.PIn{}, mkWins(fa, sp), el, len), el, len, k, c0, l)):
  next_ok(f, fa, o, cs, c0, l, LA, k, T, dfs, len, tr, d, el, hok, hL, p0, sp, PInP{}, hinv, (at, Equal.cong(List<&2, P.SrcP>, List<&2, P.SrcP>, z => S.plain(z), S.StP.src(p0), [P.SBP{len, tr, d, at}], hs)), hsp,
    p2 => sp2 => x2 => j2 => m2 => h2 => w2 => loop_ok(dfs, f, fa, o, cs, c0, l, LA, k, T, len, tr, d, el, hok, hL, p2, sp2, x2, hb, j2, m2, h2, w2))
