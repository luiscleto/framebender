import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_step.bend as ST
import ./proof_e_bud_seq.bend as SQ
import ./proof_e_wrap_base.bend as QB
import ./proof_b_budget_step.bend as BS
import ./proof_b_drive_step.bend as DS
import ./proof_base.bend as PB
import ./proof_e_merge.bend as MC
import ./proof_b_sim.bend as SA
import ./proof_e_bud_fed.bend as FD
import ./proof_e_bud_list.bend as LI
import ../lawful-bytes/defs.bend as D
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ./proof_b_defs.bend as P
import ./proof_b_drive_out.bend as DO
import ./proof_b_bud_start.bend as BSt
import ./proof_b_budget_lem.bend as BL
import ./proof_b_lines_str.bend as LS
import ./proof_e_wrap_edge.bend as ED
import ../lawful-words/proof_nat.bend as N

# Phase E, area E2: the combine, one piece per step (W.comb.next), from a
# good Q state waiting for more with the batch's pieces ps (results xs) still
# to go before cs: its potential stays within Q's (over ps then cs).

# The merge's WA
# ==============

law rem_le:
  for +fa: List<&2, B.Contig>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +l: B.Line
  {Nat.is_le(BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l), BN.LA(fa, l)) == True{} : Bool}

def rem_le(fa, fl, back, wp, m, l):
  +R = BN.RW(l)
  +Z = BN.ZW(fa)
  +b2 = Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l)))
  +b3 = Nat.is_eq(back, 0n)
  +b4 = Nat.is_lt(back, BN.lpos(l))
  BSt.pick_mono(BN.lgate(l), Nat.add(Nat.add(BN.pick(fl, R), BN.pick(b2, R)), Nat.add(BN.pick(b3, Z), BN.pick(b4, Z))), Nat.add(Nat.add(R, R), Nat.add(Z, Z)),
    BSt.add2(Nat.add(BN.pick(fl, R), BN.pick(b2, R)), Nat.add(R, R), Nat.add(BN.pick(b3, Z), BN.pick(b4, Z)), Nat.add(Z, Z),
      BSt.add2(BN.pick(fl, R), R, BN.pick(b2, R), R, BSt.pick_le1(fl, R), BSt.pick_le1(b2, R)),
      BSt.add2(BN.pick(b3, Z), Z, BN.pick(b4, Z), Z, BSt.pick_le1(b3, Z), BSt.pick_le1(b4, Z))))

law wa_las:
  for +fa: List<&2, B.Contig>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +ls: List<&2, B.Line>
  {Nat.is_le(BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls), BN.LAs(fa, ls)) == True{} : Bool}

def wa_las(fa, fl, back, wp, m, ls):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      N.le_add_mono_r(BN.LAs(fa, t), BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l), BN.LA(fa, l), rem_le(fa, fl, back, wp, m, l))

law las_app:
  for +fa: List<&2, B.Contig>
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  {BN.LAs(fa, List.append(&2, B.Line, xs, ys)) == Nat.add(BN.LAs(fa, xs), BN.LAs(fa, ys)) : Nat}

def las_app(fa, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, Nat.add(BN.LA(fa, x), BN.LAs(fa, List.append(&2, B.Line, t, ys))), Nat.add(BN.LA(fa, x), Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys))), Nat.add(Nat.add(BN.LA(fa, x), BN.LAs(fa, t)), BN.LAs(fa, ys)),
        Equal.cong(Nat, Nat, z => Nat.add(BN.LA(fa, x), z), BN.LAs(fa, List.append(&2, B.Line, t, ys)), Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys)), las_app(fa, t, ys)),
        Equal.sym(Nat, Nat.add(Nat.add(BN.LA(fa, x), BN.LAs(fa, t)), BN.LAs(fa, ys)), Nat.add(BN.LA(fa, x), Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys))), N.add_assoc(BN.LA(fa, x), BN.LAs(fa, t), BN.LAs(fa, ys))))

law bi0w:
  for +fa: List<&2, B.Contig>
  for +wp: PC.WP
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +ls: List<&2, B.Line>
  {BN.bi.ls(0n, PC.mkWin(fa, wp), m, ls) == True{} : Bool}

def bi0w(fa, wp, m, ls):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      {==}

# The merged state's WA is within WA before the piece: the text before it was
# pend ++ a ++ LF ++ after(c, k) ++ rest (PcOK), and the task's lines ls are
# the front of lines(after ++ rest), the rest being lines(tp ++ rest) (TcOK).
law wa_merge.k:
  for +fa: List<&2, B.Contig>
  for +c: String
  for +k: U32
  for +a: String
  for +L: List<&2, String>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(L))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(L)))) : List<&2, B.Line>}
  {Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, L)), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed})) == True{} : Bool}

def wa_merge.k(fa, c, k, a, L, o, md, pd, back, wp, fneed, pdT, wpT, ls, hw, hc, hn, hT):
  +D = P.pdtext(pd)
  +Y = String.append(PT.after(c, k), String.concat(L))
  +Lt = B.Text.lines(String.append(P.pdtext(pdT), String.concat(L)))
  +fl = BN.fast_left(S.mkMd(md), fneed)
  +hd = DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
  +e1 = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(String.append(z, String.concat(L))), BN.pdT(P.mkPd(pdT)), P.pdtext(pdT), BL.pdT_pic(pdT))
  +e2 = Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(BN.pdT(P.mkPd(pd)), String.concat(c <> L))), B.Text.lines(String.append(D, String.concat(c <> L))), B.Text.line(String.append(D, a)) <> List.append(&2, B.Line, ls, Lt),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(String.append(z, String.concat(c <> L))), BN.pdT(P.mkPd(pd)), D, BL.pdT_pic(pd)),
    Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(D, String.concat(c <> L))), B.Text.lines(String.append(String.append(D, a), String.append("\n", Y))), B.Text.line(String.append(D, a)) <> List.append(&2, B.Line, ls, Lt),
      Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), String.append(D, String.concat(c <> L)), String.append(String.append(D, a), String.append("\n", Y)), ED.split_first(D, c, a, PT.after(c, k), L, hc)),
      Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(String.append(D, a), String.append("\n", Y))), B.Text.line(String.append(D, a)) <> B.Text.lines(Y), B.Text.line(String.append(D, a)) <> List.append(&2, B.Line, ls, Lt),
        LS.lines_cons(String.append(D, a), Y, LS.nolf_app(D, a, hd, hn)),
        Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => B.Text.line(String.append(D, a)) <> z, B.Text.lines(Y), List.append(&2, B.Line, ls, Lt), hT))))
  +l1 = B.Text.line(String.append(D, a))
  +R0 = BN.rem(fa, fl, back, PC.mkWin(fa, wp), None{}, l1)
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(BN.pdT(P.mkPd(pdT)), String.concat(L))), Lt, e1) :
    {Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, _), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed})) == True{} : Bool}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(BN.pdT(P.mkPd(pd)), String.concat(c <> L))), l1 <> List.append(&2, B.Line, ls, Lt), e2) :
    {Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, Lt), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool}
  %Equal.sym(Nat, BN.LAs(fa, List.append(&2, B.Line, ls, Lt)), Nat.add(BN.LAs(fa, ls), BN.LAs(fa, Lt)), las_app(fa, ls, Lt)) :
    {Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, Lt), Nat.add(R0, _)) == True{} : Bool}
  N.le_trans(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, Lt), BN.LAs(fa, Lt), Nat.add(R0, Nat.add(BN.LAs(fa, ls), BN.LAs(fa, Lt))),
    wa_las(fa, True{}, 0n, wpT, None{}, Lt),
    N.le_trans(BN.LAs(fa, Lt), Nat.add(BN.LAs(fa, ls), BN.LAs(fa, Lt)), Nat.add(R0, Nat.add(BN.LAs(fa, ls), BN.LAs(fa, Lt))),
      N.le_add_l(BN.LAs(fa, Lt), BN.LAs(fa, ls)), N.le_add_l(Nat.add(BN.LAs(fa, ls), BN.LAs(fa, Lt)), R0)))

# The bound of the combine of piece c (the pieces after it L, the driver's cs).
def VCc(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP, +c: String, +L: List<&2, String>) -> Nat:
  Nat.add(ST.VQ(T, c <> L, False{}, O, BDs.WP(fa, c <> L, p)), BD.XK(cs))

law ar_s:
  for +Q: Nat
  for +X: Nat
  {Nat.is_le(Nat.add(Nat.add(Q, 1n), X), Nat.add(1n+Q, X)) == True{} : Bool}

def ar_s(Q, X):
  %Equal.sym(Nat, Nat.add(Q, 1n), 1n+Q, N.add_one(Q)) : {Nat.is_le(Nat.add(_, X), Nat.add(1n+Q, X)) == True{} : Bool}
  N.le_refl(Nat.add(1n+Q, X))

# The merged state's need: (A + (2 + (H2 + (1 + WM)))) + 0 + X <= ((1 + A) + (2 + (H + W0))) + X.
law ar_m:
  for +A: Nat
  for +H2: Nat
  for +H: Nat
  for +WM: Nat
  for +W0: Nat
  for +X: Nat
  for +hH: {Nat.is_le(H2, H) == True{} : Bool}
  for +hW: {Nat.is_le(WM, W0) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H2, Nat.add(1n, WM)))), 0n), X), Nat.add(Nat.add(1n+A, Nat.add(2n, Nat.add(H, W0))), X)) == True{} : Bool}

def ar_m(A, H2, H, WM, W0, X, hH, hW):
  +Z2 = Nat.add(H2, WM)
  +e = Equal.trans(Nat, Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H2, Nat.add(1n, WM)))), 0n), Nat.add(A, Nat.add(2n, Nat.add(H2, 1n+WM))), 1n+Nat.add(A, Nat.add(2n, Z2)),
    N.add_zero(Nat.add(A, Nat.add(2n, Nat.add(H2, 1n+WM)))),
    Equal.trans(Nat, Nat.add(A, Nat.add(2n, Nat.add(H2, 1n+WM))), Nat.add(A, 1n+Nat.add(2n, Z2)), 1n+Nat.add(A, Nat.add(2n, Z2)),
      Equal.cong(Nat, Nat, z => Nat.add(A, Nat.add(2n, z)), Nat.add(H2, 1n+WM), 1n+Z2, N.add_succ(H2, WM)),
      N.add_succ(A, Nat.add(2n, Z2))))
  %Equal.sym(Nat, Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H2, Nat.add(1n, WM)))), 0n), 1n+Nat.add(A, Nat.add(2n, Z2)), e) :
    {Nat.is_le(Nat.add(_, X), Nat.add(Nat.add(1n+A, Nat.add(2n, Nat.add(H, W0))), X)) == True{} : Bool}
  N.le_add_mono_r(X, Nat.add(A, Nat.add(2n, Z2)), Nat.add(A, Nat.add(2n, Nat.add(H, W0))), ST.vq_le(A, Z2, Nat.add(H, W0), BSt.add2(H2, H, WM, W0, hH, hW)))

# A step of Q while combining, within the piece's bound.
law seq_any:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for s: Norm.Step
  for +W1: Nat
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  for h: BDs.BudS(fa, T, List.append(&2, String, PT.texts(pt), cs), O, W1, s)
  for +hW: {Nat.is_le(W1, BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.seq_out(s, PT.mkTOuts(fa, pt, xt), e))

def seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, s, W1, hts, he, h, hW):
  +L = List.append(&2, String, PT.texts(pt), cs)
  +W0 = BDs.WP(fa, c <> L, p)
  ST.budw_mono(fa, T, cs, ef, O, Nat.add(Nat.add(ST.VQ(T, L, False{}, O, W0), 1n), BD.XK(cs)), VCc(fa, T, cs, O, p, c, L), W.seq_out(s, PT.mkTOuts(fa, pt, xt), e),
    SQ.seq_bud(fa, T, cs, ef, O, W0, s, pt, xt, e, hts, he, BS.bud_mono(fa, T, L, O, W1, W0, s, h, hW)),
    ar_s(ST.VQ(T, L, False{}, O, W0), BD.XK(cs)))

# Q goes on from a good state with nothing asked.
law go_seq:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +p2: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw2: {S.WF(fa, p2) == True{} : Bool}
  for +hr2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report}
  for +ha2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg2: {S.guard(O, N, p2) == True{} : Bool}
  for +hbi2: {BN.biS(S.mkSt(fa, p2), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hW2: {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), p2), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.seq_out(Norm.go(S.mkSt(fa, p2)), PT.mkTOuts(fa, pt, xt), e))

def go_seq(fa, T, cs, O, N, ef, p, c, pt, xt, e, p2, hb, hw2, hr2, ha2, hg2, hbi2, hW2, hts, he):
  +L = List.append(&2, String, PT.texts(pt), cs)
  seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.go(S.mkSt(fa, p2)), BDs.WP(fa, L, p2), hts, he, BS.go_bud(fa, T, L, O, N, p2, hb, hw2, hr2, ha2, hg2, hbi2), hW2)

# The merged state's WA, from any state waiting for more.
law wa_merge:
  for +fa: List<&2, B.Contig>
  for +c: String
  for +k: U32
  for +a: String
  for +L: List<&2, String>
  for +p: S.StP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(L))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(L)))) : List<&2, B.Line>}
  {Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, L)), BDs.WP(fa, c <> L, p)) == True{} : Bool}

def wa_merge(fa, c, k, a, L, p, pdT, wpT, ls, hm, hc, hn, hT):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed}:
      Empty.absurd({Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, L)), BDs.WP(fa, c <> L, S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed})) == True{} : Bool},
        PB.false_ne_true(DS.mo_se(S.WF(fa, S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed}), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      Empty.absurd({Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, L)), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed})) == True{} : Bool},
        PB.false_ne_true(DS.mo_ne(S.WF(fa, S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed}), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      Empty.absurd({Nat.is_le(BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, L)), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed})) == True{} : Bool},
        PB.false_ne_true(DS.mo_no(S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed}), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      wa_merge.k(fa, c, k, a, L, o, md, pd, back, wp, fneed, pdT, wpT, ls, DS.mo_w(S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}), True{}, True{}, True{}, hm), hc, hn, hT)

# W.edge.where on a picture (as area E1's where_eq, proof_e_wrap_clean.bend).
def here_s(+src: List<&2, P.SrcP>, +k: U32, +n: Nat, +n0: Nat) -> Bool:
  match src:
    case Con{P.SBP{len, t, d, +at}, Nil{}}:
      U32.is_eq(at, (k + 1 : U32)) && Nat.is_eq(n, 1n+n0)
    case _:
      False{}

def here_p(+p2: S.StP, +k: U32, +n0: Nat) -> Bool:
  match p2:
    case S.StP{o, +md, +src, pd, eof, back, wp, asked, fneed}:
      here_s(src, k, QB.nbm(md), n0)

def ok_p(+p2: S.StP) -> Bool:
  match p2:
    case S.StP{o, md, src, pd, +eof, back, wp, +asked, +fneed}:
      Bool.not(eof) && W.is_none(asked) && Bool.not(fneed)

law where_eq:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +k: U32
  for +c0: String
  for +l: Nat
  for +n0: Nat
  {W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0) == W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}) : W.Ew}

def where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0):
  match p2:
    case S.StP{+o2, S.MBP{P.RunP{+n2, +i2, +h2, +c2, +cbl2, +cbt2, +e2, +l2, +f2, +b2, +bn2, +tl2, +k2, +obl2, +obt2, +ow2, +ns2, +x2}}, Nil{}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MBP{P.RunP{+n2, +i2, +h2, +c2, +cbl2, +cbt2, +e2, +l2, +f2, +b2, +bn2, +tl2, +k2, +obl2, +obt2, +ow2, +ns2, +x2}}, Con{P.SBP{+len2, +t2, +d2, +at2}, Nil{}}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MBP{P.RunP{+n2, +i2, +h2, +c2, +cbl2, +cbt2, +e2, +l2, +f2, +b2, +bn2, +tl2, +k2, +obl2, +obt2, +ow2, +ns2, +x2}}, Con{P.SBP{+len2, +t2, +d2, +at2}, Con{+sh, +st}}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MBP{P.RunP{+n2, +i2, +h2, +c2, +cbl2, +cbt2, +e2, +l2, +f2, +b2, +bn2, +tl2, +k2, +obl2, +obt2, +ow2, +ns2, +x2}}, Con{P.SLP{+sp}, +st}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, Nil{}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, Con{P.SBP{+len2, +t2, +d2, +at2}, Nil{}}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, Con{P.SBP{+len2, +t2, +d2, +at2}, Con{+sh, +st}}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, Con{P.SLP{+sp}, +st}, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      {==}

# The splice: merge.ok holds and the task's run is merged (Q's state is then
# the merged run, the task's line end and window; Ask{[]} for the next piece),
# or not and Q goes on.
law splice_mb:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +o2: B.Opts
  for +rp2: P.RunP
  for +src2: List<&2, P.SrcP>
  for +pd2: P.PdP
  for +back2: Nat
  for +wp2: PC.WP
  for +asked2: Maybe<&2, List<&2, Pr.Req>>
  for +fneed2: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for +hw2: {S.WF(fa, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool}
  for +hr2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}) == T : R.Report}
  for +ha2: {S.StP.asked(S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg2: {S.guard(O, N, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}) == True{} : Bool}
  for +hbi2: {BN.biS(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hW2: {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  for +b: Bool
  for +hq: {MC.okP(l, R.Opts.w(o2), c0, rp2, rpT) == b : Bool}
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e))

def splice_mb(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, o2, rp2, src2, pd2, back2, wp2, asked2, fneed2, hb, hm, hc, hn, hT, hts, hw2, hr2, ha2, hg2, hbi2, hW2, b, hq, he):
  match b:
    case False{}:
      %Equal.sym(W.Mg, W.merge(P.mkRun(rp2), P.mkRun(rpT), l, R.Opts.w(o2), c0), W.MNo{P.mkRun(rp2)}, MC.merge_no(l, R.Opts.w(o2), c0, rp2, rpT, hq)) :
        ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.mg(_, o2, P.mkPd(pdT), PC.mkWin(fa, wpT), P.mkSrcs(src2), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2, PT.mkTOuts(fa, pt, xt), e))
      go_seq(fa, T, cs, O, N, ef, p, c, pt, xt, e, S.StP{o2, S.MBP{rp2}, src2, pd2, False{}, back2, wp2, asked2, fneed2}, hb, hw2, hr2, ha2, hg2, hbi2, hW2, hts, he)
    case True{}:
      +LL = List.append(&2, String, PT.texts(pt), cs)
      +W0 = BDs.WP(fa, c <> LL, p)
      %Equal.sym(W.Mg, W.merge(P.mkRun(rp2), P.mkRun(rpT), l, R.Opts.w(o2), c0), W.MOk{C.BT(P.RunP.obl(rp2), MC.RunP.obt(rp2)), List.reverse(&2, B.Note, MC.RunP.ns(rp2)), P.mkRun(MC.mergeP(c0, rp2, rpT))}, MC.merge_yes(l, R.Opts.w(o2), c0, rp2, rpT, hq)) :
        ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.mg(_, o2, P.mkPd(pdT), PC.mkWin(fa, wpT), P.mkSrcs(src2), P.mkPd(pd2), back2, PC.mkWin(fa, wp2), asked2, fneed2, PT.mkTOuts(fa, pt, xt), e))
      hnf => (bi0w(fa, wpT, None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, List.append(&2, String, BD.tots(PT.mkTOuts(fa, pt, xt)), cs))),
        +t => hout => hp => +n => en =>
          %en : {Nat.is_le(_, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs))) == True{} : Bool}
          %Equal.sym(List<&2, String>, BD.tots(PT.mkTOuts(fa, pt, xt)), PT.texts(pt), hts) :
            {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, Norm.St{o2, Norm.MB{P.mkRun(MC.mergeP(c0, rp2, rpT))}, Nil{}, P.mkPd(pdT), False{}, 0n, PC.mkWin(fa, wpT), None{}, False{}}, List.append(&2, String, _, cs), False{}, Pr.Ask{Nil{}}, String.append(O, t)), BN.pick(False{}, 1n)), BD.XK(cs)), VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs))) == True{} : Bool}
          ar_m(Nat.add(List.length(&2, String, LL), 1n), BN.HO(T, String.append(O, t)), BN.HO(T, O), BN.WA.ls(fa, True{}, 0n, PC.mkWin(fa, wpT), None{}, BN.lines(Nil{}, P.mkPd(pdT), False{}, LL)), W0, BD.XK(cs),
            BS.hoa(T, O, t), wa_merge(fa, c, k, a, LL, p, pdT, wpT, ls, hm, hc, hn, hT)))

law splice_bud:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +p2: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for +hw2: {S.WF(fa, p2) == True{} : Bool}
  for +hr2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report}
  for +ha2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg2: {S.guard(O, N, p2) == True{} : Bool}
  for +hbi2: {BN.biS(S.mkSt(fa, p2), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hW2: {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), p2), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  for +hok: {ok_p(p2) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.splice(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e))

def splice_bud(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, p2, hb, hm, hc, hn, hT, hts, hw2, hr2, ha2, hg2, hbi2, hW2, hok, he):
  match p2:
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, +src2, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      go_seq(fa, T, cs, O, N, ef, p, c, pt, xt, e, S.StP{o2, S.MSP{s2, qs2, ql2, cd2}, src2, pd2, eof2, back2, wp2, asked2, fneed2}, hb, hw2, hr2, ha2, hg2, hbi2, hW2, hts, he)
    case S.StP{+o2, S.MBP{+rp2}, +src2, +pd2, True{}, +back2, +wp2, +asked2, +fneed2}:
      Empty.absurd(ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, src2, pd2, True{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.false_ne_true(hok))
    case S.StP{+o2, S.MBP{+rp2}, +src2, +pd2, False{}, +back2, +wp2, +asked2, +fneed2}:
      splice_mb(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, o2, rp2, src2, pd2, back2, wp2, asked2, fneed2, hb, hm, hc, hn, hT, hts, hw2, hr2, ha2, hg2, hbi2, hW2, MC.okP(l, R.Opts.w(o2), c0, rp2, rpT), {==}, he)

# The edge
# ========

# What the edge does from a later advance (fuel g).
def IHE(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat) -> Type:
  @q: S.StP -> {S.WF(fa, q) == True{} : Bool} -> {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, q) == T : R.Report} -> {S.guard(O, N, q) == True{} : Bool}
    -> {S.StP.asked(q) == None{} : Maybe<&2, List<&2, Pr.Req>>} -> {BN.biS(S.mkSt(fa, q), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
    -> {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), q), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool} -> WD.EofOK(e, ef, cs)
    -> ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.edge.of(Norm.advance(S.mkSt(fa, q)), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))

def IHg(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat) -> Type:
  match g:
    case 0n:
      Unit
    case 1n+h:
      IHE(h, fa, T, cs, O, N, ef, p, c, k, c0, l, rpT, pdT, wpT, pt, xt, e, n0)

# Q after an advance that handled a line: at the piece's k+1 with its count
# up by one (here) or not yet.
law edge_w:
  for +g: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +n0: Nat
  for +p2: S.StP
  for +here: Bool
  for +ok: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for +hw2: {S.WF(fa, p2) == True{} : Bool}
  for +hr2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report}
  for +ha2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg2: {S.guard(O, N, p2) == True{} : Bool}
  for +hbi2: {BN.biS(S.mkSt(fa, p2), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hW2: {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), p2), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  for +hh: {here_p(p2, k, n0) == here : Bool}
  for +hk: {ok_p(p2) == ok : Bool}
  for he: WD.EofOK(e, ef, cs)
  for ih: IHg(g, fa, T, cs, O, N, ef, p, c, k, c0, l, rpT, pdT, wpT, pt, xt, e, n0)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.edge.where.if(here, ok, S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), PT.mkTOuts(fa, pt, xt), e))

def edge_w(g, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, p2, here, ok, hb, hm, hc, hn, hT, hts, hw2, hr2, ha2, hg2, hbi2, hW2, hh, hk, he, ih):
  match g here ok:
    case _ True{} True{}:
      splice_bud(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, p2, hb, hm, hc, hn, hT, hts, hw2, hr2, ha2, hg2, hbi2, hW2, hk, he)
    case _ True{} False{}:
      go_seq(fa, T, cs, O, N, ef, p, c, pt, xt, e, p2, hb, hw2, hr2, ha2, hg2, hbi2, hW2, hts, he)
    case 0n False{} _:
      go_seq(fa, T, cs, O, N, ef, p, c, pt, xt, e, p2, hb, hw2, hr2, ha2, hg2, hbi2, hW2, hts, he)
    case 1n+h False{} _:
      ih(p2, hw2, hr2, hg2, ha2, hbi2, hW2, he)

# The edge from Q's advance av at a good state pa (fuel g).
law edge_bud:
  for +g: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +n0: Nat
  for +pa: S.StP
  for av: Norm.Adv
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for +hwa: {S.WF(fa, pa) == True{} : Bool}
  for +hra: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pa) == T : R.Report}
  for +haa: {S.StP.asked(pa) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hga: {S.guard(O, N, pa) == True{} : Bool}
  for +hbia: {BN.biS(S.mkSt(fa, pa), List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hWa: {Nat.is_le(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)) == True{} : Bool}
  for ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pa, av)
  for ab: BDs.AdvB(fa, List.append(&2, String, PT.texts(pt), cs), pa, av)
  for abi: BDs.AdvBi(List.append(&2, String, PT.texts(pt), cs), av)
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.edge.of(av, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))

def edge_bud(g, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, pa, av, hb, hm, hc, hn, hT, hts, hwa, hra, haa, hga, hbia, hWa, ag, ab, abi, he):
  match g av:
    case 0n Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+elt, a5) = a4
      (+eask2, a6) = a5
      (+eeof, a7) = a6
      (+eg2, a8) = a7
      +ab2 = AB.subst(Norm.St, z => {Nat.is_le(BN.WAS(fa, z, List.append(&2, String, PT.texts(pt), cs)), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa)) == True{} : Bool}, st, S.mkSt(fa, p2), est, ab)
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}, st, S.mkSt(fa, p2), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(0n, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(0n, n0, _, PT.mkTOuts(fa, pt, xt), e))
      edge_w(0n, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, p2, here_p(p2, k, n0), ok_p(p2), hb, hm, hc, hn, hT, hts, wf2, er2, eask2, eg2, bi2, N.le_trans(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), p2), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p), ab2, hWa), {==}, {==}, he, Unit{})
    case 1n+h Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+elt, a5) = a4
      (+eask2, a6) = a5
      (+eeof, a7) = a6
      (+eg2, a8) = a7
      +ab2 = AB.subst(Norm.St, z => {Nat.is_le(BN.WAS(fa, z, List.append(&2, String, PT.texts(pt), cs)), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa)) == True{} : Bool}, st, S.mkSt(fa, p2), est, ab)
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}, st, S.mkSt(fa, p2), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(1n+h, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(1n+h, n0, _, PT.mkTOuts(fa, pt, xt), e))
      edge_w(1n+h, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, p2, here_p(p2, k, n0), ok_p(p2), hb, hm, hc, hn, hT, hts, wf2, er2, eask2, eg2, bi2, N.le_trans(BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), p2), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p), ab2, hWa), {==}, {==}, he,
        +q => +wq => +rq => +gq => +aq => +biq => +hWq => heq =>
          edge_bud(h, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, q, Norm.advance(S.mkSt(fa, q)), hb, hm, hc, hn, hT, hts, wq, rq, aq, gq, biq, hWq,
            SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, q, hb, wq, rq, gq), BS.adv_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, q, hb, wq, rq, gq, aq, biq), BS.adv_bi(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, q, hb, wq, rq, gq, aq, biq), heq))
    case _ Norm.Want{st, +r}:
      (+p2, a1) = ag
      (+est, a2) = a1
      +ab2 = AB.subst(Norm.St, z => {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, r), BN.WAS(fa, z, List.append(&2, String, PT.texts(pt), cs))), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa)) == True{} : Bool}, st, S.mkSt(fa, p2), est, ab)
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}, st, S.mkSt(fa, p2), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.EWant{_, r, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}}, PT.mkTOuts(fa, pt, xt), e))
      seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.pump(0n, Norm.Want{S.mkSt(fa, p2), r}), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), hts, he,
        BS.out_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, p2, Pr.Ask{r}, BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), bi2, ab2), hWa)
    case _ Norm.Idle{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      +ab2 = AB.subst(Norm.St, z => {Nat.is_le(BN.WAS(fa, z, List.append(&2, String, PT.texts(pt), cs)), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa)) == True{} : Bool}, st, S.mkSt(fa, p2), est, ab)
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}, st, S.mkSt(fa, p2), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.EOther{Norm.Idle{_}}, PT.mkTOuts(fa, pt, xt), e))
      seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.pump(0n, Norm.Idle{S.mkSt(fa, p2)}), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), hts, he,
        BS.idle_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, p2, BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), wf2, bi2, ab2), hWa)
    case _ Norm.Ended{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      +ab2 = AB.subst(Norm.St, z => {Nat.is_le(BN.WAS(fa, z, List.append(&2, String, PT.texts(pt), cs)), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa)) == True{} : Bool}, st, S.mkSt(fa, p2), est, ab)
      +bi2 = AB.subst(Norm.St, z => {BN.biS(z, List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}, st, S.mkSt(fa, p2), est, abi)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(g, n0, W.EOther{Norm.Ended{_}}, PT.mkTOuts(fa, pt, xt), e))
      seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.pump(0n, Norm.Ended{S.mkSt(fa, p2)}), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), hts, he,
        BS.bud_mono(fa, T, List.append(&2, String, PT.texts(pt), cs), O, BN.WAS(fa, S.mkSt(fa, p2), List.append(&2, String, PT.texts(pt), cs)), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), Norm.finish(S.mkSt(fa, p2)), BS.fin_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, p2, wf2, bi2), ab2), hWa)
    case _ Norm.Yield{st}:
      seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.pump(0n, Norm.Yield{st}), BDs.WP(fa, List.append(&2, String, PT.texts(pt), cs), pa), hts, he,
        BS.yield_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, pa, st, hwa, ab, abi), hWa)

# The batch's end
# ===============

law comb_end:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}
  ST.BudW(fa, T, cs, ef, O, Nat.add(ST.VQ(T, cs, False{}, O, BDs.WP(fa, cs, p)), BD.XK(cs)), W.comb.end(e, S.mkSt(fa, p)))

def comb_end(fa, T, cs, O, N, ef, p, e, hb, hm, hg, hr, he, hbi):
  match e:
    case False{}:
      +W0 = BDs.WP(fa, cs, p)
      %Equal.sym(Bool, ef, False{}, he) : ST.BudW(fa, T, cs, _, O, Nat.add(ST.VQ(T, cs, False{}, O, W0), BD.XK(cs)), W.wrap(Norm.out(S.mkSt(fa, p), Pr.More{}), W.BNone{}))
      ST.wrap_none(fa, T, cs, False{}, O, W0, Norm.out(S.mkSt(fa, p), Pr.More{}), BS.out_bud(fa, T, cs, O, p, Pr.More{}, W0, hbi, N.le_refl(W0)))
    case True{}:
      (h1, +h2) = he
      %Equal.sym(Bool, ef, True{}, h1) : ST.BudW(fa, T, cs, _, O, Nat.add(ST.VQ(T, cs, False{}, O, BDs.WP(fa, cs, p)), BD.XK(cs)), W.wrap(Norm.step(S.mkSt(fa, p), Pr.Eof{}), W.BNone{}))
      %Equal.sym(List<&2, String>, cs, Nil{}, h2) : ST.BudW(fa, T, _, True{}, O, Nat.add(ST.VQ(T, _, False{}, O, BDs.WP(fa, _, p)), BD.XK(_)), W.wrap(Norm.step(S.mkSt(fa, p), Pr.Eof{}), W.BNone{}))
      +W0 = BDs.WP(fa, Nil{}, p)
      +hr0 = AB.subst(List<&2, String>, z => {S.report(fa, z, O, N, p) == T : R.Report}, cs, Nil{}, h2, hr)
      +hbi0 = AB.subst(List<&2, String>, z => {BN.biS(S.mkSt(fa, p), z) == True{} : Bool}, cs, Nil{}, h2, hbi)
      +Z = Nat.add(2n, Nat.add(BN.HO(T, O), W0))
      ST.budw_mono(fa, T, Nil{}, True{}, O, Nat.add(ST.VQ(T, Nil{}, True{}, O, W0), 0n), Nat.add(ST.VQ(T, Nil{}, False{}, O, W0), 0n), W.wrap(Norm.step(S.mkSt(fa, p), Pr.Eof{}), W.BNone{}),
        ST.wrap_none(fa, T, Nil{}, True{}, O, W0, Norm.step(S.mkSt(fa, p), Pr.Eof{}),
          BS.fed_bud(fa, T, Nil{}, O, N, W0, Norm.feed_eof(S.mkSt(fa, p)), hb, BS.eof_fed(fa, T, O, N, p, hb, hm, hr0, hg, hbi0))),
        N.le_add_mono_r(0n, Z, 1n+Z, N.le_add_l(Z, 1n)))

# A dirty piece: Q's step on it.
law comb_dirty:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report}
  for +hbi: {BN.biS(S.mkSt(fa, p), c <> List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.seq_out(Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)}), PT.mkTOuts(fa, pt, xt), e))

def comb_dirty(fa, T, cs, O, N, ef, p, c, pt, xt, e, len, t, d, hb, hm, hg, hr, hbi, hok, hv, hts, he):
  +W0 = BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p)
  seq_any(fa, T, cs, O, ef, p, c, pt, xt, e, Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)}), W0, hts, he,
    BS.fed_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, W0, Norm.feed(S.mkSt(fa, p), C.BT(len, t)), hb, FD.fedg_bt(fa, T, c, List.append(&2, String, PT.texts(pt), cs), O, N, p, len, t, d, hb, hm, hr, hg, hbi, hok, hv)),
    N.le_refl(W0))

# A clean piece: fed without room, then the edge.
law comb_clean.k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  for fg: BDs.FedG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, BDs.WP(fa, c <> List.append(&2, String, PT.texts(pt), cs), p), W.feed_line(S.mkSt(fa, p), C.BT(len, t)))
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(3n, QB.nbm(S.StP.md(p)), W.edge.of(Norm.advance(W.feed_line(S.mkSt(fa, p), C.BT(len, t))), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, QB.nbm(S.StP.md(p))), PT.mkTOuts(fa, pt, xt), e))

def comb_clean.k(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, len, t, hb, hm, hc, hn, hT, hts, he, fg):
  (+p1, f1) = fg
  (+e1, f2) = f1
  (+hw1, f3) = f2
  (+hr1, f4) = f3
  (+hg1, f5) = f4
  (+ha1, f6) = f5
  (+hW1, hbi0) = f6
  +hbi1 = Equal.trans(Bool, BN.biS(S.mkSt(fa, p1), List.append(&2, String, PT.texts(pt), cs)), True{}, True{}, hbi0, {==})
  +n0 = QB.nbm(S.StP.md(p))
  %Equal.sym(Norm.St, W.feed_line(S.mkSt(fa, p), C.BT(len, t)), S.mkSt(fa, p1), e1) :
    ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.edge(3n, n0, W.edge.of(Norm.advance(_), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
  edge_bud(3n, fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, n0, p1, Norm.advance(S.mkSt(fa, p1)), hb, hm, hc, hn, hT, hts, hw1, hr1, ha1, hg1, hbi1, hW1,
    SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, p1, hb, hw1, hr1, hg1), BS.adv_bud(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, p1, hb, hw1, hr1, hg1, ha1, hbi1), BS.adv_bi(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, p1, hb, hw1, hr1, hg1, ha1, hbi1), he)

law comb_clean:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +c: String
  for +rs: List<&2, Pr.Req>
  for +k: U32
  for +c0: String
  for +l: Nat
  for +a: String
  for +rpT: P.RunP
  for +pdT: P.PdP
  for +wpT: PC.WP
  for +ls: List<&2, B.Line>
  for +pt: List<&2, PT.Pc>
  for +xt: List<&2, PT.TOutP>
  for +e: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report}
  for +hbi: {BN.biS(S.mkSt(fa, p), c <> List.append(&2, String, PT.texts(pt), cs)) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>}
  for +hts: {BD.tots(PT.mkTOuts(fa, pt, xt)) == PT.texts(pt) : List<&2, String>}
  for he: WD.EofOK(e, ef, cs)
  ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.next(PT.mkTOuts(fa, PT.Pc{c, rs, True{}, k, c0, l} <> pt, PT.TOutP{len, t, d, PT.TCleanP{PT.TcP{rpT, pdT, wpT}}} <> xt), S.mkSt(fa, p), e))

def comb_clean(fa, T, cs, O, N, ef, p, c, rs, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, len, t, d, hb, hm, hg, hr, hbi, hok, hv, hc, hn, hT, hts, he):
  %QB.qn_mk(fa, p) : ST.BudW(fa, T, cs, ef, O, VCc(fa, T, cs, O, p, c, List.append(&2, String, PT.texts(pt), cs)), W.comb.clean(_, C.BT(len, t), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e))
  comb_clean.k(fa, T, cs, O, N, ef, p, c, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, len, t, hb, hm, hc, hn, hT, hts, he,
    FD.fedg_line(fa, T, c, List.append(&2, String, PT.texts(pt), cs), O, N, p, len, t, d, hm, hr, hg, hbi, hok, hv))

law comb_bud:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hst: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for hbo: PT.BatchOK(fa, S.StP.o(p), ps, xs, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hbi: {BN.biS(S.mkSt(fa, p), List.append(&2, String, PT.texts(ps), cs)) == True{} : Bool}
  ST.BudW(fa, T, cs, ef, O, Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(ps), cs), False{}, O, BDs.WP(fa, List.append(&2, String, PT.texts(ps), cs), p)), BD.XK(cs)), W.comb.next(PT.mkTOuts(fa, ps, xs), S.mkSt(fa, p), e))

def comb_bud(fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hst, hg, hr, hby, hps, hbo, he, hbi):
  match ps xs:
    case Nil{} Nil{}:
      comb_end(fa, T, cs, O, N, ef, p, e, hb, hm, hg, hr, he, hbi)
    case Nil{} Con{+x, +xt}:
      comb_end(fa, T, cs, O, N, ef, p, e, hb, hm, hg, hr, he, hbi)
    case Con{PT.Pc{+c, +rs, +ok, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TDirtyP{}}, +xt}:
      (h1, h2) = hbo
      (+hok, i1) = h1
      (+hv, i2) = i1
      comb_dirty(fa, T, cs, O, N, ef, p, c, pt, xt, e, len, t, d, hb, hm, hg, hr, hbi, hok, hv, LI.tots_mk(fa, S.StP.o(p), pt, xt, cs, h2), he)
    case Con{PT.Pc{+c, +rs, True{}, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TCleanP{PT.TcP{+rpT, +pdT, +wpT}}}, +xt}:
      (hp0, hps2) = hps
      (a1, q1) = hp0
      (a2, q2) = q1
      (a3, q3) = q2
      (a4, q4) = q3
      (+a, q5) = q4
      (hc, hn) = q5
      (h1, h2) = hbo
      (+hok, i1) = h1
      (+hv, hres) = i1
      (inv, j1) = hres
      (+ls, j2) = j1
      (hT, hset) = j2
      comb_clean(fa, T, cs, O, N, ef, p, c, rs, k, c0, l, a, rpT, pdT, wpT, ls, pt, xt, e, len, t, d, hb, hm, hg, hr, hbi, hok, hv, hc, hn, hT, LI.tots_mk(fa, S.StP.o(p), pt, xt, cs, h2), he)
    case Con{PT.Pc{+c, +rs, False{}, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TCleanP{+x}}, +xt}:
      (h1, h2) = hbo
      (hok, i1) = h1
      (hv, hres) = i1
      Empty.absurd(ST.BudW(fa, T, cs, ef, O, Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(PT.Pc{c, rs, False{}, k, c0, l} <> pt), cs), False{}, O, BDs.WP(fa, List.append(&2, String, PT.texts(PT.Pc{c, rs, False{}, k, c0, l} <> pt), cs), p)), BD.XK(cs)), W.comb.next(PT.mkTOuts(fa, PT.Pc{c, rs, False{}, k, c0, l} <> pt, PT.TOutP{len, t, d, PT.TCleanP{x}} <> xt), S.mkSt(fa, p), e)), hres)
    case Con{+p0, +pt} Nil{}:
      Empty.absurd(ST.BudW(fa, T, cs, ef, O, Nat.add(ST.VQ(T, List.append(&2, String, PT.texts(p0 <> pt), cs), False{}, O, BDs.WP(fa, List.append(&2, String, PT.texts(p0 <> pt), cs), p)), BD.XK(cs)), W.comb.next(PT.mkTOuts(fa, p0 <> pt, Nil{}), S.mkSt(fa, p), e)), hbo)
