import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_chunk.bend as DC
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_defs.bend as SD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_comb.bend as WC
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-halves/halves.bend as HH

# Helpers for proof_e_wrap.bend (area E1): no batch (a piece starts one or
# goes to Q), collecting, and a complete batch's plan (its Ask, or its tasks
# at once when it has no reads).

# Lists and bytes
# ===============

law and_mk:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {a && b == True{} : Bool}

def and_mk(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {_ && b == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {True{} && _ == True{} : Bool}
  {==}

# The pieces held are bytes, each at most 2^31: one more at the end.
law bp_snoc:
  for +xs: List<&2, String>
  for +c: String
  for +h: {E.all_bytes(xs) && E.pieces_ok(xs) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  {E.all_bytes(List.append(&2, String, xs, [c])) && E.pieces_ok(List.append(&2, String, xs, [c])) == True{} : Bool}

def bp_snoc(xs, c, h, hcb, hcn):
  match xs:
    case Nil{}:
      and_mk(E.all_bytes([c]), E.pieces_ok([c]), and_mk(E.is_bytes(c), True{}, hcb, {==}), and_mk(E.le31(String.length(c)), True{}, hcn, {==}))
    case Con{+x, +t}:
      +ha = PB.and_true_l(E.all_bytes(x <> t), E.pieces_ok(x <> t), h)
      +hp = PB.and_true_r(E.all_bytes(x <> t), E.pieces_ok(x <> t), h)
      +hx = PB.and_true_l(E.is_bytes(x), E.all_bytes(t), ha)
      +ht = PB.and_true_r(E.is_bytes(x), E.all_bytes(t), ha)
      +lx = PB.and_true_l(E.le31(String.length(x)), E.pieces_ok(t), hp)
      +lt = PB.and_true_r(E.le31(String.length(x)), E.pieces_ok(t), hp)
      +ih = bp_snoc(t, c, and_mk(E.all_bytes(t), E.pieces_ok(t), ht, lt), hcb, hcn)
      +ta = List.append(&2, String, t, [c])
      and_mk(E.is_bytes(x) && E.all_bytes(ta), E.le31(String.length(x)) && E.pieces_ok(ta),
        and_mk(E.is_bytes(x), E.all_bytes(ta), hx, PB.and_true_l(E.all_bytes(ta), E.pieces_ok(ta), ih)),
        and_mk(E.le31(String.length(x)), E.pieces_ok(ta), lx, PB.and_true_r(E.all_bytes(ta), E.pieces_ok(ta), ih)))

law rev_acc:
  for +xs: List<&2, String>
  for +acc: List<&2, String>
  {List.reverse.go(&2, String, xs, acc) == List.append(&2, String, List.reverse.go(&2, String, xs, Nil{}), acc) : List<&2, String>}

def rev_acc(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +Rv = List.reverse.go(&2, String, t, Nil{})
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, t, y <> acc), List.append(&2, String, Rv, y <> acc), List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc),
        rev_acc(t, y <> acc),
        Equal.sym(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, Rv, y <> acc),
          Equal.trans(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, List.append(&2, String, Rv, [y]), acc), List.append(&2, String, Rv, y <> acc),
            Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, acc), List.reverse.go(&2, String, t, [y]), List.append(&2, String, Rv, [y]), rev_acc(t, [y])),
            PB.append_assoc(String, Rv, [y], acc))))

# The pieces held, newest first, with one more: in file order, before cs.
law rev_cons_app:
  for +c: String
  for +hs: List<&2, String>
  for +cs: List<&2, String>
  {List.append(&2, String, List.reverse(&2, String, c <> hs), cs) == List.append(&2, String, List.reverse(&2, String, hs), c <> cs) : List<&2, String>}

def rev_cons_app(c, hs, cs):
  +Rv = List.reverse.go(&2, String, hs, Nil{})
  Equal.trans(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, hs, [c]), cs), List.append(&2, String, List.append(&2, String, Rv, [c]), cs), List.append(&2, String, Rv, c <> cs),
    Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, cs), List.reverse.go(&2, String, hs, [c]), List.append(&2, String, Rv, [c]), rev_acc(hs, [c])),
    PB.append_assoc(String, Rv, [c], cs))

law nil_of_empty:
  for +xs: List<&2, Pr.Req>
  for +h: {List.is_empty(&2, Pr.Req, xs) == True{} : Bool}
  {xs == Nil{} : List<&2, Pr.Req>}

def nil_of_empty(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({x <> t == Nil{} : List<&2, Pr.Req>}, PB.false_ne_true(h))

# The options' arguments are bytes (WF's last test).
law wf_args:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  {E.all_bytes(S.opts_args(S.StP.o(p))) == True{} : Bool}

def wf_args(fa, p, hw):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)

law wf_more:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  {S.WF(fa, p) == True{} : Bool}

def wf_more(fa, p, hm):
  WB.mo_w(S.WF(fa, p), S.src_empty(S.StP.src(p)), Bool.not(S.StP.eof(p)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p)), hm)

# The end of a step (Q.out) into a batch
# ======================================

# ... collecting hs (newest first, k of them).
law out_col:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for s: Norm.Step
  for og: DO.OutG(fa, List.append(&2, String, List.reverse(&2, String, hs), cs), O, N, p, Pr.More{}, s)
  for +hT: {S.report(fa, List.append(&2, String, List.reverse(&2, String, hs), cs), O, N, p) == T : R.Report}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hk: {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}
  for +hst: {WB.st_stop(WB.step_st(s)) == False{} : Bool}
  WD.StepGW(fa, T, cs, O, N, False{}, W.wrap(s, W.BCol{PT.encs(hs), k}))

def out_col(fa, T, cs, O, N, p, hs, k, s, og, hT, hm, hby, hk, hst):
  match s:
    case Norm.Step{st, b, ns, Pr.More{}}:
      (+t, og1) = og
      (+p2, og2) = og1
      (eout, og3) = og2
      (+est, og4) = og3
      (+wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      (+esrc, og8) = og7
      (+eeof, og9) = og8
      (+eask, og10) = og9
      (emode, eg) = og10
      +CS = List.append(&2, String, List.reverse(&2, String, hs), cs)
      (t, (WD.WPic{p2, WD.BColP{hs, k}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BCol{PT.encs(hs), k}}, st, S.mkSt(fa, p2), est),
        (hby, (eg, (Equal.trans(R.Report, S.report(fa, CS, String.append(O, t), List.append(&2, B.Note, N, ns), p2), S.report(fa, CS, O, N, p), T, erep, hT),
        ({==}, (WB.more_keep(fa, p, p2, hm, wf, esrc, eeof, eask), (WB.stop_pic(fa, p2, st, est, hst), ({==}, hk)))))))))))
    case Norm.Step{st, b, ns, Pr.Ask{rs}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, False{}, W.wrap(Norm.Step{st, b, ns, Pr.Ask{rs}}, W.BCol{PT.encs(hs), k})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_more(z), Pr.Ask{rs}, Pr.More{}, enx)))
    case Norm.Step{st, b, ns, Pr.Finish{c}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, False{}, W.wrap(Norm.Step{st, b, ns, Pr.Finish{c}}, W.BCol{PT.encs(hs), k})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_more(z), Pr.Finish{c}, Pr.More{}, enx)))

# ... waiting for the answers to the planned pieces' reads.
law out_askb:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for s: Norm.Step
  for og: DO.OutG(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p, Pr.Ask{PT.reqs_of(ps)}, s)
  for +hT: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for +hq: {E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hst: {WB.st_stop(WB.step_st(s)) == False{} : Bool}
  WD.StepGW(fa, T, cs, O, N, ef, W.wrap(s, W.BAsk{PT.mkPls(ps), e}))

def out_askb(fa, T, cs, O, N, ef, p, ps, e, s, og, hT, hm, hby, hq, hps, he, hst):
  match s:
    case Norm.Step{st, b, ns, Pr.Ask{+rs}}:
      (+t, og1) = og
      (+p2, og2) = og1
      (eout, og3) = og2
      (+est, og4) = og3
      (+wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      (+esrc, og8) = og7
      (+eeof, og9) = og8
      (+eask, og10) = og9
      (emode, eg) = og10
      +CS = List.append(&2, String, PT.texts(ps), cs)
      (t, (WD.WPic{p2, WD.BAskP{ps, e}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BAsk{PT.mkPls(ps), e}}, st, S.mkSt(fa, p2), est),
        (hby, (eg, (Equal.trans(R.Report, S.report(fa, CS, String.append(O, t), List.append(&2, B.Note, N, ns), p2), S.report(fa, CS, O, N, p), T, erep, hT),
        (enx, (WB.more_keep(fa, p, p2, hm, wf, esrc, eeof, eask), (WB.stop_pic(fa, p2, st, est, hst), (hq, (hps, he))))))))))))
    case Norm.Step{st, b, ns, Pr.More{}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.wrap(Norm.Step{st, b, ns, Pr.More{}}, W.BAsk{PT.mkPls(ps), e})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{PT.reqs_of(ps)}, enx)))
    case Norm.Step{st, b, ns, Pr.Finish{c}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.wrap(Norm.Step{st, b, ns, Pr.Finish{c}}, W.BAsk{PT.mkPls(ps), e})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.Finish{c}, Pr.Ask{PT.reqs_of(ps)}, enx)))

# A complete batch
# ================

law reqs_nil_tasks:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +hz: {PT.reqs_of(ps) == Nil{} : List<&2, Pr.Req>}
  for +eall: {HH.all(&1, W.TOut, W.tasks(o, PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
  {HH.all(&1, W.TOut, W.tasks(o, PT.mkPls(ps), W.pairs(Nil{}))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}

def reqs_nil_tasks(fa, o, ps, xs, hz, eall):
  %hz : {HH.all(&1, W.TOut, W.tasks(o, PT.mkPls(ps), W.pairs(M.truths(fa, _)))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
  eall

# No reads: the tasks run in this step and the combine starts.
law plan_run2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hz: {PT.reqs_of(ps) == Nil{} : List<&2, Pr.Req>}
  for bt: &xs: List<&2, PT.TOutP> -> ({HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
    & PT.BatchOK(fa, S.StP.o(p), ps, xs, cs))
  WD.StepGW(fa, T, cs, O, N, ef, W.ask.run((S.mkSt(fa, p), S.StP.o(p)), PT.mkPls(ps), Nil{}, e))

def plan_run2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, hps, he, hz, bt):
  (+xs, bt1) = bt
  (eall, hbo) = bt1
  +o = S.StP.o(p)
  %Equal.sym(List<&1, W.TOut>, HH.all(&1, W.TOut, W.tasks(o, PT.mkPls(ps), W.pairs(Nil{}))), PT.mkTOuts(fa, ps, xs), reqs_nil_tasks(fa, o, ps, xs, hz, eall)) :
    WD.StepGW(fa, T, cs, O, N, ef, W.comb.next(_, S.mkSt(fa, p), e))
  WC.comb_next_ok(fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hl, hg, hr, hby, hps, hbo, he)

# A copy of the plan's guarantee (every part is an equality or a String).
law pc_mk:
  for +rs: List<&2, Pr.Req>
  for +c: String
  for +k: U32
  for +c0: String
  for +X: String
  for +a: String
  for +h1: {PT.rs_ok(rs) && PT.two(rs) == True{} : Bool}
  for +h0: {E.is_bytes(c0) == True{} : Bool}
  for +h2: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), X))) == Some{c0} : Maybe<&2, String>}
  for +h3: {U32.is_lt((k + 1 : U32), U32.from_nat(String.length(c))) == True{} : Bool}
  for +e: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +n: {P.nolf(a) == True{} : Bool}
  ({PT.rs_ok(rs) && PT.two(rs) == True{} : Bool} & ({E.is_bytes(c0) == True{} : Bool} & ({SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), X))) == Some{c0} : Maybe<&2, String>}
    & ({U32.is_lt((k + 1 : U32), U32.from_nat(String.length(c))) == True{} : Bool} & (&a: String -> ({c == String.append(a, String.append("\n", PT.after(c, k))) : String} & {P.nolf(a) == True{} : Bool}))))))
  & ({PT.rs_ok(rs) && PT.two(rs) == True{} : Bool} & ({E.is_bytes(c0) == True{} : Bool} & ({SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), X))) == Some{c0} : Maybe<&2, String>}
    & ({U32.is_lt((k + 1 : U32), U32.from_nat(String.length(c))) == True{} : Bool} & (&a: String -> ({c == String.append(a, String.append("\n", PT.after(c, k))) : String} & {P.nolf(a) == True{} : Bool}))))))

def pc_mk(rs, c, k, c0, X, a, h1, h0, h2, h3, e, n):
  ((h1, (h0, (h2, (h3, (a, (e, n)))))), (h1, (h0, (h2, (h3, (a, (e, n)))))))

law eq_dup:
  for +rs: List<&2, Pr.Req>
  for +h: {rs == Nil{} : List<&2, Pr.Req>}
  {rs == Nil{} : List<&2, Pr.Req>} & {rs == Nil{} : List<&2, Pr.Req>}

def eq_dup(rs, h):
  (h, h)

law pc_dup:
  for +p: PT.Pc
  for +X: String
  for h: PT.PcOK(p, X)
  PT.PcOK(p, X) & PT.PcOK(p, X)

def pc_dup(p, X, h):
  match p:
    case PT.Pc{+c, +rs, True{}, +k, +c0, +l}:
      (+h1, r0) = h
      (+h0, r1) = r0
      (+h2, r2) = r1
      (+h3, r3) = r2
      (+a, r4) = r3
      (e, n) = r4
      pc_mk(rs, c, k, c0, X, a, h1, h0, h2, h3, e, n)
    case PT.Pc{+c, +rs, False{}, +k, +c0, +l}:
      eq_dup(rs, h)

law pcs_two:
  for +p: PT.Pc
  for +t: List<&2, PT.Pc>
  for +dcs: List<&2, String>
  for hp: PT.PcOK(p, String.concat(List.append(&2, String, PT.texts(t), dcs))) & PT.PcOK(p, String.concat(List.append(&2, String, PT.texts(t), dcs)))
  for ht: PT.PcsOK(t, dcs) & PT.PcsOK(t, dcs)
  PT.PcsOK(p <> t, dcs) & PT.PcsOK(p <> t, dcs)

def pcs_two(p, t, dcs, hp, ht):
  (a1, a2) = hp
  (b1, b2) = ht
  ((a1, b1), (a2, b2))

law pcs_dup:
  for +ps: List<&2, PT.Pc>
  for +dcs: List<&2, String>
  for h: PT.PcsOK(ps, dcs)
  PT.PcsOK(ps, dcs) & PT.PcsOK(ps, dcs)

def pcs_dup(ps, dcs, h):
  match ps:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+p, +t}:
      (hp, ht) = h
      pcs_two(p, t, dcs, pc_dup(p, String.concat(List.append(&2, String, PT.texts(t), dcs)), hp), pcs_dup(t, dcs, ht))

law plan_run:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hd: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hz: {PT.reqs_of(ps) == Nil{} : List<&2, Pr.Req>}
  WD.StepGW(fa, T, cs, O, N, ef, W.ask.run((S.mkSt(fa, p), S.StP.o(p)), PT.mkPls(ps), Nil{}, e))

def plan_run(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, hd, he, hz):
  (h1, h2) = hd
  plan_run2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, h2, he, hz,
    PT.batch(fa, S.StP.o(p), ps, cs, hb, wf_args(fa, p, wf_more(fa, p, hm)), hby, h1))

# The plan's choice: an Ask for the reads, or (none) the tasks at once.
law plan_go_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +z: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for +hq: {E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for +hz: {List.is_empty(&2, Pr.Req, PT.reqs_of(ps)) == z : Bool}
  WD.StepGW(fa, T, cs, O, N, ef, W.plan.go(z, S.mkSt(fa, p), PT.mkPls(ps), PT.reqs_of(ps), e))

def plan_go_k(fa, T, cs, O, N, ef, p, ps, e, z, hb, hm, hl, hg, hr, hby, hq, hps, he, hz):
  match z:
    case False{}:
      out_askb(fa, T, cs, O, N, ef, p, ps, e, Norm.out(S.mkSt(fa, p), Pr.Ask{PT.reqs_of(ps)}),
        DO.out_ok(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p, Pr.Ask{PT.reqs_of(ps)}, wf_more(fa, p, hm), hg, DO.live_of(S.StP.md(p), hl)),
        hr, hm, hby, hq, hps, he, WB.out_stop(fa, p, Pr.Ask{PT.reqs_of(ps)}, hl))
    case True{}:
      %WB.opts_mk(fa, p) : WD.StepGW(fa, T, cs, O, N, ef, W.ask.run(_, PT.mkPls(ps), Nil{}, e))
      plan_run(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, pcs_dup(ps, cs, hps), he, nil_of_empty(PT.reqs_of(ps), hz))

# The plan, with its pieces ps (texts hs2).
law plan_texts:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +hs2: List<&2, String>
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, hs2, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(hs2) && E.pieces_ok(hs2) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  for +eplan: {W.plan.reqs_all(W.plan.all(PT.encs(hs2))) == (PT.mkPls(ps), PT.reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
  for +etx: {PT.texts(ps) == hs2 : List<&2, String>}
  for +hq: {E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.plan(S.mkSt(fa, p), PT.encs(hs2), e))

def plan_texts(fa, T, cs, O, N, ef, p, hs2, ps, e, hb, hm, hl, hg, hr, hby, he, eplan, etx, hq, hps):
  %Equal.sym(List<&1, W.Pl> & List<&2, Pr.Req>, W.plan.reqs_all(W.plan.all(PT.encs(hs2))), (PT.mkPls(ps), PT.reqs_of(ps)), eplan) :
    WD.StepGW(fa, T, cs, O, N, ef, W.plan.ask(S.mkSt(fa, p), _, e))
  +hr2 = Equal.trans(R.Report, S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p), S.report(fa, List.append(&2, String, hs2, cs), O, N, p), T,
    Equal.cong(List<&2, String>, R.Report, z => S.report(fa, List.append(&2, String, z, cs), O, N, p), PT.texts(ps), hs2, etx), hr)
  +hby2 = Equal.trans(Bool, E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)), E.all_bytes(hs2) && E.pieces_ok(hs2), True{},
    Equal.cong(List<&2, String>, Bool, z => E.all_bytes(z) && E.pieces_ok(z), PT.texts(ps), hs2, etx), hby)
  plan_go_k(fa, T, cs, O, N, ef, p, ps, e, List.is_empty(&2, Pr.Req, PT.reqs_of(ps)), hb, hm, hl, hg, hr2, hby2, hq, hps, he, {==})

# A complete batch (hs2 in file order): its reads are asked, or its tasks run.
law plan_sig:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +hs2: List<&2, String>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, hs2, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(hs2) && E.pieces_ok(hs2) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  for pa: &ps: List<&2, PT.Pc> -> ({W.plan.reqs_all(W.plan.all(PT.encs(hs2))) == (PT.mkPls(ps), PT.reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({PT.texts(ps) == hs2 : List<&2, String>} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & PT.PcsOK(ps, cs))))
  WD.StepGW(fa, T, cs, O, N, ef, W.plan(S.mkSt(fa, p), PT.encs(hs2), e))

def plan_sig(fa, T, cs, O, N, ef, p, hs2, e, hb, hm, hl, hg, hr, hby, he, pa):
  (+ps, pa1) = pa
  (+eplan, pa2) = pa1
  (+etx, pa3) = pa2
  (+hq, hps) = pa3
  plan_texts(fa, T, cs, O, N, ef, p, hs2, ps, e, hb, hm, hl, hg, hr, hby, he, eplan, etx, hq, hps)

law plan_ok:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +hs2: List<&2, String>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, hs2, cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(hs2) && E.pieces_ok(hs2) == True{} : Bool}
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.plan(S.mkSt(fa, p), PT.encs(hs2), e))

def plan_ok(fa, T, cs, O, N, ef, p, hs2, e, hb, hm, hl, hg, hr, hby, he):
  plan_sig(fa, T, cs, O, N, ef, p, hs2, e, hb, hm, hl, hg, hr, hby, he,
    PT.plan_all(hs2, cs, PB.and_true_l(E.all_bytes(hs2), E.pieces_ok(hs2), hby), PB.and_true_r(E.all_bytes(hs2), E.pieces_ok(hs2), hby)))

# No batch: a piece
# =================

# A piece starts a batch (Q quiet, the piece long enough) or goes to Q.
law none_chunk_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +ok: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hok: {WB.qb(p) && U32.is_le(W.minp(), U32.from_nat(String.length(c))) == ok : Bool}
  WD.StepGW(fa, T, cs, O, N, False{}, W.none.chunk((S.mkSt(fa, p), ok), E.enc(c)))

def none_chunk_k(fa, T, c, cs, O, N, p, ok, hb, hm, hr, hcb, hcn, hg, hok):
  match ok:
    case False{}:
      WB.g2_none(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), DC.step_chunk_h2(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg))
    case True{}:
      +hl = WB.qb_stop(p, PB.and_true_l(WB.qb(p), U32.is_le(W.minp(), U32.from_nat(String.length(c))), hok))
      out_col(fa, T, cs, O, N, p, [c], 1n, Norm.out(S.mkSt(fa, p), Pr.More{}),
        DO.out_ok(fa, List.append(&2, String, List.reverse(&2, String, [c]), cs), O, N, p, Pr.More{}, wf_more(fa, p, hm), hg, DO.live_of(S.StP.md(p), hl)),
        hr, hm, and_mk(E.all_bytes([c]), E.pieces_ok([c]), and_mk(E.is_bytes(c), True{}, hcb, {==}), and_mk(E.le31(String.length(c)), True{}, hcn, {==})), {==},
        WB.out_stop(fa, p, Pr.More{}, hl))

law none_chunk:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  WD.StepGW(fa, T, cs, O, N, False{}, W.step(W.St{S.mkSt(fa, p), W.BNone{}}, Pr.Chunk{E.enc(c)}))

def none_chunk(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg):
  %WB.quiet_mk(fa, p) : WD.StepGW(fa, T, cs, O, N, False{}, W.none.len(_, BY.len(E.enc(c))))
  none_chunk_k(fa, T, c, cs, O, N, p, WB.qb(p) && U32.is_le(W.minp(), U32.from_nat(String.length(c))), hb, hm, hr, hcb, hcn, hg, {==})

# Collecting
# ==========

def col_add_go(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +hs: List<&2, String>, +k: Nat, +full: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hl: {S.stopped(S.StP.md(p)) == False{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hT: {S.report(fa, List.append(&2, String, List.reverse(&2, String, c <> hs), cs), O, N, p) == T : R.Report},
  +hby2: {E.all_bytes(List.reverse(&2, String, c <> hs)) && E.pieces_ok(List.reverse(&2, String, c <> hs)) == True{} : Bool},
  +hk: {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, False{}, W.col.add(full, S.mkSt(fa, p), E.enc(c) <> PT.encs(hs), 1n+k)):
  match full:
    case False{}:
      out_col(fa, T, cs, O, N, p, c <> hs, 1n+k, Norm.out(S.mkSt(fa, p), Pr.More{}),
        DO.out_ok(fa, List.append(&2, String, List.reverse(&2, String, c <> hs), cs), O, N, p, Pr.More{}, wf_more(fa, p, hm), hg, DO.live_of(S.StP.md(p), hl)),
        hT, hm, hby2, hk, WB.out_stop(fa, p, Pr.More{}, hl))
    case True{}:
      %Equal.sym(List<&1, D.Bytes>, W.rev_b(PT.encs(c <> hs), PT.encs(Nil{})), PT.encs(List.reverse.go(&2, String, c <> hs, Nil{})), WB.rev_encs(c <> hs, Nil{})) :
        WD.StepGW(fa, T, cs, O, N, False{}, W.plan(S.mkSt(fa, p), _, False{}))
      plan_ok(fa, T, cs, O, N, False{}, p, List.reverse(&2, String, c <> hs), False{}, hb, hm, hl, hg, hT, hby2, {==})

law col_add_k:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +full: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, List.reverse(&2, String, hs), c <> cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +hk: {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}
  for +hfull: {Nat.is_le(W.kmax(), 1n+k) || U32.is_lt(U32.from_nat(String.length(c)), W.minp()) == full : Bool}
  WD.StepGW(fa, T, cs, O, N, False{}, W.col.add(full, S.mkSt(fa, p), E.enc(c) <> PT.encs(hs), 1n+k))

def col_add_k(fa, T, c, cs, O, N, p, hs, k, full, hb, hm, hl, hg, hr, hby, hcb, hcn, hk, hfull):
  +RC = List.reverse(&2, String, c <> hs)
  +hT = Equal.trans(R.Report, S.report(fa, List.append(&2, String, RC, cs), O, N, p), S.report(fa, List.append(&2, String, List.reverse(&2, String, hs), c <> cs), O, N, p), T,
    Equal.cong(List<&2, String>, R.Report, z => S.report(fa, z, O, N, p), List.append(&2, String, RC, cs), List.append(&2, String, List.reverse(&2, String, hs), c <> cs), rev_cons_app(c, hs, cs)), hr)
  +RH = List.reverse.go(&2, String, hs, Nil{})
  +hby2 = Equal.trans(Bool, E.all_bytes(RC) && E.pieces_ok(RC), E.all_bytes(List.append(&2, String, RH, [c])) && E.pieces_ok(List.append(&2, String, RH, [c])), True{},
    Equal.cong(List<&2, String>, Bool, z => E.all_bytes(z) && E.pieces_ok(z), List.reverse.go(&2, String, hs, [c]), List.append(&2, String, RH, [c]), rev_acc(hs, [c])),
    bp_snoc(RH, c, hby, hcb, hcn))
  col_add_go(fa, T, c, cs, O, N, p, hs, k, full, hb, hm, hl, hg, hT, hby2, hk)

law col_eof:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hs: List<&2, String>
  for +k: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, List.reverse(&2, String, hs), Nil{}), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  WD.StepGW(fa, T, Nil{}, O, N, True{}, W.step(W.St{S.mkSt(fa, p), W.BCol{PT.encs(hs), k}}, Pr.Eof{}))

def col_eof(fa, T, O, N, p, hs, k, hb, hm, hl, hg, hr, hby):
  %Equal.sym(List<&1, D.Bytes>, W.rev_b(PT.encs(hs), PT.encs(Nil{})), PT.encs(List.reverse.go(&2, String, hs, Nil{})), WB.rev_encs(hs, Nil{})) :
    WD.StepGW(fa, T, Nil{}, O, N, True{}, W.plan(S.mkSt(fa, p), _, True{}))
  plan_ok(fa, T, Nil{}, O, N, True{}, p, List.reverse(&2, String, hs), True{}, hb, hm, hl, hg, hr, hby, ({==}, {==}))

# The answers to a batch's reads: its tasks run, the combine starts.
law ask_run2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  for bt: &xs: List<&2, PT.TOutP> -> ({HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))) == PT.mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
    & PT.BatchOK(fa, S.StP.o(p), ps, xs, cs))
  WD.StepGW(fa, T, cs, O, N, ef, W.ask.run((S.mkSt(fa, p), S.StP.o(p)), PT.mkPls(ps), M.truths(fa, PT.reqs_of(ps)), e))

def ask_run2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, hps, he, bt):
  (+xs, bt1) = bt
  (eall, hbo) = bt1
  %Equal.sym(List<&1, W.TOut>, HH.all(&1, W.TOut, W.tasks(S.StP.o(p), PT.mkPls(ps), W.pairs(M.truths(fa, PT.reqs_of(ps))))), PT.mkTOuts(fa, ps, xs), eall) :
    WD.StepGW(fa, T, cs, O, N, ef, W.comb.next(_, S.mkSt(fa, p), e))
  WC.comb_next_ok(fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hl, hg, hr, hby, hps, hbo, he)

law ask_ref2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hd: PT.PcsOK(ps, cs) & PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.ask.run((S.mkSt(fa, p), S.StP.o(p)), PT.mkPls(ps), M.truths(fa, PT.reqs_of(ps)), e))

def ask_ref2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, hd, he):
  (h1, h2) = hd
  ask_run2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, h2, he,
    PT.batch(fa, S.StP.o(p), ps, cs, hb, wf_args(fa, p, wf_more(fa, p, hm)), hby, h1))

law ask_ref:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +p: S.StP
  for +ps: List<&2, PT.Pc>
  for +e: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report}
  for +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  for hps: PT.PcsOK(ps, cs)
  for he: WD.EofOK(e, ef, cs)
  WD.StepGW(fa, T, cs, O, N, ef, W.step(W.St{S.mkSt(fa, p), W.BAsk{PT.mkPls(ps), e}}, Pr.Ref{M.truths(fa, PT.reqs_of(ps))}))

def ask_ref(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, hps, he):
  %WB.opts_mk(fa, p) : WD.StepGW(fa, T, cs, O, N, ef, W.ask.run(_, PT.mkPls(ps), M.truths(fa, PT.reqs_of(ps)), e))
  ask_ref2(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hr, hby, pcs_dup(ps, cs, hps), he)
