import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PRD
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drivedefs.bend as DR
import ./proof_base.bend as PB
import ./proof_e_defs.bend as SD
import ./proof_e_task.bend as PT
import ./proof_e_qif.bend as QI
import ./proof_e_qif_step.bend as QS
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_qx.bend as QX
import ./proof_e_wrap_ms.bend as WM
import ./proof_e_wrap_edge.bend as ED
import ./proof_e_wrap_fb.bend as FB
import ./proof_e_wrap_mc.bend as MC
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Helpers for proof_e_wrap.bend (area E1): a clean piece in the combine. Q
# is fed the piece without room (W.feed_line) and handles the line across
# the boundary: W.edge advances at most three times (fuel 3) until Q is at
# the piece's k+1 with its line count up by one (EHere), then the task's run
# is merged (proof_e_wrap_mc.bend's merge_case) or the piece goes to Q. Bend
# refuses mutual recursion, so the edge's four fuel levels E3 .. E0 are
# separate lemmas (generated: the same text with the level's fuel). Each
# level carries the fed state p1, the current state pc and the chain of
# Moved facts from p1 to pc (ED.Ch).

# W.edge.where on a picture: here (one byte source at k+1, the count up by
# one) and ok (nothing else waiting).
def here_s(+src: List<&2, P.SrcP>, +k: U32, +n: Nat, +n0: Nat) -> Bool:
  match src:
    case Con{P.SBP{len, t, d, +at}, Nil{}}:
      U32.is_eq(at, (k + 1 : U32)) && Nat.is_eq(n, 1n+n0)
    case _:
      False{}

def here_p(+p2: S.StP, +k: U32, +n0: Nat) -> Bool:
  match p2:
    case S.StP{o, +md, +src, pd, eof, back, wp, asked, fneed}:
      here_s(src, k, WB.nbm(md), n0)

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

law or_pic:
  for +fa: List<&2, B.Contig>
  for +pc: S.StP
  for +p2: S.StP
  for -st: Norm.St
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.st_ms(st)) == True{} : Bool}
  {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.is_msp(S.StP.md(p2))) == True{} : Bool}

def or_pic(fa, pc, p2, st, est, hk):
  match pc:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
    case S.StP{+o, S.MSP{+s, +qs, +ql, +cd}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      WM.ms_pic(fa, p2, st, est, hk)

law adv_or:
  for +fa: List<&2, B.Contig>
  for +pc: S.StP
  {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.adv_ms(Norm.advance(S.mkSt(fa, pc)))) == True{} : Bool}

def adv_or(fa, pc):
  match pc:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
    case S.StP{+o, S.MSP{+s, +qs, +ql, +cd}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      WM.adv_keep_ms(fa, S.StP{o, S.MSP{s, qs, ql, cd}, src, pd, eof, back, wp, asked, fneed}, {==})

def splice_ok(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +p2: S.StP,
  +hhere: {here_p(p2, k, n0) == True{} : Bool},
  +hok: {ok_p(p2) == True{} : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwp2: {S.WF(fa, p2) == True{} : Bool},
  +hrp2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +hgp2: {S.guard(O, N, p2) == True{} : Bool},
  +hap2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefp2: {S.StP.eof(p2) == False{} : Bool},
  +hop2: {S.StP.o(p2) == o : B.Opts},
  hchp2: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, p2)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)):
  match p2:
    case S.StP{+o2, S.MBP{+rp2}, Con{P.SBP{+len2, +t2, +d2, +at2}, Nil{}}, +pd2, False{}, +back2, +wp2, +asked2, +fneed2}:
      MC.merge_case(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, o2, rp2, len2, t2, d2, at2, pd2, back2, wp2, asked2, fneed2, p1, hb, hm, hwp2, hrp2, hap2, hgp2, hop2, PB.eq_sound(P.RunP.n(rp2), 1n+n0, PB.and_true_r(U32.is_eq(at2, (k + 1 : U32)), Nat.is_eq(P.RunP.n(rp2), 1n+n0), hhere)), hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hchp2)
    case S.StP{+o2, S.MBP{+rp2}, +src2, +pd2, True{}, +back2, +wp2, +asked2, +fneed2}:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, src2, pd2, True{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.true_ne_false(hefp2))
    case S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, +src2, +pd2, +eof2, +back2, +wp2, +asked2, +fneed2}:
      FB.go_seq(fa, T, cs, O, N, ef, o, S.StP{o2, S.MSP{s2, qs2, ql2, cd2}, src2, pd2, eof2, back2, wp2, asked2, fneed2}, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)
    case S.StP{+o2, S.MBP{+rp2}, Nil{}, +pd2, False{}, +back2, +wp2, +asked2, +fneed2}:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, Nil{}, pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.false_ne_true(hhere))
    case S.StP{+o2, S.MBP{+rp2}, Con{P.SBP{+len2, +t2, +d2, +at2}, Con{+sh, +st}}, +pd2, False{}, +back2, +wp2, +asked2, +fneed2}:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, Con{P.SBP{len2, t2, d2, at2}, Con{sh, st}}, pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.false_ne_true(hhere))
    case S.StP{+o2, S.MBP{+rp2}, Con{P.SLP{+sp}, +st}, +pd2, False{}, +back2, +wp2, +asked2, +fneed2}:
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.comb.splice(S.mkSt(fa, S.StP{o2, S.MBP{rp2}, Con{P.SLP{sp}, st}, pd2, False{}, back2, wp2, asked2, fneed2}), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)), PB.false_ne_true(hhere))


def E0_k(+here: Bool, +ok: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +p2: S.StP,
  +hhere: {here_p(p2, k, n0) == here : Bool},
  +hok: {ok_p(p2) == ok : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwp2: {S.WF(fa, p2) == True{} : Bool},
  +hrp2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +hgp2: {S.guard(O, N, p2) == True{} : Bool},
  +hap2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefp2: {S.StP.eof(p2) == False{} : Bool},
  +hop2: {S.StP.o(p2) == o : B.Opts},
  hchp2: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, p2)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(0n, n0, W.edge.where.if(here, ok, S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), PT.mkTOuts(fa, pt, xt), e)):
  match here ok:
    case True{} True{}:
      splice_ok(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hhere, hok, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)
    case True{} False{}:
      FB.go_seq(fa, T, cs, O, N, ef, o, p2, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)
    case False{} _:
      FB.go_seq(fa, T, cs, O, N, ef, o, p2, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)

def E0_a(av: Norm.Adv, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc),
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, av),
  +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.adv_ms(av)) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(0n, n0, W.edge.of(av, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  match av:
    case Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (+eask, a6) = a5
      (+eeof, a7) = a6
      (+eg, a8) = a7
      (+eo, mvk) = a8
      (mv, kp) = mvk
      ch2 = ED.ch_step(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc, p2, hchpc, mv, Equal.trans(B.Opts, S.StP.o(pc), o, S.StP.o(p1), hopc, Equal.sym(B.Opts, S.StP.o(p1), o, ho1)), or_pic(fa, pc, p2, st, est, hk))
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(fa, T, cs, O, N, ef, W.edge(0n, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.edge(0n, n0, _, PT.mkTOuts(fa, pt, xt), e))
      E0_k(here_p(p2, k, n0), ok_p(p2), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, {==}, {==}, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, wf2, er2, eg, eask, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefpc), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hopc), ch2)
    case Norm.Want{st, +r}:
      FB.want_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, r, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Idle{st}:
      FB.idle_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Ended{st}:
      FB.ended_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Yield{st}:
      FB.yield_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)

def E0(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(0n, n0, W.edge.of(Norm.advance(S.mkSt(fa, pc)), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  E0_a(Norm.advance(S.mkSt(fa, pc)), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, pc, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwpc, hrpc, hgpc, hapc, hefpc, hopc, hchpc, SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, hb, hwpc, hrpc, hgpc), adv_or(fa, pc))

def E1_k(+here: Bool, +ok: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +p2: S.StP,
  +hhere: {here_p(p2, k, n0) == here : Bool},
  +hok: {ok_p(p2) == ok : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwp2: {S.WF(fa, p2) == True{} : Bool},
  +hrp2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +hgp2: {S.guard(O, N, p2) == True{} : Bool},
  +hap2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefp2: {S.StP.eof(p2) == False{} : Bool},
  +hop2: {S.StP.o(p2) == o : B.Opts},
  hchp2: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, p2)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(1n, n0, W.edge.where.if(here, ok, S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), PT.mkTOuts(fa, pt, xt), e)):
  match here ok:
    case True{} True{}:
      splice_ok(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hhere, hok, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)
    case True{} False{}:
      FB.go_seq(fa, T, cs, O, N, ef, o, p2, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)
    case False{} _:
      E0(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)

def E1_a(av: Norm.Adv, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc),
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, av),
  +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.adv_ms(av)) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(1n, n0, W.edge.of(av, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  match av:
    case Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (+eask, a6) = a5
      (+eeof, a7) = a6
      (+eg, a8) = a7
      (+eo, mvk) = a8
      (mv, kp) = mvk
      ch2 = ED.ch_step(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc, p2, hchpc, mv, Equal.trans(B.Opts, S.StP.o(pc), o, S.StP.o(p1), hopc, Equal.sym(B.Opts, S.StP.o(p1), o, ho1)), or_pic(fa, pc, p2, st, est, hk))
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(fa, T, cs, O, N, ef, W.edge(1n, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.edge(1n, n0, _, PT.mkTOuts(fa, pt, xt), e))
      E1_k(here_p(p2, k, n0), ok_p(p2), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, {==}, {==}, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, wf2, er2, eg, eask, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefpc), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hopc), ch2)
    case Norm.Want{st, +r}:
      FB.want_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, r, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Idle{st}:
      FB.idle_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Ended{st}:
      FB.ended_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Yield{st}:
      FB.yield_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)

def E1(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(1n, n0, W.edge.of(Norm.advance(S.mkSt(fa, pc)), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  E1_a(Norm.advance(S.mkSt(fa, pc)), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, pc, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwpc, hrpc, hgpc, hapc, hefpc, hopc, hchpc, SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, hb, hwpc, hrpc, hgpc), adv_or(fa, pc))

def E2_k(+here: Bool, +ok: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +p2: S.StP,
  +hhere: {here_p(p2, k, n0) == here : Bool},
  +hok: {ok_p(p2) == ok : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwp2: {S.WF(fa, p2) == True{} : Bool},
  +hrp2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +hgp2: {S.guard(O, N, p2) == True{} : Bool},
  +hap2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefp2: {S.StP.eof(p2) == False{} : Bool},
  +hop2: {S.StP.o(p2) == o : B.Opts},
  hchp2: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, p2)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(2n, n0, W.edge.where.if(here, ok, S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), PT.mkTOuts(fa, pt, xt), e)):
  match here ok:
    case True{} True{}:
      splice_ok(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hhere, hok, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)
    case True{} False{}:
      FB.go_seq(fa, T, cs, O, N, ef, o, p2, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)
    case False{} _:
      E1(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)

def E2_a(av: Norm.Adv, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc),
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, av),
  +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.adv_ms(av)) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(2n, n0, W.edge.of(av, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  match av:
    case Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (+eask, a6) = a5
      (+eeof, a7) = a6
      (+eg, a8) = a7
      (+eo, mvk) = a8
      (mv, kp) = mvk
      ch2 = ED.ch_step(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc, p2, hchpc, mv, Equal.trans(B.Opts, S.StP.o(pc), o, S.StP.o(p1), hopc, Equal.sym(B.Opts, S.StP.o(p1), o, ho1)), or_pic(fa, pc, p2, st, est, hk))
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(fa, T, cs, O, N, ef, W.edge(2n, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.edge(2n, n0, _, PT.mkTOuts(fa, pt, xt), e))
      E2_k(here_p(p2, k, n0), ok_p(p2), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, {==}, {==}, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, wf2, er2, eg, eask, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefpc), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hopc), ch2)
    case Norm.Want{st, +r}:
      FB.want_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, r, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Idle{st}:
      FB.idle_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Ended{st}:
      FB.ended_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Yield{st}:
      FB.yield_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)

def E2(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(2n, n0, W.edge.of(Norm.advance(S.mkSt(fa, pc)), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  E2_a(Norm.advance(S.mkSt(fa, pc)), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, pc, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwpc, hrpc, hgpc, hapc, hefpc, hopc, hchpc, SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, hb, hwpc, hrpc, hgpc), adv_or(fa, pc))

def E3_k(+here: Bool, +ok: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +p2: S.StP,
  +hhere: {here_p(p2, k, n0) == here : Bool},
  +hok: {ok_p(p2) == ok : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwp2: {S.WF(fa, p2) == True{} : Bool},
  +hrp2: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p2) == T : R.Report},
  +hgp2: {S.guard(O, N, p2) == True{} : Bool},
  +hap2: {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefp2: {S.StP.eof(p2) == False{} : Bool},
  +hop2: {S.StP.o(p2) == o : B.Opts},
  hchp2: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, p2)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, W.edge.where.if(here, ok, S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), PT.mkTOuts(fa, pt, xt), e)):
  match here ok:
    case True{} True{}:
      splice_ok(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hhere, hok, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)
    case True{} False{}:
      FB.go_seq(fa, T, cs, O, N, ef, o, p2, pt, xt, e, hb, hwp2, hrp2, hap2, hgp2, hefp2, hop2, hby, hps, hbo, he)
    case False{} _:
      E2(fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwp2, hrp2, hgp2, hap2, hefp2, hop2, hchp2)

def E3_a(av: Norm.Adv, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc),
  ag: S.AdvG(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, av),
  +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.adv_ms(av)) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, W.edge.of(av, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  match av:
    case Norm.Went{st}:
      (+p2, a1) = ag
      (+est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (+eask, a6) = a5
      (+eeof, a7) = a6
      (+eg, a8) = a7
      (+eo, mvk) = a8
      (mv, kp) = mvk
      ch2 = ED.ch_step(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc, p2, hchpc, mv, Equal.trans(B.Opts, S.StP.o(pc), o, S.StP.o(p1), hopc, Equal.sym(B.Opts, S.StP.o(p1), o, ho1)), or_pic(fa, pc, p2, st, est, hk))
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, W.edge.where(_, W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
      %Equal.sym(W.Ew, W.edge.where(S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), W.edge.where.if(here_p(p2, k, n0), ok_p(p2), S.mkSt(fa, p2), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}), where_eq(fa, p2, rpT, pdT, wpT, k, c0, l, n0)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, _, PT.mkTOuts(fa, pt, xt), e))
      E3_k(here_p(p2, k, n0), ok_p(p2), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, p2, {==}, {==}, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, wf2, er2, eg, eask, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(pc), False{}, eeof, hefpc), Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(pc), o, eo, hopc), ch2)
    case Norm.Want{st, +r}:
      FB.want_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, r, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Idle{st}:
      FB.idle_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Ended{st}:
      FB.ended_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)
    case Norm.Yield{st}:
      FB.yield_seq(fa, T, cs, O, N, ef, o, pc, pt, xt, e, st, hapc, hefpc, hopc, hby, hps, hbo, he, ag)

def E3(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +o: B.Opts, +p: S.StP, +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +rpT: P.RunP, +pdT: P.PdP, +wpT: PC.WP, +lsT: List<&2, B.Line>, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool, +n0: Nat, +p1: S.StP, +pc: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rpT) && P.RunP.i(rpT) && Bool.not(P.RunP.x(rpT)) && P.pd_ok(pdT) && P.nolf(P.pdtext(pdT)) && PC.wp_ok(fa, wpT) && S.mb_win(S.MBP{rpT}, wpT) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pdT), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, o, SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, o, pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  +hint1: {S.intext(p1, List.append(&2, String, PT.texts(pt), cs)) == S.intext(p, c <> List.append(&2, String, PT.texts(pt), cs)) : String},
  +hn0: {n0 == WB.nbm(S.StP.md(p1)) : Nat},
  +ho1: {S.StP.o(p1) == o : B.Opts},
  +hwpc: {S.WF(fa, pc) == True{} : Bool},
  +hrpc: {S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, pc) == T : R.Report},
  +hgpc: {S.guard(O, N, pc) == True{} : Bool},
  +hapc: {S.StP.asked(pc) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hefpc: {S.StP.eof(pc) == False{} : Bool},
  +hopc: {S.StP.o(pc) == o : B.Opts},
  hchpc: ED.Ch(fa, List.append(&2, String, PT.texts(pt), cs), p1, pc)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, W.edge.of(Norm.advance(S.mkSt(fa, pc)), W.Tc{P.mkRun(rpT), P.mkPd(pdT), PC.mkWin(fa, wpT), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e)):
  E3_a(Norm.advance(S.mkSt(fa, pc)), fa, T, cs, O, N, ef, o, p, c, k, c0, l, a, rpT, pdT, wpT, lsT, pt, xt, e, n0, p1, pc, hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hint1, hn0, ho1, hwpc, hrpc, hgpc, hapc, hefpc, hopc, hchpc, SA.adv_ok(fa, T, List.append(&2, String, PT.texts(pt), cs), O, N, pc, hb, hwpc, hrpc, hgpc), adv_or(fa, pc))


# The piece fed (feed_line's fed state p1), then the edge from it.
def clean2(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP,
  +c: String, +k: U32, +c0: String, +l: Nat, +a: String, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +rp: P.RunP, +pd: P.PdP, +wp: PC.WP, +lsT: List<&2, B.Line>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report},
  +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String},
  +hna: {P.nolf(a) == True{} : Bool},
  +hfc0: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs))))) == Some{c0} : Maybe<&2, String>},
  +hT7: {PRD.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pd), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rp)) == P.settle(L.run.go(lsT, fa, S.StP.o(p), SD.rs0(c0, l))) : R.RunSt},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, S.StP.o(p), pt, xt, cs),
  he: WD.EofOK(e, ef, cs),
  fl: &p1: S.StP -> ({W.feed_line(S.mkSt(fa, p), C.BT(len, t)) == S.mkSt(fa, p1) : Norm.St}
    & ({S.WF(fa, p1) == True{} : Bool} & ({S.StP.md(p1) == S.StP.md(p) : S.MdP} & ({S.StP.o(p1) == S.StP.o(p) : B.Opts}
    & ({S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>} & ({S.StP.eof(p1) == False{} : Bool}
    & (@cs2: List<&2, String> -> {S.intext(p1, cs2) == S.intext(p, c <> cs2) : String})))))))) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.clean((S.mkSt(fa, p), WB.nbm(S.StP.md(p))), C.BT(len, t), W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)):
  (+p1, f1) = fl
  (e1, f2) = f1
  (+hw1, f3) = f2
  (+hmd1, f4) = f3
  (+ho1, f5) = f4
  (+ha1, f6) = f5
  (+hef1, hint) = f6
  +hi = hint(List.append(&2, String, PT.texts(pt), cs))
  +n0 = WB.nbm(S.StP.md(p))
  %Equal.sym(Norm.St, W.feed_line(S.mkSt(fa, p), C.BT(len, t)), S.mkSt(fa, p1), e1) :
    WD.StepGW(fa, T, cs, O, N, ef, W.edge(3n, n0, W.edge.of(Norm.advance(_), W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}, n0), PT.mkTOuts(fa, pt, xt), e))
  E3(fa, T, cs, O, N, ef, S.StP.o(p), p, c, k, c0, l, a, rp, pd, wp, lsT, pt, xt, e, n0, p1, p1,
    hb, hm, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he, hi,
    Equal.cong(S.MdP, Nat, z => WB.nbm(z), S.StP.md(p), S.StP.md(p1), Equal.sym(S.MdP, S.StP.md(p1), S.StP.md(p), hmd1)), ho1,
    hw1, Equal.trans(R.Report, S.report(fa, List.append(&2, String, PT.texts(pt), cs), O, N, p1), S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p), T, QS.rep_of(fa, List.append(&2, String, PT.texts(pt), cs), O, N, c, p, p1, hmd1, ho1, hi), hr),
    QX.guard_md(O, N, p, p1, hmd1, hg), ha1, hef1, ho1, ED.ch_refl(fa, List.append(&2, String, PT.texts(pt), cs), p1))

# The plan's facts (PcOK) and the task's (TcOK), taken apart.
def clean_pc(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP,
  +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +rp: P.RunP, +pd: P.PdP, +wp: PC.WP, +lsT: List<&2, B.Line>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  hpc: PT.PcOK(PT.Pc{c, rs, True{}, k, c0, l}, String.concat(List.append(&2, String, PT.texts(pt), cs))),
  +hT7: {PRD.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool},
  +hlT: {B.Text.lines(String.append(PT.after(c, k), String.concat(List.append(&2, String, PT.texts(pt), cs)))) == List.append(&2, B.Line, lsT, B.Text.lines(String.append(P.pdtext(pd), String.concat(List.append(&2, String, PT.texts(pt), cs))))) : List<&2, B.Line>},
  +hsT: {P.settle(P.specRun(rp)) == P.settle(L.run.go(lsT, fa, S.StP.o(p), SD.rs0(c0, l))) : R.RunSt},
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, S.StP.o(p), pt, xt, cs),
  he: WD.EofOK(e, ef, cs)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.clean((S.mkSt(fa, p), WB.nbm(S.StP.md(p))), C.BT(len, t), W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)):
  (h1, q1) = hpc
  (h0, q2) = q1
  (+hfc0, q3) = q2
  (hk1, q4) = q3
  (+a, q5) = q4
  (hc, hna) = q5
  clean2(fa, T, cs, O, N, ef, p, c, k, c0, l, a, pt, xt, e, len, t, d, rp, pd, wp, lsT, hb, hm, hg, hr, hc, hna, hfc0, hT7, hlT, hsT, hby, hps, hbo, he,
    QI.feed_line_ok(fa, c, p, len, t, d, hm, hcb, hcn, hok, hv))

def clean_tc(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP,
  +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +rp: P.RunP, +pd: P.PdP, +wp: PC.WP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  hpc: PT.PcOK(PT.Pc{c, rs, True{}, k, c0, l}, String.concat(List.append(&2, String, PT.texts(pt), cs))),
  htc: PT.TcOK(fa, S.StP.o(p), c, k, c0, l, List.append(&2, String, PT.texts(pt), cs), PT.TcP{rp, pd, wp}),
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, S.StP.o(p), pt, xt, cs),
  he: WD.EofOK(e, ef, cs)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.clean((S.mkSt(fa, p), WB.nbm(S.StP.md(p))), C.BT(len, t), W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}, PT.mkTOuts(fa, pt, xt), e)):
  (+hT7, r1) = htc
  (+lsT, r2) = r1
  (hlT, hsT) = r2
  clean_pc(fa, T, cs, O, N, ef, p, c, rs, k, c0, l, pt, xt, e, len, t, d, rp, pd, wp, lsT, hb, hm, hg, hr, hcb, hcn, hby, hok, hv, hpc, hT7, hlT, hsT, hps, hbo, he)

def comb_clean(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP,
  +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat, +pt: List<&2, PT.Pc>, +xt: List<&2, PT.TOutP>, +e: Bool,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +rp: P.RunP, +pd: P.PdP, +wp: PC.WP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hl: {S.stopped(S.StP.md(p)) == False{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hr: {S.report(fa, c <> List.append(&2, String, PT.texts(pt), cs), O, N, p) == T : R.Report},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {P.le31(String.length(c)) == True{} : Bool},
  +hby: {E.all_bytes(PT.texts(pt)) && E.pieces_ok(PT.texts(pt)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  hpc: PT.PcOK(PT.Pc{c, rs, True{}, k, c0, l}, String.concat(List.append(&2, String, PT.texts(pt), cs))),
  htc: PT.TcOK(fa, S.StP.o(p), c, k, c0, l, List.append(&2, String, PT.texts(pt), cs), PT.TcP{rp, pd, wp}),
  hps: PT.PcsOK(pt, cs),
  hbo: PT.BatchOK(fa, S.StP.o(p), pt, xt, cs),
  he: WD.EofOK(e, ef, cs)) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.comb.piece(W.TClean{W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}}, S.mkSt(fa, p), C.BT(len, t), PT.mkTOuts(fa, pt, xt), e)):
  %WB.qn_mk(fa, p) : WD.StepGW(fa, T, cs, O, N, ef, W.comb.clean(_, C.BT(len, t), W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}, PT.mkTOuts(fa, pt, xt), e))
  clean_tc(fa, T, cs, O, N, ef, p, c, rs, k, c0, l, pt, xt, e, len, t, d, rp, pd, wp, hb, hm, hg, hr, hcb, hcn, hby, hok, hv, hpc, htc, hps, hbo, he)
