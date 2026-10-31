import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_split.bend as NS
import ./proof_b_defs.bend as P
import ./bytes_enc.bend as E
import lawful-fields@0.1.0.0/defs.bend as FD
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_split.bend as ASP
import ./proof_b_lines.bend as LN
import ./proof_b_mw.bend as MW
import ./proof_b_fasteq.bend as FE
import ./proof_s_multi.bend as MU
import ./proof_s_drv.bend as DR
import ./proof_s_term.bend as TC
import ./proof_s_recs.bend as RS
import ./proof_s_w.bend as SW
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_mb.bend as BM
import ./proof_b_budget_lem.bend as BL
import ./proof_b_budget_dec.bend as BDe
import ./proof_b_budget_fast.bend as BFa
import ./proof_b_bud_split.bend as BS
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# The budget on a body line in the byte mode with -m (proof_b_adv.bend's
# adv.mb.m and proof_b_adv_split.bend's adv_split, BD.AdvC in place of
# S.AdvG): a line whose ALT has no comma goes to the fast path; one with a
# comma goes to the byte splitter, which either gives it back (the decoded
# path, which may split it on its text) or gives its records, put in front of
# the rest of the input (inject). There the line's rem and extra allowance
# pay for the records' allowances (BS.split_le); back is 0, so bi holds.

def O1(+st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>) -> B.Opts:
  B.Opts{st, w, True{}, o0, args}

# The records put in front (inject).
def c.leaf(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat}, +l2: U32, +t2: AT.Tree<U32>, +ps: List<&2, String>,
  +hpt: {B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hrt: {NR.chars(SW.V(l2, t2)) == Norm.recs_text(ps, B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : String},
  +h10c: {FD.count(SW.V(l2, t2), 10) == List.length(&2, String, ps) : Nat},
  +hcr: {(DR.CRT(DR.TE(len, t, at, lf)) || Nat.is_eq(FD.count(SW.V(l2, t2), 13), 0n)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{O1(st, w, o0, args), Norm.MB{NR.tick(P.mkRun(rp))}, Con{Norm.SP{C.BT(l2, t2), 0}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  match hold:
    case True{}:
      Empty.absurd(BD.AdvC(fa, cs, LI.PPs(True{}, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
          Norm.Went{Norm.St{O1(st, w, o0, args), Norm.MB{NR.tick(P.mkRun(rp))}, Con{Norm.SP{C.BT(l2, t2), 0}, Con{Norm.Src.of(True{}, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}),
        ASP.sp_abs(dfs, O1(st, w, o0, args), len, t, d, at, lf, rest, ps, BL.rf_of(fa, LI.PPs(True{}, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), hw), hpt, sl))
    case False{}:
      (hsp, r1) = sl
      (hn, r2) = r1
      +o = O1(st, w, o0, args)
      +A = P.btext(len, t, at, (lf - at : U32))
      +l = B.Text.line(A)
      +tm = B.Line.term(l)
      +pre = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)
      +post = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (lf + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed)
      +LP = B.Text.lines(BM.TP(post, cs))
      +RL = B.Text.lines(P.srctext(ASP.SPQ(l2, t2)))
      +h10 = MW.lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt)
      +hterm = TC.term_cr(len, t, d, hok, at, lf, hal, hlt, h10)
      +hl = {%Equal.sym(String, P.srctext(ASP.SPQ(l2, t2)), NR.chars(SW.V(l2, t2)), ASP.spq_txt(l2, t2)) : {B.Text.lines(_) == RS.LS(ps, tm) : List<&2, B.Line>};
        RS.lines_ck(ps, tm, DR.CRT(DR.TE(len, t, at, lf)), SW.V(l2, t2), hterm, hrt, h10c, hcr) : {RL == RS.LS(ps, tm) : List<&2, B.Line>}}
      +epre = BM.tpl(dfs, cs, o, S.MBP{rp}, S.MBP{rp}, len, t, d, at, lf, rest, pd, eof, back, back, wp, wp, None{}, None{}, fneed, fneed, hsp, hn)
      ({%Equal.sym(List<&2, B.Line>, RL, RS.LS(ps, tm), hl) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, _, LP)), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, B.Text.lines(BM.TP(pre, cs)))) == True{} : Bool};
        %Equal.sym(List<&2, B.Line>, B.Text.lines(BM.TP(pre, cs)), l <> LP, epre) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, RS.LS(ps, tm), LP)), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool};
        BS.split_le(fa, o, l, ps, tm, LP, Bool.not(fneed), back, wp, None{}, True{}, 0n, wp, None{}, BS.parts_spf(dfs, o, l, ps, hpt)) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, RL, LP)), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, B.Text.lines(BM.TP(pre, cs)))) == True{} : Bool}},
       BM.bi0(fa, wp, None{}, List.append(&2, B.Line, RL, LP)))

# The splitter's answer: the line back (the decoded path) or its records.
def c.inj.b(+hold: Bool, +b: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  q: DR.SPB(b, len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, O1(st, w, o0, args), P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match b:
    case False{}:
      %Equal.sym(NS.Ans, NS.split(C.BT(len, t), at, lf, o0, dfs), NS.Out{C.BT(len, t), None{}}, q) : BD.AdvC(fa, cs, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
        Norm.split.out(_, back, O1(st, w, o0, args), P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
      BDe.c.dec(hold, dfs, fa, T, cs, O, N, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hnr)
    case True{}:
      (+l2, q1) = q
      (+t2, q2) = q1
      (+ps, q3) = q2
      (eo, q4) = q3
      (hok2, q5) = q4
      (hpt, q6) = q5
      (hrt, ck) = q6
      (h10c, hcr) = ck
      %Equal.sym(NS.Ans, NS.split(C.BT(len, t), at, lf, o0, dfs), NS.Out{C.BT(len, t), Some{C.BT(l2, t2)}}, eo) : BD.AdvC(fa, cs, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
        Norm.split.out(_, back, O1(st, w, o0, args), P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
      c.leaf(hold, dfs, fa, cs, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hw, lf, hok, hs, hal, hlt, hfl, l2, t2, ps, hpt, hrt, h10c, hcr,
        LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hnr)

def c.inj.spr(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  r: DR.SPR(len, t, NS.split(C.BT(len, t), at, lf, o0, dfs), B.Rec.parts(dfs, B.Opts{st, w, True{}, o0, args}, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32))))), B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), B.Line.term(B.Text.line(P.btext(len, t, at, (lf - at : U32)))), DR.CRT(DR.TE(len, t, at, lf))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.split.out(NS.split(C.BT(len, t), at, lf, o0, dfs), back, O1(st, w, o0, args), P.mkRun(rp), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  (+b, q) = r
  c.inj.b(hold, b, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, lf, hok, hs, hal, hlt, hfl, q, hnr)

# The byte splitter's branch (multi said Some).
def c.split(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +esp: {R.Opts.split(o) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.split.b(back, o, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      match sp:
        case False{}:
          Empty.absurd(BD.AdvC(fa, cs, LI.PPs(hold, dfs, B.Opts{st, w, False{}, o0, args}, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
            Norm.split.b(back, B.Opts{st, w, False{}, o0, args}, P.mkRun(rp), C.BT(len, t), at, lf, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)), N.false_ne_true(esp))
        case True{}:
          c.inj.spr(hold, dfs, fa, T, cs, O, N, st, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, lf, hok, hs, hal, hlt, hfl,
            DR.split_t(len, t, d, hok, Nat.pow(2n, 32n), {==}, dfs, st, w, o0, args, at, lf, hal, hlt, MW.lf_byte(len, t, d, hok, at, lf, hs, hfl, hlt)), hnr)

# multi's answer: no comma in the ALT (the fast path), or the line's LF.
def c.mm(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +m: Maybe<&2, U32>,
  +j: U32, +hj: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) : Nat}, +hmv2: {MU.MV(m, j, len) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(at, len) == True{} : Bool}, +esp: {R.Opts.split(o) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.multi((C.BT(len, t), m), back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match m:
    case None{}:
      BFa.c.fast(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hbi, hnr)
    case Some{+lf}:
      +hlj = N.eq_sound(U32.to_nat(lf), U32.to_nat(j), W.and_l(Nat.is_eq(U32.to_nat(lf), U32.to_nat(j)), Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)), hmv2))
      +hlt = W.and_r(Nat.is_eq(U32.to_nat(lf), U32.to_nat(j)), Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)), hmv2)
      +hfl = Equal.trans(Nat, D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10), U32.to_nat(j), U32.to_nat(lf), Equal.sym(Nat, U32.to_nat(j), D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10), hj), Equal.sym(Nat, U32.to_nat(lf), U32.to_nat(j), hlj))
      +hal = {%hfl : {Nat.is_le(U32.to_nat(at), _) == True{} : Bool};
        N.le_add_r(U32.to_nat(at), D.run_len(D.slice(D.view(C.BT(len, t)), U32.to_nat(at), Nat.sub(U32.to_nat(len), U32.to_nat(at))), 10)) : {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool}}
      c.split(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, lf, hok, hs, hal, hlt, hfl, esp, hnr)

def c.mp(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +j: U32, +hj: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) : Nat},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(at, len) == True{} : Bool}, +esp: {R.Opts.split(o) == True{} : Bool},
  mp: MU.MP(len, t, NS.multi(C.BT(len, t), at), j),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.multi(NS.multi(C.BT(len, t), at), back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  (e1, e2) = mp
  %Equal.sym(D.Bytes & Maybe<&2, U32>, NS.multi(C.BT(len, t), at), (C.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at))), e1) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
      Norm.body.multi(_, back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
  c.mm(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hbi, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at)), j, hj, e2, hok, hs, esp, hnr)

# A body line in the byte mode: without -m the fast path; with -m, multi's test first.
def c.m(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +sp: Bool, +esp: {R.Opts.split(o) == sp : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.m(sp, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match sp:
    case False{}:
      BFa.c.fast(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hbi, hnr)
    case True{}:
      +p = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)
      +m0 = S.md_ok(S.MBP{LI.RTP(hold, rp)})
      +hso = LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
      +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +j = Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), at, len, 10))
      +hj = Equal.trans(Nat, U32.to_nat(j), U32.to_nat(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), at, len, 10))), D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10),
        Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), F.find(C.BT(len, t), at, len, 10), BY.find(C.BT(len, t), at, len, 10), FE.find_eq(C.BT(len, t), d, at, len, 10, hok, hs, N.le_refl(U32.to_nat(len)), {==})),
        PF.find_view_t(len, t, d, at, len, 10, hok, hs, N.le_refl(U32.to_nat(len)), {==}))
      c.mp(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hin, hbi, j, hj, hok, hs, esp,
        MU.multi_pair(len, t, d, hok, at, hs), hnr)
