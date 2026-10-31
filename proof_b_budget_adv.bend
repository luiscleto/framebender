import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv.bend as A
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_wf.bend as W
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/defs.bend as D
import ./bytes_enc.bend as E
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_b_budget_fast.bend as BFa
import ./proof_b_budget_ms.bend as BMS
import ./proof_b_budget_mb.bend as BM
import ./proof_b_bud_inj.bend as BI
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# What advance does to the budget (BD.AdvC: WA and bi), by advance's paths
# as proof_b_adv.bend walks them for adv_ok. Every leaf is one of:
#   - the state as it was (Ended, Idle, Yield);
#   - the text and the fields kept, the String mode taken (WA can only drop:
#     the fast path's term goes);
#   - a line handled (Went past it): its rem leaves WA, the next line's rem is
#     at most its allowance;
#   - a Want: the flag it flips pays its step and reads.

# ---------------------------------------------------------------------------
# WA's shape
# ---------------------------------------------------------------------------

def pick_le(+b: Bool, +n: Nat) -> {Nat.is_le(BN.pick(b, n), n) == True{} : Bool}:
  match b:
    case True{}:
      N.le_refl(n)
    case False{}:
      N.le_zero_l(n)

def rem_fl(+g: Bool, +fl: Bool, +rw: Nat, +X: Nat, +Y: Nat) ->
  {Nat.is_le(BN.pick(g, Nat.add(Nat.add(BN.pick(False{}, rw), X), Y)), BN.pick(g, Nat.add(Nat.add(BN.pick(fl, rw), X), Y))) == True{} : Bool}:
  match g:
    case True{}:
      N.le_add_mono_r(Y, X, Nat.add(BN.pick(fl, rw), X), N.le_add_l(X, BN.pick(fl, rw)))
    case False{}:
      {==}

# Taking the fast path's term away only lowers WA.
def wa_fl(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) ->
  {Nat.is_le(BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), asked, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), asked, ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      N.le_add_mono_r(BN.LAs(fa, t), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), asked, l), BN.rem(fa, fl, back, PC.mkWin(fa, wp), asked, l),
        rem_fl(BN.lgate(l), fl, BN.RW(l), BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), asked, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)),
          Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa)))))

def fl_mso(s: R.RunSt, qs: List<&2, String>, +ql: Nat, +f: Bool) -> {BN.fast_left(Norm.ms.out(s, qs, ql), f) == False{} : Bool}:
  match s:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

def fl_ms(+rp: P.RunP, +f: Bool) -> {BN.fast_left(Norm.to_ms(P.mkRun(rp)), f) == False{} : Bool}:
  fl_mso(NR.to_spec(P.mkRun(rp)), Nil{}, 0n, f)

# The byte mode going to the String mode: text and fields kept, nothing asked.
def to_ms_c(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  +ls = BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  (%Equal.sym(Bool, BN.fast_left(Norm.to_ms(P.mkRun(rp)), fneed), False{}, fl_ms(rp, fneed)) :
     {Nat.is_le(BN.WAX(fa, o, _, back, PC.mkWin(fa, wp), None{}, ls), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, ls)) == True{} : Bool}
   BM.wax_le(fa, o, False{}, back, wp, None{}, Bool.not(fneed), back, wp, None{}, ls, wa_fl(fa, Bool.not(fneed), back, wp, None{}, ls)),
   hbi)

def ss_mk(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP) -> {Nat.is_le(BN.WAS(fa, S.mkSt(fa, p), cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}:
  N.le_refl(BN.WAS(fa, S.mkSt(fa, p), cs))

# ---------------------------------------------------------------------------
# The line paths (to come)
# ---------------------------------------------------------------------------

def c.mb.if(+hold: Bool, +dfs: B.Defs, +i: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +ei: {P.RunP.i(rp) == i : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.if(i, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      BDe.c.dec(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hnr)
    case True{}:
      BI.c.m(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, ei, hbi, R.Opts.split(o), {==}, hnr)


def c.mb.sb(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(rp)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), DE.inb_eq(rp)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
      Norm.body.k(back, o, _, C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
  c.mb.if(hold, dfs, P.RunP.i(rp), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, {==}, hb, hw, hr, hg, hx, hbig, hbi, hnr)

def c.ms.sb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{})):
  BMS.c_ms_sb(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

def c.ms.sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  BMS.c_ms_sl(dfs, fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

# ---------------------------------------------------------------------------
# The dispatch (as proof_b_adv.bend's)
# ---------------------------------------------------------------------------

# A record buffer in the byte mode (norm_seq.bend's sp.b): dropped when read
# to its end (its bytes left give no line: WA, XA and bi unchanged); else its
# next record, through the line paths with hold (the run unticked: the record
# counts its line again).
def c.mb.spp.if(+dn: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +edn: {U32.is_le(len, at) == dn : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.sp.b.if(dn, back, o, P.mkRun(rp), C.BT(len, t), at, P.mkSrcs(rest), P.mkPd(pd), eof, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match dn:
    case True{}:
      +p = BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +h1 = W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +hso = HX.srcs_head_p(rest, len, t, d, at, h1)
      +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +X = P.srctext(P.SPP{len, t, d, at})
      +hX = HX.em_sp(len, t, d, at, hok, edn)
      +AR = BN.ALL(P.mkSrcs(rest), P.mkPd(pd), eof, cs)
      +WR = BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, AR)
      ({%Equal.sym(String, X, "", hX) : {Nat.is_le(WR, BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, B.Text.lines(_), AR))) == True{} : Bool};
        N.le_refl(WR) : {Nat.is_le(WR, BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, B.Text.lines(X), AR))) == True{} : Bool}},
       {%Equal.sym(String, X, "", hX) : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, B.Text.lines(_), AR)) == True{} : Bool} -> {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, AR) == True{} : Bool};
        (h => h) : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, B.Text.lines(X), AR)) == True{} : Bool} -> {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, AR) == True{} : Bool}}(hbi))
    case False{}:
      +U = HX.untick_p(rp)
      +e = HX.tu_eq(rp, HX.n_sp(fa, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed, hw))
      +er = Equal.sym(P.RunP, LI.tick_p(U), rp, e)
      %Equal.sym(NR.Run, NR.untick(P.mkRun(rp)), P.mkRun(U), HX.ut_mk(rp)) :
        BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
          Norm.body.k(back, o, Norm.Run.inbody(_), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed))
      %e :
        BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{_}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
          Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(U)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed))
      c.mb.sb(True{}, dfs, fa, T, cs, O, N, o, U, len, t, d, at, rest, pd, eof, back, wp, fneed, hb,
        AB.subst(P.RunP, z => {S.WF(fa, BD.StM(dfs, o, S.MBP{z}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool}, rp, LI.tick_p(U), er, hw),
        AB.subst(P.RunP, z => {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{z}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report}, rp, LI.tick_p(U), er, hr),
        AB.subst(P.RunP, z => {S.guard(O, N, BD.StM(dfs, o, S.MBP{z}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool}, rp, LI.tick_p(U), er, hg),
        Equal.trans(Bool, P.RunP.x(U), P.RunP.x(rp), False{}, HX.ut_x(rp), hx),
        Equal.trans(Bool, U32.is_le(1073741824, P.RunP.ow(U)), U32.is_le(1073741824, P.RunP.ow(rp)), False{}, Equal.cong(U32, Bool, z => U32.is_le(1073741824, z), P.RunP.ow(U), P.RunP.ow(rp), HX.ut_ow(rp)), hf),
        Equal.trans(Bool, U32.is_le(536870912, P.RunP.obl(U)), U32.is_le(536870912, P.RunP.obl(rp)), False{}, Equal.cong(U32, Bool, z => U32.is_le(536870912, z), P.RunP.obl(U), P.RunP.obl(rp), HX.ut_obl(rp)), hbig),
        AB.subst(P.RunP, z => {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{z}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}, rp, LI.tick_p(U), er, hbi),
        HX.ult(len, at, edn))

def c.mb.spp(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.sp.b(back, o, P.mkRun(rp), BY.len(C.BT(len, t)), at, P.mkSrcs(rest), P.mkPd(pd), eof, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  c.mb.spp.if(U32.is_le(len, at), dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hf, hbig, hbi, {==})

def c.mbsrc(+dfs: B.Defs, +src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed),
    Norm.mb.src(P.mkSrcs(src), o, P.mkRun(rp), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match src:
    case Nil{}:
      (ss_mk(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Nil{}, pd, eof, back, wp, None{}, fneed)), hbi)
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      c.mb.sb(False{}, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hf, hbig, hbi, {==})
    case Con{P.SLP{+q}, +rest}:
      to_ms_c(dfs, fa, cs, o, rp, Con{P.SLP{q}, rest}, pd, eof, back, wp, fneed, hbi)
    case Con{P.SRP{+l}, +rest}:
      to_ms_c(dfs, fa, cs, o, rp, Con{P.SRP{l}, rest}, pd, eof, back, wp, fneed, hbi)
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      c.mb.spp(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hf, hbig, hbi)


def c.mb.k(+dfs: B.Defs, +x: Bool, +f: Bool, +g: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +ex: {P.RunP.x(rp) == x : Bool},
  +ef: {U32.is_le(1073741824, P.RunP.ow(rp)) == f : Bool},
  +eg: {U32.is_le(536870912, P.RunP.obl(rp)) == g : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed),
    Norm.mb.rs((P.mkRun(rp), Norm.Rs{x, f, g}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match x f g:
    case True{} _ _:
      (ss_mk(fa, cs, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case False{} True{} _:
      ({==}, (ef, hbi))
    case False{} False{} True{}:
      to_ms_c(dfs, fa, cs, o, rp, src, pd, eof, back, wp, fneed, hbi)
    case False{} False{} False{}:
      c.mbsrc(dfs, src, fa, T, cs, O, N, o, rp, pd, eof, back, wp, fneed, hb, hw, hr, hg, ex, ef, eg, hbi)

def c.mssrc(+dfs: B.Defs, +src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.src(P.mkSrcs(src), o, s, qs, ql, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  ?TODO


def c.msfull(+dfs: B.Defs, +full: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +ef: {Nat.is_le(Norm.lim(), ql) == full : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.full(full, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match full:
    case True{}:
      ({==}, (ef, hbi))
    case False{}:
      c.mssrc(dfs, src, fa, T, cs, O, N, o, s, qs, ql, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

def c.ms.k(+dfs: B.Defs, +x: Bool, +code: Maybe<&2, Nat>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +ex: {R.RunSt.halt(s) == x : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.adv(x, o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match x code:
    case _ Some{+c}:
      (ss_mk(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, Some{c}}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case True{} None{}:
      (ss_mk(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case False{} None{}:
      c.msfull(dfs, Nat.is_le(Norm.lim(), ql), fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, fneed, {==}, hb, hw, hr, hg, ex, hbi)


def none_some(+r: List<&2, Pr.Req>, +h: {Some{r} == None{} : Maybe<&2, List<&2, Pr.Req>>}) -> Empty:
  N.true_ne_false(Equal.cong(Maybe<&2, List<&2, Pr.Req>>, Bool, m => Maybe.is_some(&2, List<&2, Pr.Req>, m), Some{r}, None{}, h))

def c.top(+dfs: B.Defs, +asked: Maybe<&2, List<&2, Pr.Req>>, +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed), Norm.advance(S.mkSt(fa, BD.StM(dfs, o, md, src, pd, eof, back, wp, asked, fneed)))):
  match asked md:
    case Some{+r} _:
      Empty.absurd(BD.AdvC(fa, cs, BD.StM(dfs, o, md, src, pd, eof, back, wp, Some{r}, fneed), Norm.advance(S.mkSt(fa, BD.StM(dfs, o, md, src, pd, eof, back, wp, Some{r}, fneed)))), none_some(r, ha))
    case None{} S.MBP{+rp}:
      %Equal.sym(NR.Run & Norm.Rs, Norm.Run.rs(P.mkRun(rp)), (P.mkRun(rp), Norm.Rs{P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp))}), A.rs_eq(rp)) :
        BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed), Norm.mb.rs(_, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs))
      c.mb.k(dfs, P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp)), fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, {==}, {==}, {==}, hbi)
    case None{} S.MSP{+s, +qs, +ql, +code}:
      c.ms.k(dfs, R.RunSt.halt(s), code, fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, {==}, hbi)

# advance and the budget.
def adv_c(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, p) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, p, Norm.advance(S.mkSt(fa, p))):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      c.top(dfs, asked, ha, fa, T, cs, O, N, o, md, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, hbi)

def c2b(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, a: Norm.Adv, h: BD.AdvC(fa, cs, p, a)) -> BD.AdvB(fa, cs, p, a):
  match a:
    case Norm.Went{st}:
      match h:
        case (x, y):
          x
    case Norm.Want{st, rs}:
      match h:
        case (x, y):
          x
    case Norm.Idle{st}:
      match h:
        case (x, y):
          x
    case Norm.Ended{st}:
      match h:
        case (x, y):
          x
    case Norm.Yield{st}:
      match h:
        case (x, y):
          match y:
            case (u, v):
              (x, u)

def c2bi(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, a: Norm.Adv, h: BD.AdvC(fa, cs, p, a)) -> BD.AdvBi(cs, a):
  match a:
    case Norm.Went{st}:
      match h:
        case (x, y):
          y
    case Norm.Want{st, rs}:
      match h:
        case (x, y):
          y
    case Norm.Idle{st}:
      match h:
        case (x, y):
          y
    case Norm.Ended{st}:
      match h:
        case (x, y):
          y
    case Norm.Yield{st}:
      match h:
        case (x, y):
          match y:
            case (u, v):
              v
