import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_split.bend as NS
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_adv_ref.bend as AR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_b_bud_dech.bend as DH
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The budget on a line the byte splitter refuses (proof_b_adv_ref.bend's
# ref.adv with BD.AdvC in place of S.AdvG): the String path (proof_b_bud_dech's
# decoded), or the line passed through as body_done of the problem c.
# Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def PPF(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool) -> S.StP:
  LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)

def c.ref.pass(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code,
  +hpu: {B.Rec.parts(dfs, AR.O1(False{}, w, o0, args), AR.BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +hfc: {Maybe.is_some(&2, String, B.Fasta.find(fa, AR.FK(len, t, at, lf, 0n))) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (lf - at : U32)) == False{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, lf), +hn: {P.nolf(AR.TA(len, t, at, lf)) == True{} : Bool}, +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool}, +hby: {E.is_bytes(AR.TA(len, t, at, lf)) == True{} : Bool}) ->
  BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
    Norm.ref.pos(AR.O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, AR.FK(len, t, at, lf, 0n), (C.BT(len, t), AR.FK(len, t, at, lf, 1n)), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  +o = AR.O1(False{}, w, o0, args)
  +A0 = AR.TA(len, t, at, lf)
  +l = Norm.line(A0)
  +bd = B.Line.body(l)
  +fs = J.pfs(bd)
  +p = PPF(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed)
  +m0 = S.md_ok(S.MBP{LI.RTP(False{}, rp)})
  +hi = HX.inv_h(False{}, rp, W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +RPR = {B.Res{B.Problem{c}, B.Rec.pos(fs), bd, False{}} : B.Res}
  %Equal.sym(String, AR.FK(len, t, at, lf, 0n), B.Rec.field(fs, 0n), AR.fk_eq(len, t, at, lf, 0n, {==})) :
    BD.AdvC(fa, cs, p, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, _, (C.BT(len, t), AR.FK(len, t, at, lf, 1n)), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
  %Equal.sym(String, AR.FK(len, t, at, lf, 1n), B.Rec.field(fs, 1n), AR.fk_eq(len, t, at, lf, 1n, {==})) :
    BD.AdvC(fa, cs, p, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, B.Rec.field(fs, 0n), (C.BT(len, t), _), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
  %Equal.sym(Norm.Adv, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, B.Rec.field(fs, 0n), (C.BT(len, t), B.Rec.field(fs, 1n)), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)),
    Norm.body_done(RPR, o, Norm.ticked(P.mkRun(rp)), l, fs, at, lf, C.BT(len, t), AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)),
    AR.ref_bd(w, o0, args, Norm.ticked(P.mkRun(rp)), c, fs, l, B.Rec.pos(fs), bd, C.BT(len, t), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))) :
    BD.AdvC(fa, cs, p, _)
  DH.K.body(False{}, dfs, RPR, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, lf,
    Equal.sym(Nat, D.first(D.view(C.BT(len, t)), n(at), n(len), 10), n(lf), hfl), hsp, hn, hle, hby, hal, hlt, LP.inc_len(len, t, d, lf, hok, hlt), hsm, hin,
    {==}, SLW.body_bytes(A0, hby), PR.run_tick(rp, hi), {==})

# ---------------------------------------------------------------------------
# The refused line's branch (-c w): through, or the String path
# ---------------------------------------------------------------------------

def c.ref.sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code,
  +hpu: {B.Rec.parts(dfs, AR.O1(False{}, w, o0, args), AR.BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +hfc: {Maybe.is_some(&2, String, B.Fasta.find(fa, AR.FK(len, t, at, lf, 0n))) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (lf - at : U32)) == False{} : Bool},
  sl: AR.SLP(len, t, d, at, lf)) ->
  BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
    Norm.ref.pos(AR.O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, AR.FK(len, t, at, lf, 0n), (C.BT(len, t), AR.FK(len, t, at, lf, 1n)), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  (hsp, r1) = sl
  (hn, r2) = r1
  (hle, hby) = r2
  c.ref.pass(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, lf, hok, hs, hal, hlt, hfl, c, hpu, hfc, hsm, hsp, hn, hle, hby)

def c.ref.k(+ok: Bool, +bo: Bool, +big: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, AR.O1(False{}, w, o0, args), AR.BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), AR.FK(len, t, at, lf, 1n)) : D.Bytes & String},
  +eok: {Bool.and(bo, Bool.not(big)) == ok : Bool},
  +ebig: {U32.is_lt(268435456, (lf - at : U32)) == big : Bool},
  imp: {bo == True{} : Bool} -> {Maybe.is_some(&2, String, B.Fasta.find(fa, AR.FK(len, t, at, lf, 0n))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
    Norm.ref.if(ok, back, AR.O1(False{}, w, o0, args), P.mkRun(rp), c, AR.FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed)):
  match ok:
    case False{}:
      BDe.c.dec(False{}, dfs, fa, T, cs, O, N, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, {==})
    case True{}:
      +hbo = N.and_true_l(bo, Bool.not(big), eok)
      +hnb = AR.nt(big, N.and_true_r(bo, Bool.not(big), eok))
      +hsm = Equal.trans(Bool, U32.is_lt(268435456, (lf - at : U32)), big, False{}, ebig, hnb)
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), f1), (C.BT(len, t), AR.FK(len, t, at, lf, 1n)), h1) :
        BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
          Norm.ref.pos(AR.O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, AR.FK(len, t, at, lf, 0n), _, at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
      c.ref.sl(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, lf, hok, hs, hal, hlt, hfl, c, hpu, imp(hbo), hsm,
        LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt))

def c.ref.won(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, AR.O1(False{}, w, o0, args), AR.BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), AR.FK(len, t, at, lf, 1n)) : D.Bytes & String},
  q: AR.WON(fa, wp, AR.FK(len, t, at, lf, 0n))) ->
  BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
    Norm.ref.on(Norm.Win.on(PC.mkWin(fa, wp), AR.FK(len, t, at, lf, 0n)), U32.is_lt(268435456, (lf - at : U32)), back, AR.O1(False{}, w, o0, args), P.mkRun(rp), c, AR.FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, AR.CXF(dfs, rest, pd, eof), fneed)):
  (+bo, q1) = q
  (eq, imp) = q1
  +big = U32.is_lt(268435456, (lf - at : U32))
  %Equal.sym(Norm.Win & Bool, Norm.Win.on(PC.mkWin(fa, wp), AR.FK(len, t, at, lf, 0n)), (PC.mkWin(fa, wp), bo), eq) :
    BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
      Norm.ref.on(_, big, back, AR.O1(False{}, w, o0, args), P.mkRun(rp), c, AR.FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, AR.CXF(dfs, rest, pd, eof), fneed))
  c.ref.k(Bool.and(bo, Bool.not(big)), bo, big, dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, lf, hok, hs, hal, hlt, hfl,
    c, f1, hpu, h1, {==}, {==}, imp)

# A line the byte splitter refuses (code c; its CHROM and POS ranges f0, f1),
# from a byte source.
def c.ref.adv(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, AR.O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, AR.O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, AR.O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, PPF(dfs, AR.O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f0: NS.Rg, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, AR.O1(st, w, o0, args), AR.BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h0: {NS.txt(C.BT(len, t), f0) == (C.BT(len, t), AR.FK(len, t, at, lf, 0n)) : D.Bytes & String},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), AR.FK(len, t, at, lf, 1n)) : D.Bytes & String}) ->
  BD.AdvC(fa, cs, PPF(dfs, AR.O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
    Norm.split.out(NS.Ref{C.BT(len, t), c, f0, f1}, back, AR.O1(st, w, o0, args), P.mkRun(rp), at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed)):
  match st:
    case True{}:
      BDe.c.dec(False{}, dfs, fa, T, cs, O, N, AR.O1(True{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, {==})
    case False{}:
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), f0), (C.BT(len, t), AR.FK(len, t, at, lf, 0n)), h0) :
        BD.AdvC(fa, cs, PPF(dfs, AR.O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, fneed),
          Norm.ref.ch(_, back, AR.O1(False{}, w, o0, args), P.mkRun(rp), c, f1, at, lf, AR.CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed))
      c.ref.won(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, lf, hok, hs, hal, hlt, hfl,
        c, f1, hpu, h1, AR.win_on(fa, wp, AR.FK(len, t, at, lf, 0n)))
