import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_ms.bend as MS
import ./proof_b_adv_tostr.bend as TS
import ./proof_b_adv_dec.bend as DE
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_b_adv_fast.bend as FA
import ./proof_b_adv_msx.bend as MX
import ./proof_b_adv_msr.bend as MR
import ./proof_s_multi.bend as MU
import ./proof_b_adv_split.bend as SP
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./norm_split.bend as NS
import lawful-bytes@0.1.0.0/fast.bend as F
import ./proof_b_adv_line.bend as LI
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_b_adv_sp.bend as HX
import lawful-bytes@0.1.0.0/defs.bend as D

# adv_ok's proof (proof_b_sim.bend calls adv): handling the next line keeps a
# good state standing for the same report. By cases on advance's paths:
#   - the byte mode: the run stopped (Ended), wrote 2^30 bytes (Yield), has
#     a big buffer (to the String mode), no source (Idle), a text line (to
#     the String mode), a byte source (the line paths: adv.mb.sb);
#   - the String mode: finished or stopped (Ended), wrote 2^30 bytes
#     (Yield), no source (Idle), a byte source (adv.ms.sb), a text line
#     (adv.ms.sl).
# Every variable of the helpers is reusable.

def StM(+dfs: B.Defs, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}

# The run's state test on a pictured run computes.
law rs_eq:
  for +rp: P.RunP
  {Norm.Run.rs(P.mkRun(rp)) == (P.mkRun(rp), Norm.Rs{P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp))}) : NR.Run & Norm.Rs}

def rs_eq(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# ---------------------------------------------------------------------------
# The line paths (to come)
# ---------------------------------------------------------------------------

# The byte mode, a byte source, in the body: the fast path.
def adv.fast(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.fast.pre(back, o, P.mkRun(rp), at, NF.line(C.BT(len, t), at), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  FA.F.top(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hmv, hbig, hin, hnr)

# The fast path's test, without -m: it passes.
def mw_off(+o: B.Opts, +len: U32, +t: AT.Tree<U32>, +at: U32, +h: {R.Opts.split(o) == False{} : Bool}) -> {MU.MW(o, len, t, at) == True{} : Bool}:
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      %Equal.sym(Bool, sp, False{}, h) : {Bool.or(Bool.not(_), Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at)))) == True{} : Bool}
      {==}

def mw_or(+sp: Bool, +x: Bool, +h: {x == True{} : Bool}) -> {Bool.or(Bool.not(sp), x) == True{} : Bool}:
  match sp:
    case True{}:
      h
    case False{}:
      {==}

# With -m, multi answered None: it passes.
def mw_none(+o: B.Opts, +len: U32, +t: AT.Tree<U32>, +at: U32, +h: {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at))) == True{} : Bool}) ->
  {MU.MW(o, len, t, at) == True{} : Bool}:
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      mw_or(sp, Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at))), h)

def adv.mb.mm(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool}, +m: Maybe<&2, U32>,
  +em: {Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at)) == m : Maybe<&2, U32>},
  +j: U32, +hj: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) : Nat}, +hmv2: {MU.MV(m, j, len) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(at, len) == True{} : Bool}, +esp: {R.Opts.split(o) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.multi((C.BT(len, t), m), back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match m:
    case None{}:
      adv.fast(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, mw_none(o, len, t, at, {%Equal.sym(Maybe<&2, U32>, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at)), None{}, em) : {Maybe.is_none(&2, U32, _) == True{} : Bool}; {==} : {Maybe.is_none(&2, U32, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at))) == True{} : Bool}}), hf, hbig, hin, hnr)
    case Some{+lf}:
      +hlj = N.eq_sound(U32.to_nat(lf), U32.to_nat(j), W.and_l(Nat.is_eq(U32.to_nat(lf), U32.to_nat(j)), Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)), hmv2))
      +hlt = W.and_r(Nat.is_eq(U32.to_nat(lf), U32.to_nat(j)), Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)), hmv2)
      +hfl = Equal.trans(Nat, D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10), U32.to_nat(j), U32.to_nat(lf), Equal.sym(Nat, U32.to_nat(j), D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10), hj), Equal.sym(Nat, U32.to_nat(lf), U32.to_nat(j), hlj))
      +hal = {%hfl : {Nat.is_le(U32.to_nat(at), _) == True{} : Bool};
        N.le_add_r(U32.to_nat(at), D.run_len(D.slice(D.view(C.BT(len, t)), U32.to_nat(at), Nat.sub(U32.to_nat(len), U32.to_nat(at))), 10)) : {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool}}
      SP.adv_split_h(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, esp, hnr)

def adv.mb.mp(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool}, +j: U32, +hj: {U32.to_nat(j) == D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) : Nat},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(at, len) == True{} : Bool}, +esp: {R.Opts.split(o) == True{} : Bool},
  mp: MU.MP(len, t, NS.multi(C.BT(len, t), at), j),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.multi(NS.multi(C.BT(len, t), at), back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  (e1, e2) = mp
  %Equal.sym(D.Bytes & Maybe<&2, U32>, NS.multi(C.BT(len, t), at), (C.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at))), e1) : S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.multi(_, back, o, P.mkRun(rp), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
  adv.mb.mm(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, hin, Pair.snd(D.Bytes, Maybe<&2, U32>, NS.multi(C.BT(len, t), at)), {==}, j, hj, e2, hok, hs, esp, hnr)

# The byte mode, a byte source, in the body: the fast path, after multi's
# test with -m.
def adv.mb.m(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool}, +sp: Bool, +esp: {R.Opts.split(o) == sp : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.m(sp, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match sp:
    case False{}:
      adv.fast(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, mw_off(o, len, t, at, esp), hf, hbig, hin, hnr)
    case True{}:
      +p = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{LI.RTP(hold, rp)})
      +hso = LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
      +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
      +j = Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), at, len, 10))
      +hj = Equal.trans(Nat, U32.to_nat(j), U32.to_nat(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), at, len, 10))), D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10),
        Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), F.find(C.BT(len, t), at, len, 10), BY.find(C.BT(len, t), at, len, 10), FE.find_eq(C.BT(len, t), d, at, len, 10, hok, hs, N.le_refl(U32.to_nat(len)), {==})),
        PF.find_view_t(len, t, d, at, len, 10, hok, hs, N.le_refl(U32.to_nat(len)), {==}))
      adv.mb.mp(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, hin, j, hj, hok, hs, esp,
        MU.multi_pair(len, t, d, W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso), at, W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)), hnr)

def adv.mb.if(+hold: Bool, +dfs: B.Defs, +i: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +ei: {P.RunP.i(rp) == i : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.if(i, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      DE.dec(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig, hnr)
    case True{}:
      adv.mb.m(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, ei, R.Opts.split(o), {==}, hnr)


# The byte mode, a byte source: the line at at (fast path in the body,
# else the decoded path: header lines, a source with no complete line, a
# line too long, the slow path).
def adv.mb.sb(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(rp)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), DE.inb_eq(rp)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
      Norm.body.k(back, o, _, C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
  adv.mb.if(hold, dfs, P.RunP.i(rp), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, {==}, hnr)

# The String mode, a byte source.
def adv.ms.sb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{})):
  MX.ms_sb(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

# The String mode, a text line.
def adv.ms.sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  MX.ms_sl(dfs, fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

# ---------------------------------------------------------------------------
# The byte mode
# ---------------------------------------------------------------------------

# The byte mode, a record buffer (norm_seq.bend's sp.b): dropped when read to
# its end; else its next record, from the run its line was counted in, through
# the line paths with hold.
def adv.mb.spp.if(+dn: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +edn: {U32.is_le(len, at) == dn : Bool}) ->
  S.AdvG(fa, T, cs, O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.sp.b.if(dn, back, o, P.mkRun(rp), C.BT(len, t), at, P.mkSrcs(rest), P.mkPd(pd), eof, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match dn:
    case True{}:
      HX.sp_done(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, edn)
    case False{}:
      +U = HX.untick_p(rp)
      +e = HX.tu_eq(rp, HX.n_sp(fa, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hw))
      +er = Equal.sym(P.RunP, LI.tick_p(U), rp, e)
      %Equal.sym(NR.Run, NR.untick(P.mkRun(rp)), P.mkRun(U), HX.ut_mk(rp)) :
        S.AdvG(fa, T, cs, O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.body.k(back, o, Norm.Run.inbody(_), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed))
      %e :
        S.AdvG(fa, T, cs, O, N, HX.SD(dfs, o, _, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(U)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed))
      adv.mb.sb(True{}, dfs, fa, T, cs, O, N, o, U, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb,
        AB.subst(P.RunP, z => {S.WF(fa, HX.SD(dfs, o, z, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool}, rp, LI.tick_p(U), er, hw),
        AB.subst(P.RunP, z => {S.report(fa, cs, O, N, HX.SD(dfs, o, z, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report}, rp, LI.tick_p(U), er, hr),
        AB.subst(P.RunP, z => {S.guard(O, N, HX.SD(dfs, o, z, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool}, rp, LI.tick_p(U), er, hg),
        Equal.trans(Bool, P.RunP.x(U), P.RunP.x(rp), False{}, HX.ut_x(rp), hx),
        Equal.trans(Bool, U32.is_le(1073741824, P.RunP.ow(U)), U32.is_le(1073741824, P.RunP.ow(rp)), False{}, Equal.cong(U32, Bool, z => U32.is_le(1073741824, z), P.RunP.ow(U), P.RunP.ow(rp), HX.ut_ow(rp)), hf),
        Equal.trans(Bool, U32.is_le(536870912, P.RunP.obl(U)), U32.is_le(536870912, P.RunP.obl(rp)), False{}, Equal.cong(U32, Bool, z => U32.is_le(536870912, z), P.RunP.obl(U), P.RunP.obl(rp), HX.ut_obl(rp)), hbig),
        HX.ult(len, at, edn))

def adv.mb.spp(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, HX.SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.sp.b(back, o, P.mkRun(rp), BY.len(C.BT(len, t)), at, P.mkSrcs(rest), P.mkPd(pd), eof, PC.mkWin(fa, wp), asked, fneed, dfs)):
  adv.mb.spp.if(U32.is_le(len, at), dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, {==})

def mbsrc(+dfs: B.Defs, +src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed),
    Norm.mb.src(P.mkSrcs(src), o, P.mkRun(rp), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match src:
    case Nil{}:
      (StM(dfs, o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, ({==}, ({==}, (hx, (hg, ({==}, (W.moved_keep(fa, cs, rp, StM(dfs, o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), StM(dfs, o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), {==}, {==}, {==}, {==}), Unit{})))))))))))
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      adv.mb.sb(False{}, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, {==})
    case Con{P.SLP{+q}, +rest}:
      TS.to_ms_went(dfs, fa, T, cs, O, N, o, rp, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed, back, fneed, hw, hr, hg, hx)
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      adv.mb.spp(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig)
    case Con{P.SRP{+l}, +rest}:
      TS.to_ms_went(dfs, fa, T, cs, O, N, o, rp, Con{P.SRP{l}, rest}, pd, eof, back, wp, asked, fneed, back, fneed, hw, hr, hg, hx)



def mb.k(+dfs: B.Defs, +x: Bool, +f: Bool, +g: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +ex: {P.RunP.x(rp) == x : Bool},
  +ef: {U32.is_le(1073741824, P.RunP.ow(rp)) == f : Bool},
  +eg: {U32.is_le(536870912, P.RunP.obl(rp)) == g : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed),
    Norm.mb.rs((P.mkRun(rp), Norm.Rs{x, f, g}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match x f g:
    case True{} _ _:
      (StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (ex, ({==}, (hg, ({==}, ({==}, W.kept_same(src)))))))))))
    case False{} True{} _:
      (StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (ex, ({==}, (hg, ({==}, ({==}, W.kept_same(src)))))))))))
    case False{} False{} True{}:
      TS.to_ms_went(dfs, fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, back, fneed, hw, hr, hg, ex)
    case False{} False{} False{}:
      mbsrc(dfs, src, fa, T, cs, O, N, o, rp, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, ex, ef, eg)

# ---------------------------------------------------------------------------
# The String mode
# ---------------------------------------------------------------------------

def mssrc(+dfs: B.Defs, +src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.src(P.mkSrcs(src), o, s, qs, ql, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match src:
    case Nil{}:
      (StM(dfs, o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, ({==}, ({==}, (%Equal.sym(Bool, R.RunSt.halt(s), False{}, hx) : {Bool.or(_, False{}) == False{} : Bool}; {==}, (hg, ({==}, ({==}, Unit{})))))))))))
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      adv.ms.sb(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)
    case Con{P.SLP{+q}, +rest}:
      adv.ms.sl(dfs, fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)
    case Con{P.SRP{+l}, +rest}:
      MR.ms_sr(dfs, fa, T, cs, O, N, o, s, qs, ql, l, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      MR.ms_spp(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)


def msfull(+dfs: B.Defs, +full: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.full(full, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match full:
    case True{}:
      (StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (%Equal.sym(Bool, R.RunSt.halt(s), False{}, hx) : {Bool.or(_, False{}) == False{} : Bool}; {==}, ({==}, (hg, ({==}, ({==}, Unit{}))))))))))
    case False{}:
      mssrc(dfs, src, fa, T, cs, O, N, o, s, qs, ql, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

def ms.k(+dfs: B.Defs, +x: Bool, +code: Maybe<&2, Nat>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +ex: {R.RunSt.halt(s) == x : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.adv(x, o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)):
  match x code:
    case _ Some{+c}:
      (StM(dfs, o, S.MSP{s, qs, ql, Some{c}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (W.or_r(R.RunSt.halt(s), True{}, {==}), ({==}, (hg, ({==}, ({==}, Unit{}))))))))))
    case True{} None{}:
      (StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (W.or_l(R.RunSt.halt(s), False{}, ex), ({==}, (hg, ({==}, ({==}, Unit{}))))))))))
    case False{} None{}:
      msfull(dfs, Nat.is_le(Norm.lim(), ql), fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, ex)

# ---------------------------------------------------------------------------
# adv_ok
# ---------------------------------------------------------------------------

def adv(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, p, Norm.advance(S.mkSt(fa, p))):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      %Equal.sym(NR.Run & Norm.Rs, Norm.Run.rs(P.mkRun(rp)), (P.mkRun(rp), Norm.Rs{P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp))}), rs_eq(rp)) :
        S.AdvG(fa, T, cs, O, N, StM(dfs, o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), Norm.mb.rs(_, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))
      mb.k(dfs, P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp)), fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, {==}, {==}, {==})
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      ms.k(dfs, R.RunSt.halt(s), code, fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, {==})
