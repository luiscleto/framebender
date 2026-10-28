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
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ./proof_b_adv_fast.bend as FA
import ./proof_b_adv_msx.bend as MX

# adv_ok's proof (proof_b_sim.bend calls adv): handling the next line keeps a
# good state standing for the same report. By cases on advance's paths:
#   - the byte mode: the run stopped (Ended), wrote 2^30 bytes (Yield), has
#     a big buffer (to the String mode), no source (Idle), a text line (to
#     the String mode), a byte source (the line paths: adv.mb.sb);
#   - the String mode: finished or stopped (Ended), wrote 2^30 bytes
#     (Yield), no source (Idle), a byte source (adv.ms.sb), a text line
#     (adv.ms.sl).
# Every variable of the helpers is reusable.

def StM(+o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed}

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
def adv.fast(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.fast.pre(back, o, P.mkRun(rp), at, NF.line(C.BT(len, t), at), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed)):
  FA.F.top(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin)

def adv.mb.if(+i: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +ei: {P.RunP.i(rp) == i : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.body.if(i, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)
    case True{}:
      adv.fast(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, ei)

# The byte mode, a byte source: the line at at (fast path in the body,
# else the decoded path: header lines, a source with no complete line, a
# line too long, the slow path).
def adv.mb.sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(rp)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed)):
  %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), DE.inb_eq(rp)) :
    S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
      Norm.body.k(back, o, _, C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed))
  adv.mb.if(P.RunP.i(rp), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig, {==})

# The String mode, a byte source.
def adv.ms.sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed)):
  MX.ms_sb(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

# The String mode, a text line.
def adv.ms.sl(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  MX.ms_sl(fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

# ---------------------------------------------------------------------------
# The byte mode
# ---------------------------------------------------------------------------

def mbsrc(+src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed),
    Norm.mb.src(P.mkSrcs(src), o, P.mkRun(rp), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match src:
    case Nil{}:
      (StM(o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, ({==}, ({==}, (hx, (hg, ({==}, W.moved_keep(fa, cs, rp, StM(o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), StM(o, S.MBP{rp}, Nil{}, pd, eof, back, wp, asked, fneed), {==})))))))))))
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      adv.mb.sb(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hf, hbig)
    case Con{P.SLP{+q}, +rest}:
      TS.to_ms_went(fa, T, cs, O, N, o, rp, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed, back, fneed, hw, hr, hg, hx)

def mb.k(+x: Bool, +f: Bool, +g: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +ex: {P.RunP.x(rp) == x : Bool},
  +ef: {U32.is_le(1073741824, P.RunP.ow(rp)) == f : Bool},
  +eg: {U32.is_le(536870912, P.RunP.obl(rp)) == g : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed),
    Norm.mb.rs((P.mkRun(rp), Norm.Rs{x, f, g}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match x f g:
    case True{} _ _:
      (StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (ex, ({==}, (hg, {==}))))))))
    case False{} True{} _:
      (StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (ex, ({==}, (hg, {==}))))))))
    case False{} False{} True{}:
      TS.to_ms_went(fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, back, fneed, hw, hr, hg, ex)
    case False{} False{} False{}:
      mbsrc(src, fa, T, cs, O, N, o, rp, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, ex, ef, eg)

# ---------------------------------------------------------------------------
# The String mode
# ---------------------------------------------------------------------------

def mssrc(+src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.src(P.mkSrcs(src), o, s, qs, ql, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match src:
    case Nil{}:
      (StM(o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, ({==}, ({==}, (%Equal.sym(Bool, R.RunSt.halt(s), False{}, hx) : {Bool.or(_, False{}) == False{} : Bool}; {==}, (hg, ({==}, Unit{}))))))))))
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      adv.ms.sb(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)
    case Con{P.SLP{+q}, +rest}:
      adv.ms.sl(fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

def msfull(+full: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.full(full, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match full:
    case True{}:
      (StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (%Equal.sym(Bool, R.RunSt.halt(s), False{}, hx) : {Bool.or(_, False{}) == False{} : Bool}; {==}, ({==}, (hg, {==}))))))))
    case False{}:
      mssrc(src, fa, T, cs, O, N, o, s, qs, ql, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx)

def ms.k(+x: Bool, +code: Maybe<&2, Nat>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +ex: {R.RunSt.halt(s) == x : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.adv(x, o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)):
  match x code:
    case _ Some{+c}:
      (StM(o, S.MSP{s, qs, ql, Some{c}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (W.or_r(R.RunSt.halt(s), True{}, {==}), ({==}, (hg, {==}))))))))
    case True{} None{}:
      (StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed), ({==}, (hw, (hr, ({==}, (W.or_l(R.RunSt.halt(s), False{}, ex), ({==}, (hg, {==}))))))))
    case False{} None{}:
      msfull(Nat.is_le(Norm.lim(), ql), fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, ex)

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
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      %Equal.sym(NR.Run & Norm.Rs, Norm.Run.rs(P.mkRun(rp)), (P.mkRun(rp), Norm.Rs{P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp))}), rs_eq(rp)) :
        S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), Norm.mb.rs(_, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed))
      mb.k(P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp)), fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, {==}, {==}, {==})
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      ms.k(R.RunSt.halt(s), code, fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, {==})
