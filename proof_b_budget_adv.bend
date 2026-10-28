import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv.bend as A
import ./proof_b_adv_dec.bend as DE
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_b_budget_fast.bend as BFa
import ./proof_b_budget_ms.bend as BMS
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

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
def to_ms_c(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed}}):
  +ls = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  (%Equal.sym(Bool, BN.fast_left(Norm.to_ms(P.mkRun(rp)), fneed), False{}, fl_ms(rp, fneed)) :
     {Nat.is_le(BN.WA.ls(fa, _, back, PC.mkWin(fa, wp), None{}, ls), BN.WA.ls(fa, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, ls)) == True{} : Bool}
   wa_fl(fa, Bool.not(fneed), back, wp, None{}, ls),
   hbi)

def ss_mk(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP) -> {Nat.is_le(BN.WAS(fa, S.mkSt(fa, p), cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}:
  N.le_refl(BN.WAS(fa, S.mkSt(fa, p), cs))

# ---------------------------------------------------------------------------
# The line paths (to come)
# ---------------------------------------------------------------------------

def c.mb.if(+i: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +ei: {P.RunP.i(rp) == i : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body.if(i, back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case True{}:
      BFa.c.fast(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, ei, hbi)

def c.mb.sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body.k(back, o, Norm.Run.inbody(P.mkRun(rp)), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed)):
  %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), DE.inb_eq(rp)) :
    BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
      Norm.body.k(back, o, _, C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp), fneed))
  c.mb.if(P.RunP.i(rp), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, {==}, hb, hw, hr, hg, hx, hbig, hbi)

def c.ms.sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed)):
  BMS.c_ms_sb(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

def c.ms.sl(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  BMS.c_ms_sl(fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

# ---------------------------------------------------------------------------
# The dispatch (as proof_b_adv.bend's)
# ---------------------------------------------------------------------------

def c.mbsrc(+src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hf: {U32.is_le(1073741824, P.RunP.ow(rp)) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed),
    Norm.mb.src(P.mkSrcs(src), o, P.mkRun(rp), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed)):
  match src:
    case Nil{}:
      (ss_mk(fa, cs, BD.StM(o, S.MBP{rp}, Nil{}, pd, eof, back, wp, None{}, fneed)), hbi)
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      c.mb.sb(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hf, hbig, hbi)
    case Con{P.SLP{+q}, +rest}:
      to_ms_c(fa, cs, o, rp, Con{P.SLP{q}, rest}, pd, eof, back, wp, fneed, hbi)

def c.mb.k(+x: Bool, +f: Bool, +g: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +ex: {P.RunP.x(rp) == x : Bool},
  +ef: {U32.is_le(1073741824, P.RunP.ow(rp)) == f : Bool},
  +eg: {U32.is_le(536870912, P.RunP.obl(rp)) == g : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed),
    Norm.mb.rs((P.mkRun(rp), Norm.Rs{x, f, g}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed)):
  match x f g:
    case True{} _ _:
      (ss_mk(fa, cs, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case False{} True{} _:
      ({==}, (ef, hbi))
    case False{} False{} True{}:
      to_ms_c(fa, cs, o, rp, src, pd, eof, back, wp, fneed, hbi)
    case False{} False{} False{}:
      c.mbsrc(src, fa, T, cs, O, N, o, rp, pd, eof, back, wp, fneed, hb, hw, hr, hg, ex, ef, eg, hbi)

def c.mssrc(+src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.src(P.mkSrcs(src), o, s, qs, ql, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed)):
  match src:
    case Nil{}:
      (ss_mk(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, eof, back, wp, None{}, fneed)), hbi)
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      c.ms.sb(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)
    case Con{P.SLP{+q}, +rest}:
      c.ms.sl(fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

def c.msfull(+full: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +ef: {Nat.is_le(Norm.lim(), ql) == full : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.full(full, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed)):
  match full:
    case True{}:
      ({==}, (ef, hbi))
    case False{}:
      c.mssrc(src, fa, T, cs, O, N, o, s, qs, ql, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)

def c.ms.k(+x: Bool, +code: Maybe<&2, Nat>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +ex: {R.RunSt.halt(s) == x : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, code}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.adv(x, o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed)):
  match x code:
    case _ Some{+c}:
      (ss_mk(fa, cs, BD.StM(o, S.MSP{s, qs, ql, Some{c}}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case True{} None{}:
      (ss_mk(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), hbi)
    case False{} None{}:
      c.msfull(Nat.is_le(Norm.lim(), ql), fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, fneed, {==}, hb, hw, hr, hg, ex, hbi)


def none_some(+r: List<&2, Pr.Req>, +h: {Some{r} == None{} : Maybe<&2, List<&2, Pr.Req>>}) -> Empty:
  N.true_ne_false(Equal.cong(Maybe<&2, List<&2, Pr.Req>>, Bool, m => Maybe.is_some(&2, List<&2, Pr.Req>, m), Some{r}, None{}, h))

def c.top(+asked: Maybe<&2, List<&2, Pr.Req>>, +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>},
  +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed), Norm.advance(S.mkSt(fa, BD.StM(o, md, src, pd, eof, back, wp, asked, fneed)))):
  match asked md:
    case Some{+r} _:
      Empty.absurd(BD.AdvC(fa, cs, BD.StM(o, md, src, pd, eof, back, wp, Some{r}, fneed), Norm.advance(S.mkSt(fa, BD.StM(o, md, src, pd, eof, back, wp, Some{r}, fneed)))), none_some(r, ha))
    case None{} S.MBP{+rp}:
      %Equal.sym(NR.Run & Norm.Rs, Norm.Run.rs(P.mkRun(rp)), (P.mkRun(rp), Norm.Rs{P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp))}), A.rs_eq(rp)) :
        BD.AdvC(fa, cs, BD.StM(o, S.MBP{rp}, src, pd, eof, back, wp, None{}, fneed), Norm.mb.rs(_, o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed))
      c.mb.k(P.RunP.x(rp), U32.is_le(1073741824, P.RunP.ow(rp)), U32.is_le(536870912, P.RunP.obl(rp)), fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, {==}, {==}, {==}, hbi)
    case None{} S.MSP{+s, +qs, +ql, +code}:
      c.ms.k(R.RunSt.halt(s), code, fa, T, cs, O, N, o, s, qs, ql, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, {==}, hbi)

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
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      c.top(asked, ha, fa, T, cs, O, N, o, md, src, pd, eof, back, wp, fneed, hb, hw, hr, hg, hbi)

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
