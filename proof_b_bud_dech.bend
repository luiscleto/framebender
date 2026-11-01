import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_wr.bend as WR
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_part.bend as DPT
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_mb.bend as BM
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_split.bend as ASP
import ./proof_b_budget_lem.bend as BL
import ./proof_b_bud_vd.bend as BV
import ./proof_s_recs.bend as RSC
import ./proof_b_bud_split.bend as BS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The budget walk's decoded paths (proof_b_budget_dec.bend's c.dec), as
# proof_b_adv_dec.bend walks them for adv_ok. The leaves: a line handled
# (went_done, any state after it); the text kept with the String mode taken
# (the fast path's term goes); the text moved to the line end (WA and bi
# equal); a Want (vd_bud: its flag flips pay its step and reads). Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# WA's shape (as proof_b_budget_adv.bend's, which imports this file's user)
# ---------------------------------------------------------------------------

def rem_fl(+g: Bool, +fl: Bool, +rw: Nat, +X: Nat, +Y: Nat) ->
  {Nat.is_le(BN.pick(g, Nat.add(Nat.add(BN.pick(False{}, rw), X), Y)), BN.pick(g, Nat.add(Nat.add(BN.pick(fl, rw), X), Y))) == True{} : Bool}:
  match g:
    case True{}:
      N.le_add_mono_r(Y, X, Nat.add(BN.pick(fl, rw), X), N.le_add_l(X, BN.pick(fl, rw)))
    case False{}:
      {==}

def wa_fl(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) ->
  {Nat.is_le(BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), asked, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), asked, ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +tl:
      N.le_add_mono_r(BN.LAs(fa, tl), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), asked, l), BN.rem(fa, fl, back, PC.mkWin(fa, wp), asked, l),
        rem_fl(BN.lgate(l), fl, BN.RW(l), BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), asked, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)),
          Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa)))))

def fl_mso(s: R.RunSt, qs: List<&2, String>, +ql: Nat, +f: Bool) -> {BN.fast_left(Norm.ms.out(s, qs, ql), f) == False{} : Bool}:
  match s:
    case R.RunSt{n0, i, h, c, e, l, b, k, o, ns, x}:
      {==}

def fl_ms(+rp: P.RunP, +f: Bool) -> {BN.fast_left(Norm.to_ms(P.mkRun(rp)), f) == False{} : Bool}:
  fl_mso(NR.to_spec(P.mkRun(rp)), Nil{}, 0n, f)

# bi holds once back is 0.
def bi0(+fa: List<&2, B.Contig>, +wp: PC.WP, +ls: List<&2, B.Line>) -> {BN.bi.ls(0n, PC.mkWin(fa, wp), None{}, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +tl}:
      {==}

# A Want's share, with the fast path's term on both sides and the lines
# after it.
def want_le(+g: Bool, +fl: Bool, +rw: Nat, +H2: Nat, +Z2: Nat, +H1: Nat, +Z1: Nat, +k: Nat, +Lr: Nat,
  +h: {Nat.is_le(Nat.add(k, BN.pick(g, Nat.add(Nat.add(BN.pick(False{}, rw), H2), Z2))), BN.pick(g, Nat.add(Nat.add(BN.pick(False{}, rw), H1), Z1))) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(k, Nat.add(BN.pick(g, Nat.add(Nat.add(BN.pick(fl, rw), H2), Z2)), Lr)), Nat.add(BN.pick(g, Nat.add(Nat.add(BN.pick(fl, rw), H1), Z1)), Lr)) == True{} : Bool}:
  match g:
    case False{}:
      +hk0 = {%N.add_zero(k) : {Nat.is_le(_, 0n) == True{} : Bool}; h : {Nat.is_le(k, 0n) == True{} : Bool}}
      N.le_add_mono_r(Lr, k, 0n, hk0)
    case True{}:
      +F = BN.pick(fl, rw)
      +h2 = {%Equal.sym(Nat, Nat.add(Nat.add(F, H2), Z2), Nat.add(F, Nat.add(H2, Z2)), N.add_assoc(F, H2, Z2)) : {Nat.is_le(Nat.add(k, _), Nat.add(Nat.add(F, H1), Z1)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(Nat.add(F, H1), Z1), Nat.add(F, Nat.add(H1, Z1)), N.add_assoc(F, H1, Z1)) : {Nat.is_le(Nat.add(k, Nat.add(F, Nat.add(H2, Z2))), _) == True{} : Bool};
        %N.add_left_comm(F, k, Nat.add(H2, Z2)) : {Nat.is_le(_, Nat.add(F, Nat.add(H1, Z1))) == True{} : Bool};
        N.le_add_mono_l(F, Nat.add(k, Nat.add(H2, Z2)), Nat.add(H1, Z1), h) : {Nat.is_le(Nat.add(k, Nat.add(Nat.add(F, H2), Z2)), Nat.add(Nat.add(F, H1), Z1)) == True{} : Bool}}
      %N.add_assoc(k, Nat.add(Nat.add(F, H2), Z2), Lr) : {Nat.is_le(_, Nat.add(Nat.add(Nat.add(F, H1), Z1), Lr)) == True{} : Bool}
      N.le_add_mono_r(Lr, Nat.add(k, Nat.add(Nat.add(F, H2), Z2)), Nat.add(Nat.add(F, H1), Z1), h2)

# A zero window held (bi's) is a window holding 0 .. e (vd_bud's).
def zh_hw(w: Norm.Win, +c: String, +e: Nat, +h: {BN.zheld(w, c, e) == True{} : Bool}) -> {BN.holdsW(w, c, 0n, e) == True{} : Bool}:
  match w:
    case Norm.WNone{}:
      Empty.absurd({BN.holdsW(Norm.WNone{}, c, 0n, e) == True{} : Bool}, W.ft(h))
    case Norm.WUnk{+c0}:
      Empty.absurd({BN.holdsW(Norm.WUnk{c0}, c, 0n, e) == True{} : Bool}, W.ft(h))
    case Norm.WKnown{+c0, cb, +a0, +b0, +clen, off, raw, offu, rlen, clenu}:
      W.and_l(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen))), Nat.is_le(e, clen), h)
    case Norm.WStr{+c0, +a0, +b0, +clen, off, raw}:
      W.and_l(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen))), Nat.is_le(e, clen), h)

def orz(+a: Bool, w: Norm.Win, +c: String, +e: Nat, +h: {Bool.or(a, BN.zheld(w, c, e)) == True{} : Bool}) ->
  {Bool.or(a, BN.holdsW(w, c, 0n, e)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      zh_hw(w, c, e, h)

# The lines to come: the line at at, then those after its LF.
def lcons(+hold: Bool, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +cs: List<&2, String>,
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  {BM.AP(hold, len, t, d, at, rest, pd, eof, cs) == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> BM.AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs) : List<&2, B.Line>}:
  BM.allx(hold, len, t, d, at, j, rest, pd, eof, cs, hsp, hn)

# ---------------------------------------------------------------------------
# The leaves
# ---------------------------------------------------------------------------

# A line handled (done.b): whatever the run after it.
def CW(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  x: NR.Run,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MB{x}, Con{Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrc(LI.SXP(hold, len, t, d, (j + 1 : U32))), HX.so_eq(hold, len, t, d, (j + 1 : U32))) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
      Norm.Went{Norm.St{o, Norm.MB{x}, Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}})
  (BM.went_ap(hold, fa, o, cs, Bool.not(fneed), back, wp, None{}, True{}, 0n, wp, None{}, len, t, d, at, j, rest, pd, eof, hsp, hn),
    bi0(fa, wp, BM.AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs)))

# The String mode taken, the text and back kept.
def TMC(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +f2: Bool,
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.to_ms(Norm.retick(hold, P.mkRun(rp))), Con{Norm.Src.of(hold, C.BT(len, t), at), P.mkSrcs(rest)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, f2, dfs}}):
  +ls = BM.AP(hold, len, t, d, at, rest, pd, eof, cs)
  %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), at), P.mkSrc(LI.SXP(hold, len, t, d, at)), HX.so_eq(hold, len, t, d, at)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.to_ms(Norm.retick(hold, P.mkRun(rp))), Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, f2, dfs}})
  (%Equal.sym(Bool, BN.fast_left(Norm.to_ms(Norm.retick(hold, P.mkRun(rp))), f2), False{}, fl_mso(NR.to_spec(Norm.retick(hold, P.mkRun(rp))), Nil{}, 0n, f2)) :
     {Nat.is_le(BN.WAX(fa, o, _, back, PC.mkWin(fa, wp), None{}, ls), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, ls)) == True{} : Bool};
   BM.wax_le(fa, o, False{}, back, wp, None{}, Bool.not(fneed), back, wp, None{}, ls, wa_fl(fa, Bool.not(fneed), back, wp, None{}, ls)),
   hbi)

# The source's text moves to the line end.
def Q2(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +rest: List<&2, P.SrcP>, +pd2: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool) -> S.StP:
  BD.StM(dfs, o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed)

def CPT.pa(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  pa: DPT.PAW(pd, len, t, at),
  +hnr: LI.HNE(False{}, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  match pa:
    case (+pd2, q):
      match q:
        case (eadd, q2):
          match q2:
            case (hpd2, htx):
              +q2p = Q2(dfs, o, rp, rest, pd2, eof, back, wp, fneed)
              +eqT = Equal.trans(String, BM.TP(q2p, cs), S.intext(q2p, cs), BM.TP(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), BL.text_pic(q2p, cs, W.nr_first(rest, W.W8_nr(fa, o, S.MBP{rp}, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed, dfs, BL.w8_of(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), hw)))),
                Equal.trans(String, S.intext(q2p, cs), S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), BM.TP(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs),
                  DPT.DP.tq(dfs, rest, fa, cs, o, rp, len, t, d, at, pd, eof, back, wp, None{}, fneed, fneed, hw, hn, hsa, pd2, htx),
                  Equal.sym(String, BM.TP(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), BL.text_pic(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs, BL.rf_of(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), hw)))))
              %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) :
                BD.AdvC(fa, cs, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), _, eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}})
              +hnr = W.W8_nr(fa, o, S.MBP{rp}, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed, dfs, BL.w8_of(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), hw))
              +eal = Equal.sym(List<&2, B.Line>, BN.ALL(P.mkSrcs(rest), P.mkPd(pd2), eof, cs), BN.lines(P.mkSrcs(rest), P.mkPd(pd2), eof, cs), BL.all_nr(rest, pd2, eof, cs, hnr))
              ({%eal : {Nat.is_le(BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, _), BN.WAS(fa, S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool};
                %Equal.sym(String, BM.TP(q2p, cs), BM.TP(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), eqT) :
                  {Nat.is_le(BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, B.Text.lines(_)), BN.WAS(fa, S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool};
                N.le_refl(BN.WAS(fa, S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) : {Nat.is_le(BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(rest), P.mkPd(pd2), eof, cs)), BN.WAS(fa, S.mkSt(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool}},
               {%eal : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, _) == True{} : Bool};
                %Equal.sym(String, BM.TP(q2p, cs), BM.TP(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), cs), eqT) : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, B.Text.lines(_)) == True{} : Bool};
                hbi : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(rest), P.mkPd(pd2), eof, cs)) == True{} : Bool}})

def CPT(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjl: {n(len) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  sn: DPT.SNW(len, t, d, at),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, (C.BT(len, t), len), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match hold:
    case True{}:
      Empty.absurd(BD.AdvC(fa, cs, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
        Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, (C.BT(len, t), len), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed)),
        HX.part_sp(dfs, fa, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed, hw, hjl, hnr))
    case False{}:
      match sn:
        case (hn, hsa):
          +hfit = {%Equal.sym(Nat, n((len - at : U32)), Nat.sub(n(len), n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool};
            %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(len), n(at))), n(len), N.le_sub_add(n(at), n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, n(len)) == True{} : Bool};
            N.le_refl(n(len)) : {Nat.is_le(Nat.add(n(at), n((len - at : U32))), n(len)) == True{} : Bool}}
          CPT.pa(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hn, hsa, LN.pend_add(pd, len, t, d, at, (len - at : U32), W.c9_2(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W2(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W3(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W4(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W5(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W6(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W7(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W8(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), hw), hok, hfit), hnr)

# A Want: vd_bud's share, on the line WA counts.
def K.vw(+hold: Bool, +dfs: B.Defs, +reqs: List<&2, Pr.Req>, +b2: Nat, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), Norm.VWant{PC.mkWin(fa, wp), reqs, b2}),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.want.b(o, P.mkRun(rp), C.BT(len, t), at, b2, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), reqs, fneed)):
  match vb:
    case (vb1, vb2):
      +e1 = lcons(hold, dfs, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, fneed, cs, hsp, hn, hnr)
      +FL = Bool.not(fneed)
      +KQ = {1n+List.length(&2, Pr.Req, reqs) : Nat}
      +LR = BN.LAs(fa, BM.AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs))
      +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
      +g1 = {%Equal.sym(List<&2, B.Line>, BM.AP(hold, len, t, d, at, rest, pd, eof, cs), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> BM.AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs), e1) :
          {Nat.is_le(Nat.add(KQ, BN.WA.ls(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, _)), BN.WA.ls(fa, FL, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool};
        %LN.line_eq(P.btext(len, t, at, (j - at : U32))) :
          {Nat.is_le(Nat.add(KQ, Nat.add(BN.rem(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, _), LR)), Nat.add(BN.rem(fa, FL, back, PC.mkWin(fa, wp), None{}, _), LR)) == True{} : Bool};
        want_le(BN.lgate(l), FL, BN.RW(l),
          BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), Some{reqs}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)), Nat.add(BN.pick(Nat.is_eq(b2, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(b2, BN.lpos(l)), BN.ZW(fa))),
          BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), None{}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)), Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa))),
          KQ, LR, vb1) :
          {Nat.is_le(Nat.add(KQ, BN.WA.ls(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, BM.AP(hold, len, t, d, at, rest, pd, eof, cs))), BN.WA.ls(fa, FL, back, PC.mkWin(fa, wp), None{}, BM.AP(hold, len, t, d, at, rest, pd, eof, cs))) == True{} : Bool}}
      +g2 = {%Equal.sym(List<&2, B.Line>, BM.AP(hold, len, t, d, at, rest, pd, eof, cs), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> BM.AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs), e1) : {BN.bi.ls(b2, PC.mkWin(fa, wp), Some{reqs}, _) == True{} : Bool};
        %LN.line_eq(P.btext(len, t, at, (j - at : U32))) : {Bool.or(Nat.is_eq(b2, 0n), BN.heldZ(PC.mkWin(fa, wp), Some{reqs}, BN.lchrom(_), BN.lend(_))) == True{} : Bool};
        vb2 : {BN.bi.ls(b2, PC.mkWin(fa, wp), Some{reqs}, BM.AP(hold, len, t, d, at, rest, pd, eof, cs)) == True{} : Bool}}
      %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), at), P.mkSrc(LI.SXP(hold, len, t, d, at)), HX.so_eq(hold, len, t, d, at)) :
        BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.Want{Norm.St{o, Norm.MB{Norm.retick(hold, P.mkRun(rp))}, Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, b2, PC.mkWin(fa, wp), Some{reqs}, fneed, dfs}, reqs})
      (BM.wax_want(fa, o, KQ, FL, b2, wp, Some{reqs}, FL, back, wp, None{}, BM.AP(hold, len, t, d, at, rest, pd, eof, cs), g1), g2)

def K.same.d(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +rp1: P.RunP,
  dw: SLW.DW(rp1, o, len, t, at, j, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, (P.mkRun(rp1), P.RunP.n(rp1)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          %Equal.sym(NR.Run & D.Bytes, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
            BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
          CW(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, P.mkRun(rp2), hnr)

def K.same.t(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hrj: {B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}} == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, NR.Run.n(NR.tick(P.mkRun(rp))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, SLW.hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = SLW.f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = SLW.f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.same_done(o, NR.Run.n(_), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.same_done(o, _, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  K.same.d(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, rp1, PR.run_same_done(rp1, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hs, hfl, hal, hlt), hbig1, hk, hcb, hcl), hnr)

def K.same(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hrj: {B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}} == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res},
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, Norm.ticked(P.mkRun(rp)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          K.same.t(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hrj, rp1, et, i1, s1, obl1, hnr)

def K.body.d(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +rp1: P.RunP,
  dw: SLW.DW(rp1, o, len, t, at, j, r, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, (P.mkRun(rp1), P.RunP.n(rp1)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          %Equal.sym(NR.Run & D.Bytes, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
            BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
          CW(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, P.mkRun(rp2), hnr)

def K.body.t(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hfit: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +hrj: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, NR.Run.n(NR.tick(P.mkRun(rp))), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, SLW.hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = SLW.f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = SLW.f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  +hfit1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {Norm.res_fits(r, l, (1073741824 - _ : U32)) == True{} : Bool}; hfit : {Norm.res_fits(r, l, (1073741824 - P.RunP.obl(rp1) : U32)) == True{} : Bool}}
  +hres = hrj
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.body_done(r, o, NR.Run.n(_), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.body_done(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  K.body.d(hold, dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, rp1, PR.run_body_line(rp1, r, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hs, hfl, hal, hlt), hbig1, hk, hfit1, hres, hcb, hcl), hnr)

def K.body(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hfit: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +hrj: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, Norm.ticked(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          K.body.t(hold, dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hfit, hrj, rp1, et, i1, s1, obl1, hnr)

# ---------------------------------------------------------------------------
# The slow path's verdict
# ---------------------------------------------------------------------------

def K.fit(+hold: Bool, +dfs: B.Defs, +fits: Bool, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hrj: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +ef: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == fits : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.fits(fits, r, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match fits:
    case False{}:
      TMC(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, False{}, hnr)
    case True{}:
      K.body(hold, dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, ef, hrj, PR.run_tick(rp, hi), hnr)

def K.vr(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hrj: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.body.res(r, o, Norm.Run.oblen(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  %Equal.sym(NR.Run & U32, Norm.Run.oblen(P.mkRun(rp)), (P.mkRun(rp), P.RunP.obl(rp)), SLW.oblen_eq(rp)) :
    BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.body.res(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  K.fit(hold, dfs, Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)), r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hrj, {==}, hnr)

def K.v(+hold: Bool, +dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  hk: MSX.vdOK(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v),
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v)),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
      K.vr(hold, dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin,
        {%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hk) : {E.is_bytes(P.res_text(_)) == True{} : Bool}; SLW.judge_bytes(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, SLW.body_bytes(P.btext(len, t, at, (j - at : U32)), hby)) : {E.is_bytes(P.res_text(r)) == True{} : Bool}}, hnr)
    case MSX.VSP{}:
      K.same(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk, PR.run_tick(rp, hi), hnr)
    case MSX.VWP{+reqs, +b2}:
      K.vw(hold, dfs, reqs, b2, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, vb, hnr)

def K.sv(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  h: MSX.VdG(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))),
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(Norm.line(P.btext(len, t, at, (j - at : U32)))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))))):
  match h:
    case (+v, q):
      match q:
        case (ev, hk):
          +evc = Equal.trans(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), MSX.mkVd(fa, wp, v), ev, {==})
          %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), evc) :
            BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, _))
          K.v(hold, dfs, v, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk, AB.subst(Norm.Vd, z => BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), evc, vb), hnr)

# WF's 7th test (the window), and bi's zero window for the line.
def K.hv(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) -> {PC.wp_ok(fa, wp) == True{} : Bool}:
  +p = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)
  W.c9_6(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)

def K.e1(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +cs: List<&2, String>,
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(Norm.line(P.btext(len, t, at, (j - at : U32)))), 0n, BN.lend(Norm.line(P.btext(len, t, at, (j - at : U32)))))) == True{} : Bool}:
  +e1 = lcons(hold, dfs, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, fneed, cs, hsp, hn, hnr)
  {%Equal.sym(B.Line, Norm.line(P.btext(len, t, at, (j - at : U32))), B.Text.line(P.btext(len, t, at, (j - at : U32))), LN.line_eq(P.btext(len, t, at, (j - at : U32)))) : {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(_), 0n, BN.lend(_))) == True{} : Bool};
    orz(Nat.is_eq(back, 0n), PC.mkWin(fa, wp), BN.lchrom(B.Text.line(P.btext(len, t, at, (j - at : U32)))), BN.lend(B.Text.line(P.btext(len, t, at, (j - at : U32)))),
      %e1 : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, _) == True{} : Bool}; hbi) :
    {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(Norm.line(P.btext(len, t, at, (j - at : U32)))), 0n, BN.lend(Norm.line(P.btext(len, t, at, (j - at : U32)))))) == True{} : Bool}}

# A result's text is bytes once -m refuses the line (unsplit.res: judge's, or
# the line passed as it came).
def ub(b: Bool, +r: B.Res, +x: B.Res, +hr: {E.is_bytes(P.res_text(r)) == True{} : Bool}, +hx: {E.is_bytes(P.res_text(x)) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(Bool.pick(B.Res, b, r, x))) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      hx

# A line -m refuses (code c): its verdict, as vd.unsplit gives it.
def K.vu(+hold: Bool, +c: B.Code, +strict: Bool, +v: MSX.VdP, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  hk: MSX.vdOK(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v),
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v)),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, MSX.mkVd(fa, wp, MSX.vdU(c, strict, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)))):
  match v:
    case MSX.VRP{+r}:
      +hbb = SLW.body_bytes(P.btext(len, t, at, (j - at : U32)), hby)
      +X = {B.Res{B.Problem{c}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}} : B.Res}
      +hr = {%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hk) : {E.is_bytes(P.res_text(_)) == True{} : Bool}; SLW.judge_bytes(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, hbb) : {E.is_bytes(P.res_text(r)) == True{} : Bool}}
      K.vr(hold, dfs, Norm.unsplit.res(c, strict, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), r), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin,
        ub(Norm.stops(r, strict), r, X, hr, hbb), hnr)
    case MSX.VSP{}:
      +hbb = SLW.body_bytes(P.btext(len, t, at, (j - at : U32)), hby)
      K.vr(hold, dfs, B.Res{B.Problem{c}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hbb, hnr)
    case MSX.VWP{+reqs, +b2}:
      K.vw(hold, dfs, reqs, b2, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, vb, hnr)

def K.su(+hold: Bool, +c: B.Code, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  h: MSX.VdG(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))),
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(Norm.line(P.btext(len, t, at, (j - at : U32)))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back,
      Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))))):
  match h:
    case (+v, q):
      match q:
        case (+ev, hk):
          %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), ev) : BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), _)))
          %Equal.sym(Norm.Vd, Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), MSX.mkVd(fa, wp, v)), MSX.mkVd(fa, wp, MSX.vdU(c, R.Opts.strict(o), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)), MSX.vdu_eq(fa, wp, c, R.Opts.strict(o), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)) : BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed, back, _))
          K.vu(hold, c, R.Opts.strict(o), v, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk, AB.subst(Norm.Vd, z => BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), ev, vb), hnr)

# The records of a line split on its text (inject.r): its rem and extra
# allowance pay for theirs; back is 0.
def K.injr(+hold: Bool, +ps: List<&2, String>, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hpt: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == B.Pieces{ps} : B.Parts},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.inject.r(o, P.mkRun(rp), C.BT(len, t), j, ps, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match hold:
    case True{}:
      Empty.absurd(BD.AdvC(fa, cs, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
          Norm.inject.r(o, P.mkRun(rp), C.BT(len, t), j, ps, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp))),
        ASP.sp_abs(dfs, o, len, t, d, at, j, rest, ps, BL.rf_of(fa, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), hw),
          {%LN.line_eq(P.btext(len, t, at, (j - at : U32))) : {B.Rec.parts(dfs, o, B.Line.body(_)) == B.Pieces{ps} : B.Parts}; hpt : {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Pieces{ps} : B.Parts}},
          (hsp, (hn, (hle, hby)))))
    case False{}:
      +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
      +tm = B.Line.term(l)
      +post = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed)
      +LP = B.Text.lines(BM.TP(post, cs))
      +AN = BN.ALL(Norm.recs_src(ps, tm, P.mkSrcs(Con{P.SBP{len, t, d, (j + 1 : U32)}, rest})), P.mkPd(pd), eof, cs)
      +ea = BS.all_rs(ps, tm, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, cs)
      +epre = BM.tpl(dfs, cs, o, S.MBP{rp}, S.MBP{rp}, len, t, d, at, j, rest, pd, eof, back, back, wp, wp, None{}, None{}, fneed, fneed, hsp, hn)
      ({%Equal.sym(List<&2, B.Line>, AN, List.append(&2, B.Line, RSC.LS(ps, tm), LP), ea) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, _), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, BM.AP(False{}, len, t, d, at, rest, pd, eof, cs))) == True{} : Bool};
        %Equal.sym(List<&2, B.Line>, BM.AP(False{}, len, t, d, at, rest, pd, eof, cs), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> LP, epre) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, RSC.LS(ps, tm), LP)), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool};
        %LN.line_eq(P.btext(len, t, at, (j - at : U32))) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, List.append(&2, B.Line, RSC.LS(ps, tm), LP)), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, _ <> LP)) == True{} : Bool};
        BS.split_le(fa, o, l, ps, tm, LP, Bool.not(fneed), back, wp, None{}, True{}, 0n, wp, None{}, BS.parts_spf(dfs, o, l, ps, hpt)) :
          {Nat.is_le(BN.WAX(fa, o, True{}, 0n, PC.mkWin(fa, wp), None{}, AN), BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, BM.AP(False{}, len, t, d, at, rest, pd, eof, cs))) == True{} : Bool}},
       BM.bi0(fa, wp, None{}, AN))

# The line whole (as without -m): its verdict.
def K.whole(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.whole(back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  +e1 = lcons(hold, dfs, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, fneed, cs, hsp, hn, hnr)
  +hv = W.c9_6(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W2(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W3(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W4(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W5(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W6(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W7(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W8(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), hw)
  +hbl = {%Equal.sym(B.Line, Norm.line(P.btext(len, t, at, (j - at : U32))), B.Text.line(P.btext(len, t, at, (j - at : U32))), LN.line_eq(P.btext(len, t, at, (j - at : U32)))) : {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(_), 0n, BN.lend(_))) == True{} : Bool};
    orz(Nat.is_eq(back, 0n), PC.mkWin(fa, wp), BN.lchrom(B.Text.line(P.btext(len, t, at, (j - at : U32)))), BN.lend(B.Text.line(P.btext(len, t, at, (j - at : U32)))),
      %e1 : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, _) == True{} : Bool}; hbi) :
    {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(Norm.line(P.btext(len, t, at, (j - at : U32)))), 0n, BN.lend(Norm.line(P.btext(len, t, at, (j - at : U32)))))) == True{} : Bool}}
  K.sv(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, MSX.vd_ok(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, hv), BV.vd_bud(fa, wp, back, Norm.line(P.btext(len, t, at, (j - at : U32))), hb, hv, hbl), hnr)

# What -m does with the line: whole, its records, or refused (code c).
def K.pk(+hold: Bool, +pt: B.Parts, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +ept: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == pt : B.Parts},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.parts.k(pt, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), PC.mkWin(fa, wp), fneed)):
  match pt:
    case B.Whole{}:
      K.whole(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hnr)
    case B.Pieces{+ps}:
      K.injr(hold, ps, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, ept, hnr)
    case B.Unsplit{+c}:
      +e1 = K.e1(hold, dfs, fa, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, fneed, cs, hsp, hn, hw, hbi, hnr)
      K.su(hold, c, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, MSX.vd_ok(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, K.hv(hold, dfs, fa, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hw, hnr)),
        BV.vd_bud(fa, wp, back, Norm.line(P.btext(len, t, at, (j - at : U32))), hb, K.hv(hold, dfs, fa, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hw, hnr), e1), hnr)

def K.sp(+hold: Bool, +sp: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +esp: {R.Opts.split(o) == sp : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow.split(sp, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match sp:
    case False{}:
      K.whole(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hnr)
    case True{}:
      K.pk(hold, B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, {==}, hnr)

def K.slow(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) -> 
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.slow(back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  K.sp(hold, R.Opts.split(o), dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, {==}, hnr)


# ---------------------------------------------------------------------------
# Header lines
# ---------------------------------------------------------------------------

def K.hf(+hold: Bool, +dfs: B.Defs, +fits: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.head.fits(fits, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match fits:
    case True{}:
      CW(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, NR.head_line(True{}, NR.tick(P.mkRun(rp)), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), hnr)
    case False{}:
      TMC(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, False{}, hnr)

def K.head(+hold: Bool, +dfs: B.Defs, +isc: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.head(isc, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match isc:
    case False{}:
      CW(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, NR.head_line(False{}, NR.tick(P.mkRun(rp)), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), hnr)
    case True{}:
      %Equal.sym(NR.Run & Bool, Norm.Run.head(P.mkRun(rp)), (P.mkRun(rp), Norm.len_le(P.RunP.h(rp), 268435456)), WR.rhead_eq(rp)) :
        BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.head.len(o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
      K.hf(hold, dfs, Bool.and(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456)), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hnr)

# ---------------------------------------------------------------------------
# The decoded chain (as proof_b_adv_dec.bend's)
# ---------------------------------------------------------------------------

def K.go(+hold: Bool, +dfs: B.Defs, +i: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +ei: {P.RunP.i(rp) == i : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.go(i, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      K.head(hold, dfs, R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hnr)
    case True{}:
      K.slow(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, ei, hnr)

def K.in(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.in(back, o, Norm.Run.inbody(P.mkRun(rp)), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          match q2:
            case (hle, hby):
              +hfit = {%Equal.sym(Nat, n((j - at : U32)), Nat.sub(n(j), n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool};
                %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(j), n(at))), n(j), N.le_sub_add(n(at), n(j), hal)) : {Nat.is_le(_, n(len)) == True{} : Bool};
                N.lt_to_le(n(j), n(len), hlt) : {Nat.is_le(Nat.add(n(at), n((j - at : U32))), n(len)) == True{} : Bool}}
              %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), DE.inb_eq(rp)) :
                BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.decoded.in(back, o, _, at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
              %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), P.btext(len, t, at, (j - at : U32))), DE.text_eq(len, t, d, at, (j - at : U32), hok, hfit)) :
                BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.decoded.k(P.RunP.i(rp), back, o, P.mkRun(rp), at, j, _, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
              K.go(hold, dfs, P.RunP.i(rp), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, LP.inc_len(len, t, d, j, hok, hlt), hsm, {==}, hnr)

def K.big(+hold: Bool, +dfs: B.Defs, +big: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hne: {U32.is_eq(j, len) == False{} : Bool},
  +eb: {U32.is_lt(268435456, (j - at : U32)) == big : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.big(big, back, o, P.mkRun(rp), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match big:
    case True{}:
      TMC(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, fneed, hnr)
    case False{}:
      +hjr = DE.j_range(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr)
      +hlt = DE.j_lt(len, j, W.and_r(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr), hne)
      K.in(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hal, hlt, eb, LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf), hlt), hnr)

def K.if(+hold: Bool, +dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.if(part, back, o, P.mkRun(rp), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match part:
    case True{}:
      CPT(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, %U.is_eq_true(j, len, ep) : {n(_) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat}; hjf,
        LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, n(len), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), %U.is_eq_true(j, len, ep) : {n(_) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat}; hjf)), hnr)
    case False{}:
      K.big(hold, dfs, U32.is_lt(268435456, (j - at : U32)), j, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hjf, ep, {==}, hnr)

def K.j(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: DE.LFW(len, t, at),
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.decoded.lf(back, o, P.mkRun(rp), at, _, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed))
          K.if(hold, dfs, U32.is_eq(j, len), j, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hjf, {==}, hnr)

# c.dec (proof_b_budget_dec.bend).
def top(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N0: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  BD.AdvC(fa, cs, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed)):
  +hi = HX.inv_h(hold, rp, W.c9_0(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W2(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W3(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W4(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W5(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W6(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W7(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W8(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), hw))
  +hso = LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W2(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W3(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W4(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W5(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W6(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W7(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), W.W8(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  K.j(hold, dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, LN.lf_ok(len, t, d, at, hok, hs), hnr)
