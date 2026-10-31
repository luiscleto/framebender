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
import ./proof_b_budget_lem.bend as BL
import ./proof_b_bud_vd.bend as BV
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
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
def lcons(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +cs: List<&2, String>,
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs)) == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)) : List<&2, B.Line>}:
  +pre = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
  +post = BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed)
  Equal.trans(List<&2, B.Line>, B.Text.lines(BM.TP(pre, cs)), B.Text.lines(S.intext(pre, cs)), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), BM.TP(pre, cs), S.intext(pre, cs), BL.text_pic(pre, cs)),
    Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(pre, cs)), B.Text.lines(String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", S.intext(post, cs)))), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)),
      Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(pre, cs), String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", S.intext(post, cs))),
        Equal.sym(String, String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", S.intext(post, cs))), S.intext(pre, cs), LI.itx(dfs, o, S.MBP{rp}, S.MBP{rp}, rest, pd, eof, back, back, wp, None{}, None{}, fneed, fneed, cs, len, t, d, at, j, hsp))),
      Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", S.intext(post, cs)))), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(S.intext(post, cs)), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)),
        LSS.lines_cons(P.btext(len, t, at, (j - at : U32)), S.intext(post, cs), hn),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(z), S.intext(post, cs), BM.TP(post, cs), Equal.sym(String, BM.TP(post, cs), S.intext(post, cs), BL.text_pic(post, cs))))))

# ---------------------------------------------------------------------------
# The leaves
# ---------------------------------------------------------------------------

# A line handled (done.b): whatever the run after it.
def CW(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  x: NR.Run) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MB{x}, Con{Norm.SB{C.BT(len, t), (j + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  (BM.went_done(dfs, fa, cs, o, S.MBP{rp}, S.MBP{rp}, len, t, d, at, j, rest, pd, eof, back, 0n, wp, wp, None{}, None{}, fneed, False{}, hsp, hn),
    bi0(fa, wp, BN.lines(Con{Norm.SB{C.BT(len, t), (j + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, cs)))

# The String mode taken, the text and back kept.
def TMC(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +f2: Bool) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, f2, dfs}}):
  +ls = BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)
  (%Equal.sym(Bool, BN.fast_left(Norm.to_ms(P.mkRun(rp)), f2), False{}, fl_ms(rp, f2)) :
     {Nat.is_le(BN.WA.ls(fa, _, back, PC.mkWin(fa, wp), None{}, ls), BN.WA.ls(fa, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, ls)) == True{} : Bool};
   wa_fl(fa, Bool.not(fneed), back, wp, None{}, ls),
   hbi)

# The source's text moves to the line end.
def Q2(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +rest: List<&2, P.SrcP>, +pd2: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool) -> S.StP:
  BD.StM(dfs, o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed)

def CPT.pa(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  pa: DPT.PAW(pd, len, t, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  match pa:
    case (+pd2, q):
      match q:
        case (eadd, q2):
          match q2:
            case (hpd2, htx):
              +q2p = Q2(dfs, o, rp, rest, pd2, eof, back, wp, fneed)
              +eqT = Equal.trans(String, BM.TP(q2p, cs), S.intext(q2p, cs), BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), BL.text_pic(q2p, cs),
                Equal.trans(String, S.intext(q2p, cs), S.intext(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs),
                  DPT.DP.tq(dfs, rest, fa, cs, o, rp, len, t, d, at, pd, eof, back, wp, None{}, fneed, fneed, hw, hn, hsa, pd2, htx),
                  Equal.sym(String, BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), S.intext(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), BL.text_pic(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs))))
              %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) :
                BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), _, eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}})
              ({%Equal.sym(String, BM.TP(q2p, cs), BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), eqT) :
                  {Nat.is_le(BN.WA.ls(fa, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, B.Text.lines(_)), BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool};
                N.le_refl(BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs)) : {Nat.is_le(BN.WA.ls(fa, Bool.not(fneed), back, PC.mkWin(fa, wp), None{}, B.Text.lines(BM.TP(q2p, cs))), BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool}},
               {%Equal.sym(String, BM.TP(q2p, cs), BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs), eqT) : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, B.Text.lines(_)) == True{} : Bool};
                hbi : {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, B.Text.lines(BM.TP(q2p, cs))) == True{} : Bool}})

def CPT(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjl: {n(len) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  sn: DPT.SNW(len, t, d, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, (C.BT(len, t), len), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match sn:
    case (hn, hsa):
      +hfit = {%Equal.sym(Nat, n((len - at : U32)), Nat.sub(n(len), n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(len), n(at))), n(len), N.le_sub_add(n(at), n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, n(len)) == True{} : Bool};
        N.le_refl(n(len)) : {Nat.is_le(Nat.add(n(at), n((len - at : U32))), n(len)) == True{} : Bool}}
      CPT.pa(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hn, hsa, LN.pend_add(pd, len, t, d, at, (len - at : U32), W.c9_2(S.md_ok(S.MBP{rp}), W.W1(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W2(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W3(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W4(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W5(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W6(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W7(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W8(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), hw), hok, hfit))

# A Want: vd_bud's share, on the line WA counts.
def K.vw(+dfs: B.Defs, +reqs: List<&2, Pr.Req>, +b2: Nat, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), Norm.VWant{PC.mkWin(fa, wp), reqs, b2})) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.want.b(o, P.mkRun(rp), C.BT(len, t), at, b2, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), reqs, fneed)):
  match vb:
    case (vb1, vb2):
      +e1 = lcons(dfs, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, fneed, cs, hsp, hn)
      +FL = Bool.not(fneed)
      +KQ = {1n+List.length(&2, Pr.Req, reqs) : Nat}
      +LR = BN.LAs(fa, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)))
      +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
      +g1 = {%Equal.sym(List<&2, B.Line>, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs)), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)), e1) :
          {Nat.is_le(Nat.add(KQ, BN.WA.ls(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, _)), BN.WA.ls(fa, FL, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool};
        %LN.line_eq(P.btext(len, t, at, (j - at : U32))) :
          {Nat.is_le(Nat.add(KQ, Nat.add(BN.rem(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, _), LR)), Nat.add(BN.rem(fa, FL, back, PC.mkWin(fa, wp), None{}, _), LR)) == True{} : Bool};
        want_le(BN.lgate(l), FL, BN.RW(l),
          BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), Some{reqs}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)), Nat.add(BN.pick(Nat.is_eq(b2, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(b2, BN.lpos(l)), BN.ZW(fa))),
          BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), None{}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), BN.RW(l)), Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa))),
          KQ, LR, vb1) :
          {Nat.is_le(Nat.add(KQ, BN.WA.ls(fa, FL, b2, PC.mkWin(fa, wp), Some{reqs}, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs)))), BN.WA.ls(fa, FL, back, PC.mkWin(fa, wp), None{}, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs)))) == True{} : Bool}}
      +g2 = {%Equal.sym(List<&2, B.Line>, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs)), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, None{}, fneed), cs)), e1) : {BN.bi.ls(b2, PC.mkWin(fa, wp), Some{reqs}, _) == True{} : Bool};
        %LN.line_eq(P.btext(len, t, at, (j - at : U32))) : {Bool.or(Nat.is_eq(b2, 0n), BN.heldZ(PC.mkWin(fa, wp), Some{reqs}, BN.lchrom(_), BN.lend(_))) == True{} : Bool};
        vb2 : {BN.bi.ls(b2, PC.mkWin(fa, wp), Some{reqs}, B.Text.lines(BM.TP(BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), cs))) == True{} : Bool}}
      (g1, g2)

def K.same.d(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  dw: SLW.DW(rp1, o, len, t, at, j, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, (P.mkRun(rp1), P.RunP.n(rp1)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          %Equal.sym(NR.Run & D.Bytes, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
          CW(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, P.mkRun(rp2))

def K.same.t(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, NR.Run.n(NR.tick(P.mkRun(rp))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, SLW.hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = SLW.f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = SLW.f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.same_done(o, NR.Run.n(_), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.same_done(o, _, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
  K.same.d(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, rp1, PR.run_same_done(rp1, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hs, hfl, hal, hlt), hbig1, hk, hcb, hcl))

def K.same(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  tk: WR.TKW(rp)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.same_done(o, Norm.ticked(P.mkRun(rp)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
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
                          K.same.t(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hrj, rp1, et, i1, s1, obl1)

def K.body.d(+dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  dw: SLW.DW(rp1, o, len, t, at, j, r, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, (P.mkRun(rp1), P.RunP.n(rp1)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          %Equal.sym(NR.Run & D.Bytes, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
          CW(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, P.mkRun(rp2))

def K.body.t(+dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hrj: {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, NR.Run.n(NR.tick(P.mkRun(rp))), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, SLW.hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = SLW.f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = SLW.f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  +hfit1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {Norm.res_fits(r, l, (1073741824 - _ : U32)) == True{} : Bool}; hfit : {Norm.res_fits(r, l, (1073741824 - P.RunP.obl(rp1) : U32)) == True{} : Bool}}
  +hres = {%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hrj) : {E.is_bytes(P.res_text(_)) == True{} : Bool}; SLW.judge_bytes(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, SLW.body_bytes(P.btext(len, t, at, (j - at : U32)), hby)) : {E.is_bytes(P.res_text(r)) == True{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.body_done(r, o, NR.Run.n(_), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.body_done(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
  K.body.d(dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, rp1, PR.run_body_line(rp1, r, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hs, hfl, hal, hlt), hbig1, hk, hfit1, hres, hcb, hcl))

def K.body(+dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hrj: {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res},
  tk: WR.TKW(rp)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body_done(r, o, Norm.ticked(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
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
                          K.body.t(dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hfit, hrj, rp1, et, i1, s1, obl1)

# ---------------------------------------------------------------------------
# The slow path's verdict
# ---------------------------------------------------------------------------

def K.fit(+dfs: B.Defs, +fits: Bool, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hrj: {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res},
  +ef: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == fits : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body.fits(fits, r, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  match fits:
    case False{}:
      TMC(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, False{})
    case True{}:
      K.body(dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, ef, hrj, PR.run_tick(rp, hi))

def K.vr(+dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hrj: {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.body.res(r, o, Norm.Run.oblen(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  %Equal.sym(NR.Run & U32, Norm.Run.oblen(P.mkRun(rp)), (P.mkRun(rp), P.RunP.obl(rp)), SLW.oblen_eq(rp)) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.body.res(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
  K.fit(dfs, Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)), r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hrj, {==})

def K.v(+dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, fneed, back, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
      K.vr(dfs, r, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk)
    case MSX.VSP{}:
      K.same(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk, PR.run_tick(rp, hi))
    case MSX.VWP{+reqs, +b2}:
      K.vw(dfs, reqs, b2, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, vb)

def K.sv(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  vb: BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(Norm.line(P.btext(len, t, at, (j - at : U32)))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, fneed, back, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))))):
  match h:
    case (+v, q):
      match q:
        case (ev, hk):
          +evc = Equal.trans(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), MSX.mkVd(fa, wp, v), ev, {==})
          %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), evc) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, fneed, back, _))
          K.v(dfs, v, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, hin, hk, AB.subst(Norm.Vd, z => BD.VB(fa, Norm.line(P.btext(len, t, at, (j - at : U32))), back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), evc, vb))

def K.slow(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hin: {P.RunP.i(rp) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.slow(back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  ?TODO


# ---------------------------------------------------------------------------
# Header lines
# ---------------------------------------------------------------------------

def K.hf(+dfs: B.Defs, +fits: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.head.fits(fits, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  match fits:
    case True{}:
      CW(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, NR.head_line(True{}, NR.tick(P.mkRun(rp)), o, Norm.line(P.btext(len, t, at, (j - at : U32)))))
    case False{}:
      TMC(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, False{})

def K.head(+dfs: B.Defs, +isc: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.head(isc, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  match isc:
    case False{}:
      CW(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hsp, hn, NR.head_line(False{}, NR.tick(P.mkRun(rp)), o, Norm.line(P.btext(len, t, at, (j - at : U32)))))
    case True{}:
      %Equal.sym(NR.Run & Bool, Norm.Run.head(P.mkRun(rp)), (P.mkRun(rp), Norm.len_le(P.RunP.h(rp), 268435456)), WR.rhead_eq(rp)) :
        BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.head.len(o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
      K.hf(dfs, Bool.and(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456)), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm)

# ---------------------------------------------------------------------------
# The decoded chain (as proof_b_adv_dec.bend's)
# ---------------------------------------------------------------------------

def K.go(+dfs: B.Defs, +i: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
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
  +ei: {P.RunP.i(rp) == i : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.go(i, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match i:
    case False{}:
      K.head(dfs, R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm)
    case True{}:
      K.slow(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, hinc, hsm, ei)

def K.in(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +j: U32,
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.in(back, o, Norm.Run.inbody(P.mkRun(rp)), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
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
                BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.decoded.in(back, o, _, at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed))
              %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), P.btext(len, t, at, (j - at : U32))), DE.text_eq(len, t, d, at, (j - at : U32), hok, hfit)) :
                BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.decoded.k(P.RunP.i(rp), back, o, P.mkRun(rp), at, j, _, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed))
              K.go(dfs, P.RunP.i(rp), fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hsp, hn, hle, hby, hal, hlt, LP.inc_len(len, t, d, j, hok, hlt), hsm, {==})

def K.big(+dfs: B.Defs, +big: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hne: {U32.is_eq(j, len) == False{} : Bool},
  +eb: {U32.is_lt(268435456, (j - at : U32)) == big : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.big(big, back, o, P.mkRun(rp), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match big:
    case True{}:
      TMC(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, fneed)
    case False{}:
      +hjr = DE.j_range(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr)
      +hlt = DE.j_lt(len, j, W.and_r(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr), hne)
      K.in(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, j, hjf, hal, hlt, eb, LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf), hlt))

def K.if(+dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded.if(part, back, o, P.mkRun(rp), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match part:
    case True{}:
      CPT(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, %U.is_eq_true(j, len, ep) : {n(_) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat}; hjf,
        LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, n(len), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), %U.is_eq_true(j, len, ep) : {n(_) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat}; hjf)))
    case False{}:
      K.big(dfs, U32.is_lt(268435456, (j - at : U32)), j, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hjf, ep, {==})

def K.j(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: DE.LFW(len, t, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed), Norm.decoded.lf(back, o, P.mkRun(rp), at, _, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed))
          K.if(dfs, U32.is_eq(j, len), j, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, hjf, {==})

# c.dec (proof_b_budget_dec.bend).
def top(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N0: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed)):
  +hi = W.c9_0(S.md_ok(S.MBP{rp}), W.W1(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W2(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W3(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W4(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W5(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W6(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W7(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W8(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), hw)
  +hso = LI.srcs_head(rest, len, t, d, at, W.c9_1(S.md_ok(S.MBP{rp}), W.W1(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W2(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W3(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W4(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W5(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W6(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W7(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), W.W8(fa, BD.StM(dfs, o, S.MBP{rp}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  K.j(dfs, fa, cs, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hx, hbig, hbi, hi, hok, hs, LN.lf_ok(len, t, d, at, hok, hs))
