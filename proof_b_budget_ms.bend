import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_lem.bend as BL
import ./proof_b_budget.bend as BG
import ./proof_b_bud_win.bend as BW
import ./proof_b_bud_fm.bend as FM
import ./proof_b_bud_vd.bend as BV
import ./proof_b_lines.bend as LN
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_part.bend as DPT
import ./proof_b_adv_str.bend as AS
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-words/proof_u32.bend as U
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_adv_wf.bend as W
import ./proof_b_cache_lem.bend as X
import ./proof_b_lines_str.bend as LS
import ./proof_machine_nat.bend as PN
import ./proof_fast.bend as PF
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# pb-cut's budget walk, the String-mode lines (proof_b_budget_adv.bend's
# c.ms.sb and c.ms.sl): what advance does to WA and bi on a text line.
#   - a line consumed (ms.done): the text loses its first line, back is 0;
#   - the partial line moved to pend (ms.part.len): text and fields kept;
#   - a Want (ms.want): the verdict's reads are paid by the flag they flip
#     (vd_pay below; it is about the body line only, so the byte mode's slow
#     path can use it too).

# ---------------------------------------------------------------------------
# The text: its first line, then the rest
# ---------------------------------------------------------------------------

def lines_split(+src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  {BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{B.Text.line(q), BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}:
  +R0 = String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))
  +S2 = P.srcstext(src2)
  %Equal.sym(String, BN.srcT(P.mkSrcs(src)), P.srcstext(src), BL.srcT_pic(src)) :
    {B.Text.lines(String.append(_, R0)) == Con{B.Text.line(q), B.Text.lines(String.append(BN.srcT(P.mkSrcs(src2)), R0))} : List<&2, B.Line>}
  %Equal.sym(String, BN.srcT(P.mkSrcs(src2)), S2, BL.srcT_pic(src2)) :
    {B.Text.lines(String.append(P.srcstext(src), R0)) == Con{B.Text.line(q), B.Text.lines(String.append(_, R0))} : List<&2, B.Line>}
  %Equal.sym(String, P.srcstext(src), String.append(q, String.append("\n", S2)), hst) :
    {B.Text.lines(String.append(_, R0)) == Con{B.Text.line(q), B.Text.lines(String.append(S2, R0))} : List<&2, B.Line>}
  %Equal.sym(String, String.append(String.append(q, String.append("\n", S2)), R0), String.append(q, String.append(String.append("\n", S2), R0)), PN.str_assoc(q, String.append("\n", S2), R0)) :
    {B.Text.lines(_) == Con{B.Text.line(q), B.Text.lines(String.append(S2, R0))} : List<&2, B.Line>}
  %Equal.sym(String, String.append(String.append("\n", S2), R0), String.append("\n", String.append(S2, R0)), PN.str_assoc("\n", S2, R0)) :
    {B.Text.lines(String.append(q, _)) == Con{B.Text.line(q), B.Text.lines(String.append(S2, R0))} : List<&2, B.Line>}
  LS.lines_cons(q, String.append(S2, R0), hq)

# ---------------------------------------------------------------------------
# A line consumed: WA drops, bi holds (back is 0)
# ---------------------------------------------------------------------------

def pk(+b: Bool, +n: Nat) -> {Nat.is_le(BN.pick(b, n), n) == True{} : Bool}:
  match b:
    case True{}:
      N.le_refl(n)
    case False{}:
      N.le_zero_l(n)

def am(+a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +h1: {Nat.is_le(a1, b1) == True{} : Bool}, +h2: {Nat.is_le(a2, b2) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a1, a2), Nat.add(b1, b2)) == True{} : Bool}:
  N.le_trans(Nat.add(a1, a2), Nat.add(b1, a2), Nat.add(b1, b2), N.le_add_mono_r(a2, a1, b1, h1), N.le_add_mono_l(b1, a2, b2, h2))

def rl(+g: Bool, +f: Bool, +h: Bool, +z: Bool, +z2: Bool, +rw: Nat, +zw: Nat) ->
  {Nat.is_le(BN.pick(g, Nat.add(Nat.add(BN.pick(f, rw), BN.pick(h, rw)), Nat.add(BN.pick(z, zw), BN.pick(z2, zw)))), BN.pick(g, Nat.add(Nat.add(rw, rw), Nat.add(zw, zw)))) == True{} : Bool}:
  match g:
    case True{}:
      am(Nat.add(BN.pick(f, rw), BN.pick(h, rw)), Nat.add(rw, rw), Nat.add(BN.pick(z, zw), BN.pick(z2, zw)), Nat.add(zw, zw),
        am(BN.pick(f, rw), rw, BN.pick(h, rw), rw, pk(f, rw), pk(h, rw)),
        am(BN.pick(z, zw), zw, BN.pick(z2, zw), zw, pk(z, zw), pk(z2, zw)))
    case False{}:
      {==}

def rem_le_la(+fa: List<&2, B.Contig>, +fl: Bool, +b: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line) ->
  {Nat.is_le(BN.rem(fa, fl, b, PC.mkWin(fa, wp), m, l), BN.LA(fa, l)) == True{} : Bool}:
  rl(BN.lgate(l), fl, Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))), Nat.is_eq(b, 0n), Nat.is_lt(b, BN.lpos(l)), BN.RW(l), BN.ZW(fa))

def wa_le(+fa: List<&2, B.Contig>, +fl: Bool, +b: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) ->
  {Nat.is_le(BN.WA.ls(fa, fl, b, PC.mkWin(fa, wp), m, ls), BN.LAs(fa, ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      N.le_add_mono_r(BN.LAs(fa, t), BN.rem(fa, fl, b, PC.mkWin(fa, wp), m, l), BN.LA(fa, l), rem_le_la(fa, fl, b, wp, m, l))

def bi0(+fa: List<&2, B.Contig>, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) -> {BN.bi.ls(0n, PC.mkWin(fa, wp), m, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      {==}

def went_wa(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +fl: Bool, +wp: PC.WP, +back: Nat,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  {Nat.is_le(BN.WA.ls(fa, fl, 0n, PC.mkWin(fa, wp), None{}, BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs))) == True{} : Bool}:
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  %Equal.sym(List<&2, B.Line>, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs), Con{B.Text.line(q), L2}, lines_split(src, src2, pd, eof, cs, q, hst, hq)) :
    {Nat.is_le(BN.WA.ls(fa, fl, 0n, PC.mkWin(fa, wp), None{}, L2), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool}
  N.le_trans(BN.WA.ls(fa, fl, 0n, PC.mkWin(fa, wp), None{}, L2), BN.LAs(fa, L2), Nat.add(BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, B.Text.line(q)), BN.LAs(fa, L2)),
    wa_le(fa, fl, 0n, wp, None{}, L2), N.le_add_l(BN.LAs(fa, L2), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, B.Text.line(q))))

# A consumed line (ms.done) keeps the budget.
def done_c(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +s2: R.RunSt,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.done(o, s2, qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  (went_wa(fa, cs, BN.fast_left(Norm.ms.out(s2, qs, ql), False{}), wp, back, src, src2, pd, eof, q, hst, hq),
   bi0(fa, wp, None{}, BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)))

# ---------------------------------------------------------------------------
# A Want (ms.want): the line goes back in front; vd_bud pays
# ---------------------------------------------------------------------------

def want_c(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +reqs: List<&2, Pr.Req>, +bk: Nat,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  hvb: BD.VB(fa, B.Text.line(q), back, PC.mkWin(fa, wp), Norm.VWant{PC.mkWin(fa, wp), reqs, bk})) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.want(o, s, qs, ql, q, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp), reqs, bk)):
  (h1, h2) = hvb
  +L0 = B.Text.line(q)
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +LS3 = {Con{L0, L2} : List<&2, B.Line>}
  +LN1 = BN.lines(P.mkSrcs(Con{P.SLP{q}, src2}), P.mkPd(pd), eof, cs)
  +LN0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +K1 = {1n+List.length(&2, Pr.Req, reqs) : Nat}
  +RN = BN.rem(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, L0)
  +RO = BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, L0)
  +A = BN.LAs(fa, L2)
  +e1 = lines_split(Con{P.SLP{q}, src2}, src2, pd, eof, cs, q, PN.str_assoc(q, "\n", P.srcstext(src2)), hq)
  +e0 = lines_split(src, src2, pd, eof, cs, q, hst, hq)
  +hA = {%N.add_assoc(K1, RN, A) : {Nat.is_le(_, Nat.add(RO, A)) == True{} : Bool};
    N.le_add_mono_r(A, Nat.add(K1, RN), RO, h1) :
    {Nat.is_le(Nat.add(K1, BN.WA.ls(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, LS3)), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, LS3)) == True{} : Bool}}
  +hB = AB.subst(List<&2, B.Line>, z => {Nat.is_le(Nat.add(K1, BN.WA.ls(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, z)), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, LS3)) == True{} : Bool},
    LS3, LN1, Equal.sym(List<&2, B.Line>, LN1, LS3, e1), hA)
  +hC = AB.subst(List<&2, B.Line>, z => {Nat.is_le(Nat.add(K1, BN.WA.ls(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, LN1)), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, z)) == True{} : Bool},
    LS3, LN0, Equal.sym(List<&2, B.Line>, LN0, LS3, e0), hB)
  +hD = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(bk, PC.mkWin(fa, wp), Some{reqs}, z) == True{} : Bool}, LS3, LN1, Equal.sym(List<&2, B.Line>, LN1, LS3, e1), h2)
  (hC, hD)

# ---------------------------------------------------------------------------
# A text line q in front of the sources (head line, decided body line, Want)
# ---------------------------------------------------------------------------

def cbody.v(+v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  hvb: BD.VB(fa, B.Text.line(q), back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v))) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, q, B.Text.line(q), BN.lfs(B.Text.line(q)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
      +L0 = B.Text.line(q)
      +FS = BN.lfs(L0)
      done_c(fa, cs, o, s, qs, ql, R.body_line(r, R.tick(s), o, L0, Norm.at_of(R.RunSt.n(R.tick(s)), FS), B.Rec.pos(FS)), src, src2, pd, eof, back, wp, fneed, q, hst, hq)
    case MSX.VSP{}:
      +L0 = B.Text.line(q)
      +FS = BN.lfs(L0)
      done_c(fa, cs, o, s, qs, ql, R.body_line(B.Res{B.Normalized{}, B.Rec.pos(FS), B.Line.body(L0), False{}}, R.tick(s), o, L0, Norm.at_of(R.RunSt.n(R.tick(s)), FS), B.Rec.pos(FS)),
        src, src2, pd, eof, back, wp, fneed, q, hst, hq)
    case MSX.VWP{+reqs, +bk}:
      want_c(fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, reqs, bk, hst, hq, hvb)

def cbody.h(+v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +heq: {Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(B.Text.line(q)), B.Line.body(B.Text.line(q))) == MSX.mkVd(fa, wp, v) : Norm.Vd},
  hvb: BD.VB(fa, B.Text.line(q), back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(B.Text.line(q)), B.Line.body(B.Text.line(q))))) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, q, B.Text.line(q), BN.lfs(B.Text.line(q)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof},
      Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(B.Text.line(q)), B.Line.body(B.Text.line(q))))):
  +L0 = B.Text.line(q)
  AB.subst(Norm.Vd, z => BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
      Norm.ms.body(o, s, qs, ql, q, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, z)),
    MSX.mkVd(fa, wp, v), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), MSX.mkVd(fa, wp, v), heq),
    cbody.v(v, fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, hst, hq,
      AB.subst(Norm.Vd, z => BD.VB(fa, L0, back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), MSX.mkVd(fa, wp, v), heq, hvb)))

def cbody.g(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  g: MSX.VdG(fa, wp, back, B.Line.body(B.Text.line(q))),
  hvb: BD.VB(fa, B.Text.line(q), back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(B.Text.line(q)), B.Line.body(B.Text.line(q))))) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, q, B.Text.line(q), BN.lfs(B.Text.line(q)), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof},
      Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(B.Text.line(q)), B.Line.body(B.Text.line(q))))):
  (v, pr) = g
  (heq, hok) = pr
  cbody.h(v, fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, hst, hq, heq, hvb)

def clk(+ib: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hbi1: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(B.Text.line(q)), 0n, BN.lend(B.Text.line(q)))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line.k(ib, o, s, qs, ql, q, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  match ib:
    case False{}:
      +L0 = B.Text.line(q)
      done_c(fa, cs, o, s, qs, ql, R.head_line(R.is_chrom_line(B.Line.body(L0)), R.tick(s), o, L0), src, src2, pd, eof, back, wp, fneed, q, hst, hq)
    case True{}:
      +L0 = B.Text.line(q)
      cbody.g(fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, hst, hq,
        MSX.vd_ok(fa, wp, back, B.Line.body(L0), hb, hwp), BV.vd_bud(fa, wp, back, L0, hb, hwp, hbi1))

# bi's zero window (held and fitting) holds the read from 0.
def zh_hw(w: Norm.Win, +c: String, +e: Nat, +h: {BN.zheld(w, c, e) == True{} : Bool}) -> {BN.holdsW(w, c, 0n, e) == True{} : Bool}:
  match w:
    case Norm.WNone{}:
      Empty.absurd({BN.holdsW(Norm.WNone{}, c, 0n, e) == True{} : Bool}, N.false_ne_true(h))
    case Norm.WUnk{+c0}:
      Empty.absurd({BN.holdsW(Norm.WUnk{c0}, c, 0n, e) == True{} : Bool}, N.false_ne_true(h))
    case Norm.WKnown{+c0, cb, +a0, +b0, +clen, off, raw, offu, rlen, clenu}:
      +H = Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen)))
      W.and_l(H, Nat.is_le(e, clen), h)
    case Norm.WStr{+c0, +a0, +b0, +clen, off, raw}:
      +H = Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen)))
      W.and_l(H, Nat.is_le(e, clen), h)

def or_z(+a: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +e: Nat,
  +h: {Bool.or(a, BN.zheld(PC.mkWin(fa, wp), c, e)) == True{} : Bool}) ->
  {Bool.or(a, BN.holdsW(PC.mkWin(fa, wp), c, 0n, e)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      zh_hw(PC.mkWin(fa, wp), c, e, h)

def cline(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  +L0 = B.Text.line(q)
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +LN0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +hbi1 = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, LN0, Con{L0, L2}, lines_split(src, src2, pd, eof, cs, q, hst, hq), hbi)
  AB.subst(Norm.Adv, z => BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed), z),
    Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, q, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp)), Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp)),
    Equal.sym(Norm.Adv, Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp)), Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, q, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp)),
      MSX.mline_eq(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, PC.mkWin(fa, wp))),
    clk(R.RunSt.inbody(s), fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, hb, hwp, hst, hq,
      or_z(Nat.is_eq(back, 0n), fa, wp, BN.lchrom(L0), BN.lend(L0), hbi1)))

# ---------------------------------------------------------------------------
# c.ms.sl: a text line source
# ---------------------------------------------------------------------------

def c_ms_sl(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  +pp = BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)
  +hc = MSX.wfC(fa, pp, hw)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +hsl = MSX.src_hd(P.SLP{q}, rest, W.c9_1(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc))
  cline(fa, cs, o, s, qs, ql, q, Con{P.SLP{q}, rest}, rest, pd, eof, back, wp, fneed, hb, W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
    PN.str_assoc(q, "\n", P.srcstext(rest)), W.and_r(E.is_bytes(q), P.nolf(q), hsl), hbi)

# ---------------------------------------------------------------------------
# c.ms.sb: a byte source
# ---------------------------------------------------------------------------

# No LF left: the source's text moves to the line end; the text is the same.
def ptxt.k(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +Y: String,
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String}) ->
  {String.append(BN.srcT(P.mkSrcs(rest)), String.append(P.btext(len, t, at, (len - at : U32)), Y))
    == String.append(String.append(P.srctext(P.SBP{len, t, d, at}), BN.srcT(P.mkSrcs(rest))), Y) : String}:
  match rest:
    case Nil{}:
      +A = P.btext(len, t, at, (len - at : U32))
      %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), A, hsa) : {String.append("", String.append(A, Y)) == String.append(String.append(_, ""), Y) : String}
      %Equal.sym(String, String.append(A, ""), A, DPT.s_app_nil(A)) : {String.append("", String.append(A, Y)) == String.append(_, Y) : String}
      {==}
    case Con{+sp2, +r2}:
      +S0 = P.srctext(P.SBP{len, t, d, at})
      +A = P.btext(len, t, at, (len - at : U32))
      +R0 = BN.srcT(P.mkSrcs(Con{sp2, r2}))
      +hlS = W.and_r(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(S0), W.and_l(Bool.and(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(S0)), S.srcs_ok(Con{sp2, r2}), h1))
      +eS = DPT.empty_eq(S0, AS.nolf_lf(S0, hn, hlS))
      +eA = Equal.trans(String, A, S0, "", Equal.sym(String, S0, A, hsa), eS)
      %Equal.sym(String, A, "", eA) : {String.append(R0, String.append(_, Y)) == String.append(String.append(S0, R0), Y) : String}
      %Equal.sym(String, S0, "", eS) : {String.append(R0, Y) == String.append(String.append(_, R0), Y) : String}
      {==}

def ptxt(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +pd2: P.PdP, +Y: String,
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hp2: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  {String.append(BN.srcT(P.mkSrcs(rest)), String.append(BN.pdT(P.mkPd(pd2)), Y))
    == String.append(BN.srcT(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest})), String.append(BN.pdT(P.mkPd(pd)), Y)) : String}:
  +A = P.btext(len, t, at, (len - at : U32))
  +R0 = BN.srcT(P.mkSrcs(rest))
  +S0 = P.srctext(P.SBP{len, t, d, at})
  %Equal.sym(String, BN.pdT(P.mkPd(pd2)), P.pdtext(pd2), BL.pdT_pic(pd2)) :
    {String.append(R0, String.append(_, Y)) == String.append(String.append(S0, R0), String.append(BN.pdT(P.mkPd(pd)), Y)) : String}
  %Equal.sym(String, BN.pdT(P.mkPd(pd)), P.pdtext(pd), BL.pdT_pic(pd)) :
    {String.append(R0, String.append(P.pdtext(pd2), Y)) == String.append(String.append(S0, R0), String.append(_, Y)) : String}
  %Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), A), hp2) :
    {String.append(R0, String.append(_, Y)) == String.append(String.append(S0, R0), String.append(P.pdtext(pd), Y)) : String}
  %Equal.sym(String, P.pdtext(pd), "", DPT.empty_eq(P.pdtext(pd), hp0)) :
    {String.append(R0, String.append(String.append(_, A), Y)) == String.append(String.append(S0, R0), String.append(_, Y)) : String}
  ptxt.k(rest, len, t, d, at, Y, h1, hn, hsa)

def cpart.k(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +pd2: P.PdP,
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +eadd: {Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)) == P.mkPd(pd2) : Norm.Pd},
  +hp2: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed}}):
  +Y = S.concat_if(eof, cs)
  +L = BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)
  +L1 = BN.lines(P.mkSrcs(rest), P.mkPd(pd2), eof, cs)
  +e1 = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), String.append(BN.srcT(P.mkSrcs(rest)), String.append(BN.pdT(P.mkPd(pd2)), Y)),
    String.append(BN.srcT(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest})), String.append(BN.pdT(P.mkPd(pd)), Y)), ptxt(rest, len, t, d, at, pd, pd2, Y, h1, hn, hsa, hp0, hp2))
  +hle = AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, z), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, L)) == True{} : Bool},
    L, L1, Equal.sym(List<&2, B.Line>, L1, L, e1), N.le_refl(BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, L)))
  +hbi2 = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, L, L1, Equal.sym(List<&2, B.Line>, L1, L, e1), hbi)
  %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) : BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), _, eof, back, PC.mkWin(fa, wp), None{}, fneed}})
  (hle, hbi2)

def cpart.g(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  pa: DPT.PAW(pd, len, t, at), sn: DPT.SNW(len, t, d, at)) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed}}):
  (pd2, q1) = pa
  (eadd, q2) = q1
  (hpd2, hp2) = q2
  (hn, hsa) = sn
  cpart.k(fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, pd2, h1, hn, hsa, hp0, eadd, hp2, hbi)

def csb_line(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp))):
  +A = P.btext(len, t, at, (j - at : U32))
  +hfit = {%Equal.sym(Nat, LI.n((j - at : U32)), Nat.sub(LI.n(j), LI.n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(j), LI.n(at))), LI.n(j), N.le_sub_add(LI.n(at), LI.n(j), hal)) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
    N.lt_to_le(LI.n(j), LI.n(len), hlt) : {Nat.is_le(Nat.add(LI.n(at), LI.n((j - at : U32))), LI.n(len)) == True{} : Bool}}
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), A), MSX.sb_text(len, t, d, at, (j - at : U32), hok, hfit)) :
    BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
      Norm.ms.sb.k(o, s, qs, ql, at, j, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp)))
  cline(fa, cs, o, s, qs, ql, A, Con{P.SBP{len, t, d, at}, rest}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, fneed,
    hb, hwp, MSX.hst_sb(len, t, d, at, j, rest, hsp), hn, hbi)

def csb_split(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp))):
  (hsp, q1) = sl
  (hn, q2) = q1
  (hle, hby) = q2
  csb_line(fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hal, hlt, hsp, hn)

def csb_if(+part: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +h2: {P.pd_ok(pd) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.if(part, o, s, qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed)):
  match part:
    case True{}:
      +hjl = {%U.is_eq_true(j, len, ep) : {LI.n(_) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}; hjf : {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}}
      +hfit = {%Equal.sym(Nat, LI.n((len - at : U32)), Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(len), LI.n(at))), LI.n(len), N.le_sub_add(LI.n(at), LI.n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
        N.le_refl(LI.n(len)) : {Nat.is_le(Nat.add(LI.n(at), LI.n((len - at : U32))), LI.n(len)) == True{} : Bool}}
      cpart.g(fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, h1, hp0, hbi,
        LN.pend_add(pd, len, t, d, at, (len - at : U32), h2, hok, hfit),
        LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjl)))
    case False{}:
      +hjr = MSX.sb_jr(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr)
      +hlt = MSX.sb_jlt(len, j, W.and_r(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr), ep)
      csb_split(fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hal, hlt,
        LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf), hlt))

def csb_j(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +h2: {P.pd_ok(pd) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: MSX.SBW(len, t, at)) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed)):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
              Norm.ms.sb(o, s, qs, ql, at, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed))
          csb_if(U32.is_eq(j, len), j, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, h1, h2, hp0, hok, hs, hjf, {==})

def c_ms_sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed)):
  +pp = BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
  +hc = MSX.wfC(fa, pp, hw)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +h1 = W.c9_1(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hso = LI.srcs_head(rest, len, t, d, at, h1)
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  csb_j(fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hbi, h1,
    W.c9_2(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_4(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hok, hs, LN.lf_ok(len, t, d, at, hok, hs))
