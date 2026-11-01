import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_lem.bend as BL
import ./proof_b_budget_mb.bend as MB
import ./proof_b_budget.bend as BG
import ./proof_b_bud_win.bend as BW
import ./proof_b_bud_fm.bend as FM
import ./proof_b_bud_vd.bend as BV
import ./proof_b_lines.bend as LN
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_part.bend as DPT
import ./proof_b_adv_str.bend as AS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_adv_sp.bend as HX
import ./proof_b_bud_split.bend as BS
import ./proof_s_recs.bend as SRC
import ./proof_b_adv_wf.bend as W
import ./proof_b_cache_lem.bend as X
import ./proof_b_lines_str.bend as LS
import ./proof_machine_nat.bend as PN
import ./proof_fast.bend as PF
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

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
  +hq: {P.nolf(q) == True{} : Bool},
  +hn0: {S.no_recs(src) == True{} : Bool}, +hn2: {S.no_recs(src2) == True{} : Bool}) ->
  {BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{B.Text.line(q), BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}:
  +R0 = String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))
  +S2 = P.srcstext(src2)
  %Equal.sym(String, BN.srcT(P.mkSrcs(src)), P.srcstext(src), BL.srcT_pic(src, hn0)) :
    {B.Text.lines(String.append(_, R0)) == Con{B.Text.line(q), B.Text.lines(String.append(BN.srcT(P.mkSrcs(src2)), R0))} : List<&2, B.Line>}
  %Equal.sym(String, BN.srcT(P.mkSrcs(src2)), S2, BL.srcT_pic(src2, hn2)) :
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

def went_wa(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +fl: Bool, +wp: PC.WP, +back: Nat,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hn0: {S.no_recs(src) == True{} : Bool}, +hn2: {S.no_recs(src2) == True{} : Bool}) ->
  {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs))) == True{} : Bool}:
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  %Equal.sym(List<&2, B.Line>, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs), L2, BL.all_nr(src2, pd, eof, cs, hn2)) :
    {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, _), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs))) == True{} : Bool}
  %Equal.sym(List<&2, B.Line>, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs), BL.all_nr(src, pd, eof, cs, hn0)) :
    {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, L2), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool}
  %Equal.sym(List<&2, B.Line>, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs), Con{B.Text.line(q), L2}, lines_split(src, src2, pd, eof, cs, q, hst, hq, hn0, hn2)) :
    {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, L2), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, _)) == True{} : Bool}
  MB.wax_tail(fa, o, False{}, back, wp, None{}, fl, 0n, wp, None{}, B.Text.line(q), L2)

# ---------------------------------------------------------------------------
# A line in front of the sources: its text (LsT) or a record of a split line
# (LsR), with the lines still to come being the line, then those of src2
# (hA). The budget does not read the run, so the picture's run (s0) and the
# machine's (s, unticked for a record) may differ.
# ---------------------------------------------------------------------------

# Where a Want puts the line back (ms.want.k): a text as SL, a record as SR.
def WS(+ls: Norm.Ls, +src2: List<&2, P.SrcP>) -> List<&2, P.SrcP>:
  match ls:
    case Norm.LsT{+p}:
      Con{P.SLP{p}, src2}
    case Norm.LsR{+l}:
      Con{P.SRP{l}, src2}

# A consumed line (ms.done) keeps the budget.
def done_g(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +qs: List<&2, String>, +ql: Nat, +s2: R.RunSt,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool, +L0: B.Line,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.done(o, s2, qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  +A0 = BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +A2 = BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +fl = BN.fast_left(Norm.ms.out(s2, qs, ql), False{})
  (AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, A2), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, z)) == True{} : Bool},
     Con{L0, A2}, A0, Equal.sym(List<&2, B.Line>, A0, Con{L0, A2}, hA), MB.wax_tail(fa, o, False{}, back, wp, None{}, fl, 0n, wp, None{}, L0, A2)),
   bi0(fa, wp, None{}, A2))

# A Want: the line goes back in front (srcw); vd_bud pays.
def want_k(+fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +srcw: List<&2, P.SrcP>,
  +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +reqs: List<&2, Pr.Req>, +bk: Nat, +L0: B.Line,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(srcw), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.VWant{PC.mkWin(fa, wp), reqs, bk})) ->
  {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, reqs), BN.WAX(fa, o, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, BN.ALL(P.mkSrcs(srcw), P.mkPd(pd), eof, cs))),
    BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs))) == True{} : Bool}
  & {BN.bi.ls(bk, PC.mkWin(fa, wp), Some{reqs}, BN.ALL(P.mkSrcs(srcw), P.mkPd(pd), eof, cs)) == True{} : Bool}:
  (h1, h2) = hvb
  +A2 = BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +AW = BN.ALL(P.mkSrcs(srcw), P.mkPd(pd), eof, cs)
  +A0 = BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +LS3 = {Con{L0, A2} : List<&2, B.Line>}
  +K1 = {1n+List.length(&2, Pr.Req, reqs) : Nat}
  +RN = BN.rem(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, L0)
  +RO = BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, L0)
  +A = BN.LAs(fa, A2)
  +hA1 = {%N.add_assoc(K1, RN, A) : {Nat.is_le(_, Nat.add(RO, A)) == True{} : Bool};
    N.le_add_mono_r(A, Nat.add(K1, RN), RO, h1) :
    {Nat.is_le(Nat.add(K1, BN.WA.ls(fa, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, LS3)), BN.WA.ls(fa, False{}, back, PC.mkWin(fa, wp), None{}, LS3)) == True{} : Bool}}
  +hAx = MB.wax_want(fa, o, K1, False{}, bk, wp, Some{reqs}, False{}, back, wp, None{}, LS3, hA1)
  +hB = AB.subst(List<&2, B.Line>, z => {Nat.is_le(Nat.add(K1, BN.WAX(fa, o, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, z)), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, LS3)) == True{} : Bool},
    LS3, AW, Equal.sym(List<&2, B.Line>, AW, LS3, hAw), hAx)
  +hC = AB.subst(List<&2, B.Line>, z => {Nat.is_le(Nat.add(K1, BN.WAX(fa, o, False{}, bk, PC.mkWin(fa, wp), Some{reqs}, AW)), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, z)) == True{} : Bool},
    LS3, A0, Equal.sym(List<&2, B.Line>, A0, LS3, hA), hB)
  +hD = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(bk, PC.mkWin(fa, wp), Some{reqs}, z) == True{} : Bool}, LS3, AW, Equal.sym(List<&2, B.Line>, AW, LS3, hAw), h2)
  (hC, hD)

def want_g(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool, +reqs: List<&2, Pr.Req>, +bk: Nat, +L0: B.Line,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.VWant{PC.mkWin(fa, wp), reqs, bk})) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.want(o, s, qs, ql, ls, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), reqs, bk)):
  match ls:
    case Norm.LsT{+p}:
      want_k(fa, o, cs, src, src2, Con{P.SLP{p}, src2}, pd, eof, back, wp, reqs, bk, L0, hA, hAw, hvb)
    case Norm.LsR{+l}:
      want_k(fa, o, cs, src, src2, Con{P.SRP{l}, src2}, pd, eof, back, wp, reqs, bk, L0, hA, hAw, hvb)

# A body line with the verdict v.
def body_v(+dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
      +FS = BN.lfs(L0)
      done_g(dfs, fa, cs, o, s0, qs, ql, R.body_line(r, R.tick(s), o, L0, Norm.at_of(R.RunSt.n(R.tick(s)), FS), B.Rec.pos(FS)), src, src2, pd, eof, back, wp, fneed, hold, L0, hA)
    case MSX.VSP{}:
      +FS = BN.lfs(L0)
      done_g(dfs, fa, cs, o, s0, qs, ql, R.body_line(B.Res{B.Normalized{}, B.Rec.pos(FS), B.Line.body(L0), False{}}, R.tick(s), o, L0, Norm.at_of(R.RunSt.n(R.tick(s)), FS), B.Rec.pos(FS)),
        src, src2, pd, eof, back, wp, fneed, hold, L0, hA)
    case MSX.VWP{+reqs, +bk}:
      want_g(dfs, fa, cs, o, s0, s, qs, ql, ls, src, src2, pd, eof, back, wp, fneed, hold, reqs, bk, L0, hA, hAw, hvb)

# The line's verdict, as verdict gives it (MSX.vd_ok's VdG).
def body_g.h(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +v: MSX.VdP, +heq: {Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)) == MSX.mkVd(fa, wp, v) : Norm.Vd},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))):
  AB.subst(Norm.Vd, z => BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
      Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, z)),
    MSX.mkVd(fa, wp, v), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), MSX.mkVd(fa, wp, v), heq),
    body_v(dfs, v, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw,
      AB.subst(Norm.Vd, z => BD.VB(fa, L0, back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)), MSX.mkVd(fa, wp, v), heq, hvb)))

# A line -m refuses (code c): its verdict, as vd.unsplit gives it.
def body_g(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  g: MSX.VdG(fa, wp, back, B.Line.body(L0)),
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))):
  (v, pr) = g
  (heq, hok) = pr
  body_g.h(dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw, v, heq, hvb)

def uns_v(+c: B.Code, +strict: Bool, +dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, MSX.mkVd(fa, wp, MSX.vdU(c, strict, B.Line.body(L0), v)))):
  match v:
    case MSX.VRP{+r}:
      body_v(dfs, MSX.VRP{Norm.unsplit.res(c, strict, J.pfs(B.Line.body(L0)), B.Line.body(L0), r)}, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw, Unit{})
    case MSX.VSP{}:
      body_v(dfs, MSX.VRP{B.Res{B.Problem{c}, B.Rec.pos(J.pfs(B.Line.body(L0))), B.Line.body(L0), False{}}}, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw, Unit{})
    case MSX.VWP{+reqs, +bk}:
      body_v(dfs, MSX.VWP{reqs, bk}, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw, hvb)

def uns_g.h(+c: B.Code, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +v: MSX.VdP, +heq: {Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)) == MSX.mkVd(fa, wp, v) : Norm.Vd},
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold},
      Norm.vd.unsplit(c, R.Opts.strict(o), BN.lfs(L0), B.Line.body(L0), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0))))):
  +bd = B.Line.body(L0)
  +st = R.Opts.strict(o)
  AB.subst(Norm.Vd, z => BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
      Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, Norm.vd.unsplit(c, st, BN.lfs(L0), bd, z))),
    MSX.mkVd(fa, wp, v), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), bd), Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), bd), MSX.mkVd(fa, wp, v), heq),
    AB.subst(Norm.Vd, z => BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
        Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, z)),
      MSX.mkVd(fa, wp, MSX.vdU(c, st, bd, v)), Norm.vd.unsplit(c, st, BN.lfs(L0), bd, MSX.mkVd(fa, wp, v)),
      Equal.sym(Norm.Vd, Norm.vd.unsplit(c, st, BN.lfs(L0), bd, MSX.mkVd(fa, wp, v)), MSX.mkVd(fa, wp, MSX.vdU(c, st, bd, v)), MSX.vdu_eq(fa, wp, c, st, bd, v)),
      uns_v(c, st, dfs, v, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw,
        AB.subst(Norm.Vd, z => BD.VB(fa, L0, back, PC.mkWin(fa, wp), z), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), bd), MSX.mkVd(fa, wp, v), heq, hvb))))

# A split line (-m, Pieces): its records go in front (SR), back is 0; its rem
# and extra allowance pay for their allowances.
def uns_g(+c: B.Code, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  g: MSX.VdG(fa, wp, back, B.Line.body(L0)),
  hvb: BD.VB(fa, L0, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0)))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.body(o, s, qs, ql, ls, L0, BN.lfs(L0), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold},
      Norm.vd.unsplit(c, R.Opts.strict(o), BN.lfs(L0), B.Line.body(L0), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(L0), B.Line.body(L0))))):
  (v, pr) = g
  (heq, hok) = pr
  uns_g.h(c, dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw, v, heq, hvb)

def pcs_g(+ps: List<&2, String>, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hpt: {B.Rec.parts(dfs, o, B.Line.body(L0)) == B.Pieces{ps} : B.Parts}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.done(o, R.tick(s), qs, ql, Norm.Cx.push(Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, ps, B.Line.term(L0)), PC.mkWin(fa, wp))):
  +tm = B.Line.term(L0)
  +A0 = BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +A2 = BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +AN = BN.ALL(Norm.recs_src(ps, tm, P.mkSrcs(src2)), P.mkPd(pd), eof, cs)
  +LR = List.append(&2, B.Line, SRC.LS(ps, tm), A2)
  +fl = BN.fast_left(Norm.ms.out(R.tick(s), qs, ql), False{})
  +h1 = BS.split_le(fa, o, L0, ps, tm, A2, False{}, back, wp, None{}, fl, 0n, wp, None{}, BS.parts_spf(dfs, o, L0, ps, hpt))
  +h2 = AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, LR), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, z)) == True{} : Bool},
    Con{L0, A2}, A0, Equal.sym(List<&2, B.Line>, A0, Con{L0, A2}, hA), h1)
  (AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, fl, 0n, PC.mkWin(fa, wp), None{}, z), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, A0)) == True{} : Bool},
     LR, AN, Equal.sym(List<&2, B.Line>, AN, LR, BS.all_rs(ps, tm, src2, pd, eof, cs)), h2),
   bi0(fa, wp, None{}, AN))

# What -m does with a body line (B.Rec.parts): whole, its records, refused.
def parts_g(+pt: B.Parts, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hbi1: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(L0), 0n, BN.lend(L0))) == True{} : Bool},
  +ept: {B.Rec.parts(dfs, o, B.Line.body(L0)) == pt : B.Parts}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.parts.k(pt, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, o, s, qs, ql, ls, L0, back, PC.mkWin(fa, wp))):
  match pt:
    case B.Whole{}:
      body_g(dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw,
        MSX.vd_ok(fa, wp, back, B.Line.body(L0), hb, hwp), BV.vd_bud(fa, wp, back, L0, hb, hwp, hbi1))
    case B.Pieces{+ps}:
      pcs_g(ps, dfs, fa, cs, o, s0, s, qs, ql, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, ept)
    case B.Unsplit{+c}:
      uns_g(c, dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw,
        MSX.vd_ok(fa, wp, back, B.Line.body(L0), hb, hwp), BV.vd_bud(fa, wp, back, L0, hb, hwp, hbi1))

def split_g(+sp: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s0: R.RunSt, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +L0: B.Line,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +hold: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>},
  +hbi1: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(L0), 0n, BN.lend(L0))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.split(sp, o, s, qs, ql, ls, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match sp:
    case False{}:
      body_g(dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hA, hAw,
        MSX.vd_ok(fa, wp, back, B.Line.body(L0), hb, hwp), BV.vd_bud(fa, wp, back, L0, hb, hwp, hbi1))
    case True{}:
      parts_g(B.Rec.parts(dfs, o, B.Line.body(L0)), dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hb, hwp, hA, hAw, hbi1, {==})

# One line in the String mode (ms.line.k): a header line, or a body line
# (with -m, split first).
law clk_g:
  for +dfs: B.Defs
  for +ib: Bool
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +o: B.Opts
  for +s0: R.RunSt
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +L0: B.Line
  for +src: List<&2, P.SrcP>
  for +src2: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hold: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hwp: {PC.wp_ok(fa, wp) == True{} : Bool}
  for +hA: {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}
  for +hAw: {BN.ALL(P.mkSrcs(WS(ls, src2)), P.mkPd(pd), eof, cs) == Con{L0, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}
  for +hbi1: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(L0), 0n, BN.lend(L0))) == True{} : Bool}
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s0, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line.k(ib, o, s, qs, ql, ls, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))

def clk_g(dfs, ib, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hb, hwp, hA, hAw, hbi1):
  match ib:
    case False{}:
      done_g(dfs, fa, cs, o, s0, qs, ql, R.head_line(R.is_chrom_line(B.Line.body(L0)), R.tick(s), o, L0), src, src2, pd, eof, back, wp, fneed, hold, L0, hA)
    case True{}:
      split_g(R.Opts.split(o), dfs, fa, cs, o, s0, s, qs, ql, ls, L0, src, src2, pd, eof, back, wp, fneed, hold, hb, hwp, hA, hAw, hbi1)

# A text line q before src2 (no records): the lines still to come.
def hA_txt(+src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hn0: {S.no_recs(src) == True{} : Bool}, +hn2: {S.no_recs(src2) == True{} : Bool}) ->
  {BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs) == Con{B.Text.line(q), BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)} : List<&2, B.Line>}:
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  Equal.trans(List<&2, B.Line>, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs), Con{B.Text.line(q), BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)},
    BL.all_nr(src, pd, eof, cs, hn0),
    Equal.trans(List<&2, B.Line>, BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs), Con{B.Text.line(q), L2}, Con{B.Text.line(q), BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)},
      lines_split(src, src2, pd, eof, cs, q, hst, hq, hn0, hn2),
      Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => Con{B.Text.line(q), z}, L2, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs), Equal.sym(List<&2, B.Line>, BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs), L2, BL.all_nr(src2, pd, eof, cs, hn2)))))

def clk(+dfs: B.Defs, +ib: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hn0: {S.no_recs(src) == True{} : Bool}, +hn2: {S.no_recs(src2) == True{} : Bool},
  +hbi1: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(B.Text.line(q)), 0n, BN.lend(B.Text.line(q)))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line.k(ib, o, s, qs, ql, Norm.LsT{q}, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  +hnw = W.and_tt(Bool.not(S.is_rec(P.SLP{q})), S.no_recs(src2), {==}, hn2)
  clk_g(dfs, ib, fa, cs, o, s, s, qs, ql, Norm.LsT{q}, B.Text.line(q), src, src2, pd, eof, back, wp, fneed, False{}, hb, hwp,
    hA_txt(src, src2, pd, eof, cs, q, hst, hq, hn0, hn2),
    hA_txt(Con{P.SLP{q}, src2}, src2, pd, eof, cs, q, PN.str_assoc(q, "\n", P.srcstext(src2)), hq, hnw, hn2), hbi1)

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

def cline(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hn0: {S.no_recs(src) == True{} : Bool}, +hn2: {S.no_recs(src2) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  +L0 = B.Text.line(q)
  +L2 = BN.lines(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +LN0 = BN.lines(P.mkSrcs(src), P.mkPd(pd), eof, cs)
  +hbi1 = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, LN0, Con{L0, L2}, lines_split(src, src2, pd, eof, cs, q, hst, hq, hn0, hn2),
    AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, BN.ALL(P.mkSrcs(src), P.mkPd(pd), eof, cs), LN0, BL.all_nr(src, pd, eof, cs, hn0), hbi))
  AB.subst(Norm.Adv, z => BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed), z),
    Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, Norm.LsT{q}, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)), Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)),
    Equal.sym(Norm.Adv, Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)), Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, Norm.LsT{q}, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)),
      MSX.mline_eq(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))),
    clk(dfs, R.RunSt.inbody(s), fa, cs, o, s, qs, ql, q, src, src2, pd, eof, back, wp, fneed, hb, hwp, hst, hq, hn0, hn2,
      or_z(Nat.is_eq(back, 0n), fa, wp, BN.lchrom(L0), BN.lend(L0), hbi1)))

# ---------------------------------------------------------------------------
# c.ms.sl: a text line source
# ---------------------------------------------------------------------------

def c_ms_sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, s, qs, ql, Norm.LsT{q}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp))):
  +pp = BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)
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
  cline(dfs, fa, cs, o, s, qs, ql, q, Con{P.SLP{q}, rest}, rest, pd, eof, back, wp, fneed, hb, W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
    PN.str_assoc(q, "\n", P.srcstext(rest)), W.and_r(E.is_bytes(q), P.nolf(q), hsl),
    W.and_tt(Bool.not(S.is_rec(P.SLP{q})), S.no_recs(rest), {==}, BL.rf_of(fa, pp, hw)), BL.rf_of(fa, pp, hw), hbi)

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

def cpart.k(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool, +pd2: P.PdP,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +eadd: {Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)) == P.mkPd(pd2) : Norm.Pd},
  +hp2: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  +Y = S.concat_if(eof, cs)
  +L = BN.lines(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)
  +L1 = BN.lines(P.mkSrcs(rest), P.mkPd(pd2), eof, cs)
  +e1 = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), String.append(BN.srcT(P.mkSrcs(rest)), String.append(BN.pdT(P.mkPd(pd2)), Y)),
    String.append(BN.srcT(P.mkSrcs(Con{P.SBP{len, t, d, at}, rest})), String.append(BN.pdT(P.mkPd(pd)), Y)), ptxt(rest, len, t, d, at, pd, pd2, Y, h1, hn, hsa, hp0, hp2))
  +A1 = BN.ALL(P.mkSrcs(rest), P.mkPd(pd2), eof, cs)
  +ea = Equal.trans(List<&2, B.Line>, L, L1, A1, Equal.sym(List<&2, B.Line>, L1, L, e1), Equal.sym(List<&2, B.Line>, A1, L1, BL.all_nr(rest, pd2, eof, cs, hnr)))
  +hle = AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, z), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, L)) == True{} : Bool},
    L, A1, ea, N.le_refl(BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, L)))
  +hbi2 = AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, L, A1, ea, hbi)
  %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) : BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), _, eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}})
  (hle, hbi2)

def cpart.g(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  pa: DPT.PAW(pd, len, t, at), sn: DPT.SNW(len, t, d, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  (pd2, q1) = pa
  (eadd, q2) = q1
  (hpd2, hp2) = q2
  (hn, hsa) = sn
  cpart.k(dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, pd2, hnr, h1, hn, hsa, hp0, eadd, hp2, hbi)

def csb_line(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, False{})):
  +A = P.btext(len, t, at, (j - at : U32))
  +hfit = {%Equal.sym(Nat, LI.n((j - at : U32)), Nat.sub(LI.n(j), LI.n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(j), LI.n(at))), LI.n(j), N.le_sub_add(LI.n(at), LI.n(j), hal)) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
    N.lt_to_le(LI.n(j), LI.n(len), hlt) : {Nat.is_le(Nat.add(LI.n(at), LI.n((j - at : U32))), LI.n(len)) == True{} : Bool}}
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), A), MSX.sb_text(len, t, d, at, (j - at : U32), hok, hfit)) :
    BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
      Norm.ms.sb.k(o, s, qs, ql, at, j, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, False{}))
  cline(dfs, fa, cs, o, s, qs, ql, A, Con{P.SBP{len, t, d, at}, rest}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, fneed,
    hb, hwp, MSX.hst_sb(len, t, d, at, j, rest, hsp), hn,
    W.and_tt(Bool.not(S.is_rec(P.SBP{len, t, d, at})), S.no_recs(rest), {==}, hnr), W.and_tt(Bool.not(S.is_rec(P.SBP{len, t, d, (j + 1 : U32)})), S.no_recs(rest), {==}, hnr), hbi)

def csb_split(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, False{})):
  (hsp, q1) = sl
  (hn, q2) = q1
  (hle, hby) = q2
  csb_line(dfs, fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hnr, hb, hwp, hbi, hok, hal, hlt, hsp, hn)

def csb_if(+dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +h2: {P.pd_ok(pd) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.if(part, o, s, qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{})):
  match part:
    case True{}:
      +hjl = {%U.is_eq_true(j, len, ep) : {LI.n(_) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}; hjf : {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}}
      +hfit = {%Equal.sym(Nat, LI.n((len - at : U32)), Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(len), LI.n(at))), LI.n(len), N.le_sub_add(LI.n(at), LI.n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
        N.le_refl(LI.n(len)) : {Nat.is_le(Nat.add(LI.n(at), LI.n((len - at : U32))), LI.n(len)) == True{} : Bool}}
      cpart.g(dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hnr, h1, hp0, hbi,
        LN.pend_add(pd, len, t, d, at, (len - at : U32), h2, hok, hfit),
        LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjl)))
    case False{}:
      +hjr = MSX.sb_jr(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr)
      +hlt = MSX.sb_jlt(len, j, W.and_r(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr), ep)
      csb_split(dfs, fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hnr, hb, hwp, hbi, hok, hal, hlt,
        LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf), hlt))

def csb_j(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hnr: {S.no_recs(rest) == True{} : Bool},
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +h1: {S.srcs_ok(Con{P.SBP{len, t, d, at}, rest}) == True{} : Bool},
  +h2: {P.pd_ok(pd) == True{} : Bool},
  +hp0: {String.is_empty(P.pdtext(pd)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: MSX.SBW(len, t, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{})):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
              Norm.ms.sb(o, s, qs, ql, at, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{}))
          csb_if(dfs, U32.is_eq(j, len), j, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hnr, hb, hwp, hbi, h1, h2, hp0, hok, hs, hjf, {==})

def c_ms_sb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, False{})):
  +pp = BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
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
  csb_j(dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, BL.rf_of(fa, pp, hw), hb, W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hbi, h1,
    W.c9_2(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), W.c9_4(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hok, hs, LN.lf_ok(len, t, d, at, hok, hs))

# ---------------------------------------------------------------------------
# The String mode's next source (proof_b_budget_adv.bend's c.mssrc): a
# record (SR) and a buffer of records (SP) too
# ---------------------------------------------------------------------------

# ms.line is ms.line.k on the line, for any line.
def mline_g(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +ls: Norm.Ls, +back: Nat, cx: Norm.Cx, win: Norm.Win) ->
  {Norm.ms.line(o, s, qs, ql, ls, back, cx, win) == Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, ls, Norm.Ls.line(ls), back, cx, win) : Norm.Adv}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      {==}

def ss_le(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP) -> {Nat.is_le(BN.WAS(fa, S.mkSt(fa, p), cs), BN.WAS(fa, S.mkSt(fa, p), cs)) == True{} : Bool}:
  N.le_refl(BN.WAS(fa, S.mkSt(fa, p), cs))

# A record (SR): the line is the record, the lines still to come after it
# by reduction.
def ms_sr_c(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +l: B.Line,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SRP{l}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SRP{l}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SRP{l}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp))):
  +pp = BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SRP{l}, rest}, pd, eof, back, wp, None{}, fneed)
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
  +s1 = Norm.rs_untick(s)
  AB.subst(Norm.Adv, z => BD.AdvC(fa, cs, pp, z),
    Norm.ms.line.k(R.RunSt.inbody(s1), o, s1, qs, ql, Norm.LsR{l}, l, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
    Norm.ms.line(o, s1, qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
    Equal.sym(Norm.Adv, Norm.ms.line(o, s1, qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
      Norm.ms.line.k(R.RunSt.inbody(s1), o, s1, qs, ql, Norm.LsR{l}, l, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
      mline_g(o, s1, qs, ql, Norm.LsR{l}, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp))),
    clk_g(dfs, R.RunSt.inbody(s1), fa, cs, o, s, s1, qs, ql, Norm.LsR{l}, l, Con{P.SRP{l}, rest}, rest, pd, eof, back, wp, fneed, True{}, hb,
      W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), {==}, {==}, or_z(Nat.is_eq(back, 0n), fa, wp, BN.lchrom(l), BN.lend(l), hbi)))

# The next record of a buffer (its LF at j): the record in front, the rest
# of the buffer after it.
def sp_line(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, Norm.rs_untick(s), qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, True{})):
  +A = P.btext(len, t, at, (j - at : U32))
  +L0 = Norm.line(A)
  +s1 = Norm.rs_untick(s)
  +pp = BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
  +src2 = {Con{P.SPP{len, t, d, (j + 1 : U32)}, rest} : List<&2, P.SrcP>}
  +A0 = BN.ALL(P.mkSrcs(Con{P.SPP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)
  +A1 = BN.ALL(P.mkSrcs(rest), P.mkPd(pd), eof, cs)
  +A2 = BN.ALL(P.mkSrcs(src2), P.mkPd(pd), eof, cs)
  +hfit = {%Equal.sym(Nat, LI.n((j - at : U32)), Nat.sub(LI.n(j), LI.n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(j), LI.n(at))), LI.n(j), N.le_sub_add(LI.n(at), LI.n(j), hal)) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
    N.lt_to_le(LI.n(j), LI.n(len), hlt) : {Nat.is_le(Nat.add(LI.n(at), LI.n((j - at : U32))), LI.n(len)) == True{} : Bool}}
  +hA = Equal.trans(List<&2, B.Line>, A0, Con{B.Text.line(A), A2}, Con{L0, A2},
    Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => List.append(&2, B.Line, z, A1), B.Text.lines(P.srctext(P.SPP{len, t, d, at})),
      Con{B.Text.line(A), B.Text.lines(P.srctext(P.SPP{len, t, d, (j + 1 : U32)}))}, HX.lines_sp(len, t, d, at, j, hsp, hn)),
    Equal.cong(B.Line, List<&2, B.Line>, z => z <> A2, B.Text.line(A), L0, Equal.sym(B.Line, L0, B.Text.line(A), LN.line_eq(A))))
  +hbi1 = or_z(Nat.is_eq(back, 0n), fa, wp, BN.lchrom(L0), BN.lend(L0),
    AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, A0, Con{L0, A2}, hA, hbi))
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), A), MSX.sb_text(len, t, d, at, (j - at : U32), hok, hfit)) :
    BD.AdvC(fa, cs, pp, Norm.ms.sb.k(o, s1, qs, ql, at, j, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, True{}))
  AB.subst(Norm.Adv, z => BD.AdvC(fa, cs, pp, z),
    Norm.ms.line.k(R.RunSt.inbody(s1), o, s1, qs, ql, Norm.LsR{L0}, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
    Norm.ms.line(o, s1, qs, ql, Norm.LsR{L0}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
    Equal.sym(Norm.Adv, Norm.ms.line(o, s1, qs, ql, Norm.LsR{L0}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
      Norm.ms.line.k(R.RunSt.inbody(s1), o, s1, qs, ql, Norm.LsR{L0}, L0, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp)),
      mline_g(o, s1, qs, ql, Norm.LsR{L0}, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp))),
    clk_g(dfs, R.RunSt.inbody(s1), fa, cs, o, s, s1, qs, ql, Norm.LsR{L0}, L0, Con{P.SPP{len, t, d, at}, rest}, src2, pd, eof, back, wp, fneed, True{}, hb, hwp, hA, {==}, hbi1))

def sp_sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.k(o, Norm.rs_untick(s), qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), dfs, True{})):
  (hsp, q1) = sl
  (hn, q2) = q1
  sp_line(dfs, fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hal, hlt, hsp, hn)

# A record buffer never ends without its LF (rtok): no partial line.
def sp_pf(+dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(P.SPP{len, t, d, at})) == True{} : Bool},
  +hl0: {U32.is_le(len, at) == False{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb.if(part, o, Norm.rs_untick(s), qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, True{})):
  match part:
    case True{}:
      +hjl = {%U.is_eq_true(j, len, ep) : {LI.n(_) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}; hjf : {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}}
      Empty.absurd(BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
          Norm.ms.sb.if(True{}, o, Norm.rs_untick(s), qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, True{})),
        HX.part_sp.k(len, t, d, at, hok, HX.ult(len, at, hl0), hlf,
          LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjl))))
    case False{}:
      +hjr = MSX.sb_jr(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr)
      +hlt = MSX.sb_jlt(len, j, W.and_r(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr), ep)
      sp_sl(dfs, fa, cs, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hal, hlt,
        LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf), hlt))

def sp_j(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(P.SPP{len, t, d, at})) == True{} : Bool},
  +hl0: {U32.is_le(len, at) == False{} : Bool},
  ex: MSX.SBW(len, t, at)) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.ms.sb(o, Norm.rs_untick(s), qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, True{})):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
              Norm.ms.sb(o, Norm.rs_untick(s), qs, ql, at, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed, dfs, True{}))
          sp_pf(dfs, U32.is_eq(j, len), j, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hs, hlf, hl0, hjf, {==})

# A record buffer: dropped when read to its end (its bytes left give no
# line); else its next record.
def sp_dn(+dn: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(P.SPP{len, t, d, at})) == True{} : Bool},
  +edn: {U32.is_le(len, at) == dn : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.sp.s.if(dn, o, s, qs, ql, C.BT(len, t), at, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match dn:
    case True{}:
      +A0 = BN.ALL(P.mkSrcs(Con{P.SPP{len, t, d, at}, rest}), P.mkPd(pd), eof, cs)
      +A1 = BN.ALL(P.mkSrcs(rest), P.mkPd(pd), eof, cs)
      +E = Equal.cong(String, List<&2, B.Line>, z => List.append(&2, B.Line, B.Text.lines(z), A1), P.srctext(P.SPP{len, t, d, at}), "", HX.em_sp(len, t, d, at, hok, edn))
      (AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, A1), BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, z)) == True{} : Bool},
         A1, A0, Equal.sym(List<&2, B.Line>, A0, A1, E), N.le_refl(BN.WAX(fa, o, False{}, back, PC.mkWin(fa, wp), None{}, A1))),
       AB.subst(List<&2, B.Line>, z => {BN.bi.ls(back, PC.mkWin(fa, wp), None{}, z) == True{} : Bool}, A0, A1, E, hbi))
    case False{}:
      sp_j(dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hwp, hbi, hok, hs, hlf, edn, LN.lf_ok(len, t, d, at, hok, hs))

def ms_sp_c(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
    Norm.sp.s(o, s, qs, ql, BY.len(C.BT(len, t)), at, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  +pp = BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)
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
  +X = P.srctext(P.SPP{len, t, d, at})
  +hso = HX.srcs_head_p(rest, len, t, d, at, W.c9_1(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hrt = W.and_l(S.rtok(X), S.recs_first(rest), BL.rf_of(fa, pp, hw))
  sp_dn(U32.is_le(len, at), dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc), hbi, hok, hs,
    W.and_l(S.ends_lf(X), S.all_one(B.Text.lines(X)), hrt), {==})

# proof_b_budget_adv.bend's c.mssrc (its statement).
def c_mssrc_h(+dfs: B.Defs, +src: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
  BD.AdvC(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, None{}, fneed),
    Norm.ms.src(P.mkSrcs(src), o, s, qs, ql, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  match src:
    case Nil{}:
      (ss_le(fa, cs, BD.StM(dfs, o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, eof, back, wp, None{}, fneed)), hbi)
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      c_ms_sb(dfs, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)
    case Con{P.SLP{+q}, +rest}:
      c_ms_sl(dfs, fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbi)
    case Con{P.SRP{+l}, +rest}:
      ms_sr_c(dfs, fa, cs, o, s, qs, ql, l, rest, pd, eof, back, wp, fneed, hb, hw, hbi)
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      ms_sp_c(dfs, fa, cs, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hbi)
