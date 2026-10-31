import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_b_budget_lem.bend as BL
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_e_qif_fed.bend as F
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_run.bend as RN
import ./LAWS.bend as L
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_e_qif_step.bend as QS

# Phase E, area E2: a piece fed to Q (Q.feed after the room, or W.feed_line)
# keeps what the budget reads of Q's state: the mode bit, back, the window and
# asked are untouched (feed.k only moves input), and the text still to come
# is the same (area F's Fed). So WA and bi over the pieces after it are WA and
# bi before it over the piece and those pieces (phase B's FedG).

# The fields the budget reads besides the input.
def stK(st: Norm.St) -> B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))):
  match st:
    case Norm.St{+o, md, src, pend, eof, +back, win, asked, +fneed, +dfs}:
      (o, (BN.fast_left(md, fneed), (back, (win, asked))))

def wak(+fa: List<&2, B.Contig>, k: B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), +ls: List<&2, B.Line>) -> Nat:
  (+o, k0) = k
  (+fl, k1) = k0
  (+bk, k2) = k1
  (w, m) = k2
  BN.WAX(fa, o, fl, bk, w, m, ls)

def bik(k: B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), +ls: List<&2, B.Line>) -> Bool:
  (+o, k0) = k
  (fl, k1) = k0
  (+bk, k2) = k1
  (w, m) = k2
  BN.bi.ls(bk, w, m, ls)

# With no record source in front, the lines still to come are the plain
# ones (BN.ALL is BN.lines).
law all_lines:
  for +sps: List<&2, P.SrcP>
  for -pend: Norm.Pd
  for +eof: Bool
  for +cs: List<&2, String>
  for +h: {S.recs(sps) == Nil{} : List<&2, P.SrcP>}
  {BN.ALL(P.mkSrcs(sps), pend, eof, cs) == BN.lines(P.mkSrcs(sps), pend, eof, cs) : List<&2, B.Line>}

def all_lines(sps, pend, eof, cs, h):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      {==}
    case Con{P.SLP{+q}, +r}:
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      Empty.absurd({BN.ALL(P.mkSrcs(Con{P.SPP{len, t, d, at}, r}), pend, eof, cs) == BN.lines(P.mkSrcs(Con{P.SPP{len, t, d, at}, r}), pend, eof, cs) : List<&2, B.Line>},
        PB.false_ne_true(Equal.cong(List<&2, P.SrcP>, Bool, z => List.is_empty(&2, P.SrcP, z), Con{P.SPP{len, t, d, at}, S.recs(r)}, Nil{}, h)))
    case Con{P.SRP{+l}, +r}:
      Empty.absurd({BN.ALL(P.mkSrcs(Con{P.SRP{l}, r}), pend, eof, cs) == BN.lines(P.mkSrcs(Con{P.SRP{l}, r}), pend, eof, cs) : List<&2, B.Line>},
        PB.false_ne_true(Equal.cong(List<&2, P.SrcP>, Bool, z => List.is_empty(&2, P.SrcP, z), Con{P.SRP{l}, S.recs(r)}, Nil{}, h)))

# A good state's sources have their records first (WF's last test).
law wf_rf:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  {S.recs_first(S.StP.src(p)) == True{} : Bool}

def wf_rf(fa, p, hw):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +h8 = DO.x9_8(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
        Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))), PC.wp_ok(fa, wp), S.mb_win(md, wp),
        E.all_bytes(S.opts_args(o)) && S.recs_first(src) && S.recs_run(md, src), hw)
      PB.and_true_r(E.all_bytes(S.opts_args(o)), S.recs_first(src), PB.and_true_l(E.all_bytes(S.opts_args(o)) && S.recs_first(src), S.recs_run(md, src), h8))

# feed.k's branches keep the fields
# =================================

law fk_all:
  for +dfs: B.Defs
  for +o: B.Opts
  for md: Norm.Md
  for r: D.Bytes & U32
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.all(o, md, r, pend, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk_all(dfs,o, md, r, pend, eof, back, win, asked, fneed):
  (b, +n) = r
  {==}

law fk_join:
  for +dfs: B.Defs
  for +o: B.Opts
  for md: Norm.Md
  for +k: U32
  for p: Norm.Pd & D.Bytes
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.join(o, md, k, p, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk_join(dfs,o, md, k, p, eof, back, win, asked, fneed):
  (j, b) = p
  {==}

law fk_lf:
  for +dfs: B.Defs
  for none: Bool
  for +o: B.Opts
  for md: Norm.Md
  for b: D.Bytes
  for +k: U32
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.lf(none, o, md, b, k, pend, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk_lf(dfs,none, o, md, b, k, pend, eof, back, win, asked, fneed):
  match none:
    case True{}:
      fk_all(dfs, o, md, BY.len(b), pend, eof, back, win, asked, fneed)
    case False{}:
      fk_join(dfs, o, md, k, Norm.join.k(pend, b, k), eof, back, win, asked, fneed)

law fk_find:
  for +dfs: B.Defs
  for +o: B.Opts
  for md: Norm.Md
  for t: NF.Tb
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.find(o, md, t, pend, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk_find(dfs,o, md, t, pend, eof, back, win, asked, fneed):
  match t:
    case NF.Tb{b, +k, none, x}:
      fk_lf(dfs, none, o, md, b, k, pend, eof, back, win, asked, fneed)

law fk_if:
  for +dfs: B.Defs
  for empty: Bool
  for +o: B.Opts
  for md: Norm.Md
  for src: List<&1, Norm.Src>
  for b: D.Bytes
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.if(empty, o, md, src, b, pend, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk_if(dfs,empty, o, md, src, b, pend, eof, back, win, asked, fneed):
  match empty:
    case True{}:
      {==}
    case False{}:
      fk_find(dfs, o, md, NF.lf(b, 0), pend, eof, back, win, asked, fneed)

law fk:
  for +dfs: B.Defs
  for +o: B.Opts
  for md: Norm.Md
  for src: List<&1, Norm.Src>
  for b: D.Bytes
  for r: Norm.Pd & Nat
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {stK(Norm.feed.k(o, md, src, b, r, eof, back, win, asked, fneed, dfs)) == (o, (BN.fast_left(md, fneed), (back, (win, asked)))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}

def fk(dfs,o, md, src, b, r, eof, back, win, asked, fneed):
  (pend, +n) = r
  fk_if(dfs, Nat.is_eq(n, 0n), o, md, src, b, pend, eof, back, win, asked, fneed)

# From Fed to FedG
# ================

law fedg_k2:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +L: List<&2, String>
  for +c: String
  for +o: B.Opts
  for +md: S.MdP
  for +md0: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for -X: Norm.St
  for +p1: S.StP
  for +e: {X == S.mkSt(fa, p1) : Norm.St}
  for +hK: {stK(X) == (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}
  for +hi1: {S.intext(p1, L) == S.intext(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}, c <> L) : String}
  for +hrc: {S.recs(S.StP.src(p1)) == Nil{} : List<&2, P.SrcP>}
  for +hw: {S.WF(fa, p1) == True{} : Bool}
  {Nat.is_le(BDs.WP(fa, L, p1), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs})) == True{} : Bool}
    & {BN.biS(S.mkSt(fa, p1), L) == BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> L) : Bool}

def fedg_k2(dfs,fa, L, c, o, md, md0, pd, back, wp, fneed, X, p1, e, hK, hi1, hrc, hw):
  match p1:
    case S.StP{+o1, +md1, +src1, +pd1, +eof1, +back1, +wp1, +asked1, +fneed1, +dfs}:
      +q1 = {S.StP{o1, md1, src1, pd1, eof1, back1, wp1, asked1, fneed1, dfs} : S.StP}
      +q0 = {S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      +qp = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      +hf = wf_rf(fa, q1, hw)
      +s1 = String.append(BN.srcT(P.mkSrcs(src1)), String.append(BN.pdT(P.mkPd(pd1)), S.concat_if(eof1, L)))
      +s0 = String.append(BN.srcT(P.mkSrcs(Nil{})), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(False{}, c <> L)))
      +es = Equal.trans(String, s1, S.intext(q1, L), s0, BL.text_pic(q1, L, hf),
        Equal.trans(String, S.intext(q1, L), S.intext(q0, c <> L), s0, hi1, Equal.sym(String, s0, S.intext(q0, c <> L), BL.text_pic(q0, c <> L, {==}))))
      +el = Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), s1, s0, es)
      +ek = Equal.trans(B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), stK(S.mkSt(fa, q1)), stK(X), (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))),
        Equal.sym(B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), stK(X), stK(S.mkSt(fa, q1)), Equal.cong(Norm.St, B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), z => stK(z), X, S.mkSt(fa, q1), e)), hK)
      +l1 = B.Text.lines(s1)
      +l0 = B.Text.lines(s0)
      +a1 = BN.ALL(P.mkSrcs(src1), P.mkPd(pd1), eof1, L)
      +ea = Equal.trans(List<&2, B.Line>, a1, l1, l0, all_lines(src1, P.mkPd(pd1), eof1, L, hrc), el)
      (%Equal.sym(B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), stK(S.mkSt(fa, q1)), (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))), ek) :
         {Nat.is_le(wak(fa, _, a1), BDs.WP(fa, c <> L, qp)) == True{} : Bool};
       %Equal.sym(List<&2, B.Line>, a1, l0, ea) : {Nat.is_le(wak(fa, (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))), _), BDs.WP(fa, c <> L, qp)) == True{} : Bool};
       N.le_refl(BDs.WP(fa, c <> L, qp)),
       %Equal.sym(B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), stK(S.mkSt(fa, q1)), (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))), ek) :
         {bik(_, a1) == BN.biS(S.mkSt(fa, qp), c <> L) : Bool};
       %Equal.sym(List<&2, B.Line>, a1, l0, ea) : {bik((o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))), _) == BN.biS(S.mkSt(fa, qp), c <> L) : Bool};
       {==})

law fedg_k3:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +L: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +md0: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for -X: Norm.St
  for +p1: S.StP
  for +e: {X == S.mkSt(fa, p1) : Norm.St}
  for +hw: {S.WF(fa, p1) == True{} : Bool}
  for +hmd: {S.StP.md(p1) == S.StP.md(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) : S.MdP}
  for +ho: {S.StP.o(p1) == S.StP.o(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) : B.Opts}
  for +ha: {S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hiL: {S.intext(p1, L) == S.intext(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}, c <> L) : String}
  for +hdf: {S.StP.dfs(p1) == S.StP.dfs(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) : B.Defs}
  for +hrc: {S.recs(S.StP.src(p1)) == S.recs(S.StP.src(S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs})) : List<&2, P.SrcP>}
  for +hr0: {S.report(fa, c <> L, O, N, S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg0: {S.guard(O, N, S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> L) == True{} : Bool}
  for r: {Nat.is_le(BDs.WP(fa, L, p1), BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs})) == True{} : Bool}
    & {BN.biS(S.mkSt(fa, p1), L) == BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> L) : Bool}
  BDs.FedG(fa, T, L, O, N, BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), X)

def fedg_k3(dfs,fa, T, c, L, O, N, o, md, md0, pd, back, wp, fneed, X, p1, e, hw, hmd, ho, ha, hiL, hdf, hrc, hr0, hg0, hbi, r):
  (hle, hbe) = r
  +p0 = {S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +p = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  (p1, (e, (hw, (Equal.trans(R.Report, S.report(fa, L, O, N, p1), S.report(fa, c <> L, O, N, p0), T, QS.rep_of(fa, L, O, N, c, p0, p1, hmd, ho, hiL, hdf, hrc), hr0),
    (AB.subst(S.MdP, m => {Bool.or(R.RunSt.inbody(S.smd(m)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}, S.StP.md(p0), S.StP.md(p1),
       Equal.sym(S.MdP, S.StP.md(p1), S.StP.md(p0), hmd), hg0),
    (ha, (hle, Equal.trans(Bool, BN.biS(S.mkSt(fa, p1), L), BN.biS(S.mkSt(fa, p), c <> L), True{}, hbe, hbi))))))))

# A Fed state is a FedG state for the budget, given that feed.k kept the fields.
law fedg_k:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +L: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +md: S.MdP
  for +md0: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for -X: Norm.St
  for +hK: {stK(X) == (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))) : B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))}
  for +hr0: {S.report(fa, c <> L, O, N, S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report}
  for +hg0: {S.guard(O, N, S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> L) == True{} : Bool}
  for f: F.Fed(fa, c, S.StP{o, md0, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}, X)
  BDs.FedG(fa, T, L, O, N, BDs.WP(fa, c <> L, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), X)

def fedg_k(dfs,fa, T, c, L, O, N, o, md, md0, pd, back, wp, fneed, X, hK, hr0, hg0, hbi, f):
  (+p1, f1) = f
  (+e, f2) = f1
  (+hw, f3) = f2
  (+hmd, f4) = f3
  (+ho, f5) = f4
  (+ha, f6) = f5
  (+he, f7) = f6
  (+hdf, f8) = f7
  (+hrc, hi) = f8
  +hiL = hi(L)
  fedg_k3(dfs, fa, T, c, L, O, N, o, md, md0, pd, back, wp, fneed, X, p1, e, hw, hmd, ho, ha, hiL, hdf, hrc, hr0, hg0, hbi,
    fedg_k2(dfs, fa, L, c, o, md, md0, pd, back, wp, fneed, X, p1, e, hK, hiL, hrc, hw))

# The run gets room for the piece (proof_b_drive_chunk.bend's chunk_mb2).
def fb_mb2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +e: {NR.reserve(P.mkRun(rp), len) == P.mkRun(rp2) : NR.Run},
  +hi2: {RN.RunInv(rp2) == True{} : Bool},
  +hs: {P.specRun(rp2) == P.specRun(rp) : R.RunSt},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool}) ->
  BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  +md = {S.MBP{rp} : S.MdP}
  +md2 = {S.MBP{rp2} : S.MdP}
  +hw2 = DO.x9_mk(S.md_ok(md2), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md2, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hi2,
    DO.x9_1(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_4(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw),
    DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw))
  +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +q2 = {S.StP{o, md2, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +hr2 = Equal.trans(R.Report, S.report(fa, c <> cs, O, N, q2), S.report(fa, c <> cs, O, N, q), T,
    Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(B.Text.lines(S.intext(q, c <> cs)), fa, L.defs.go(B.Text.lines(S.intext(q, c <> cs)), R.RunSt.inbody(z), dfs), o, S.pre(O, N, z))), P.specRun(rp2), P.specRun(rp), hs), hr)
  +hg2 = AB.subst(R.RunSt, z => {Bool.or(R.RunSt.inbody(z), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}, P.specRun(rp), P.specRun(rp2),
    Equal.sym(R.RunSt, P.specRun(rp2), P.specRun(rp), hs), hg)
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), len), P.mkRun(rp2), e) :
    BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))
  fedg_k(dfs, fa, T, c, cs, O, N, o, md, md2, pd, back, wp, fneed, Norm.feed.k(o, S.mkMd(md2), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs),
    fk(dfs, o, S.mkMd(md2), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed), hr2, hg2, hbi,
    F.core(dfs, fa, c, len, t, d, o, md2, pd, back, wp, fneed, hw2, hok, hv))


def fb_mb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), len) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32}))),
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool}) ->
  BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (hs, ho) = r3
  fb_mb2(dfs, fa, T, c, cs, O, N, o, rp, rp2, pd, back, wp, fneed, len, t, d, hb, hw, hr, hg, hok, hv, e, hi2, hs, hbi)

# By the run's mode (the String mode's run has no buffer).
def fb_md(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +md: S.MdP, +pd: P.PdP, +back: Nat, +wp: PC.WP, +fneed: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == T : R.Report},
  +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hbi: {BN.biS(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), c <> cs) == True{} : Bool}) ->
  BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Norm.feed(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), C.BT(len, t))):
  match md:
    case S.MBP{+rp}:
      fb_mb(dfs, fa, T, c, cs, O, N, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hr, hg, hok, hv,
        RN.run_reserve(rp, len, DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), E.all_bytes(S.opts_args(o)) && True{} && True{}, hw)), hbi)
    case S.MSP{+s, +qs, +ql, +code}:
      +md0 = {S.MSP{s, qs, ql, code} : S.MdP}
      fedg_k(dfs, fa, T, c, cs, O, N, o, md0, md0, pd, back, wp, fneed, Norm.feed.k(o, S.mkMd(md0), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs),
        fk(dfs, o, S.mkMd(md0), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed), hr, hg, hbi,
        F.core(dfs, fa, c, len, t, d, o, md0, pd, back, wp, fneed, hw, hok, hv))



# By the state (a state waiting for more has no source, is before the end of
# the file and asked nothing).
def fedg_bt(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, p), Norm.feed(S.mkSt(fa, p), C.BT(len, t))):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), Norm.feed(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      fb_md(dfs, fa, T, c, cs, O, N, o, md, pd, back, wp, fneed, len, t, d, hb, DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hr, hg, hok, hv, hbi)

def fedg_line(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, p), W.feed_line(S.mkSt(fa, p), C.BT(len, t))):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(BDs.FedG(fa, T, cs, O, N, BDs.WP(fa, c <> cs, q), W.feed_line(S.mkSt(fa, q), C.BT(len, t))),
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      fedg_k(dfs, fa, T, c, cs, O, N, o, md, md, pd, back, wp, fneed, W.feed_line(S.mkSt(fa, q), C.BT(len, t)),
        fk(dfs, o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed), hr, hg, hbi,
        F.core(dfs, fa, c, len, t, d, o, md, pd, back, wp, fneed, DS.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hok, hv))

# The opts a state carries (stK's first field).
def opt.k(k: B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>)))) -> B.Opts:
  (+o, r) = k
  o

def opt(st: Norm.St) -> B.Opts:
  opt.k(stK(st))

law opt_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {opt(S.mkSt(fa, p)) == S.StP.o(p) : B.Opts}

def opt_mk(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      {==}

# A piece fed to a state waiting for more keeps its opts.
law opt_fl:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +len: U32
  for +t: AT.Tree<U32>
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  {opt(W.feed_line(S.mkSt(fa, p), C.BT(len, t))) == S.StP.o(p) : B.Opts}

def opt_fl(fa, p, len, t, hm):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd({opt(W.feed_line(S.mkSt(fa, q), C.BT(len, t))) == o : B.Opts},
        PB.false_ne_true(DS.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd({opt(W.feed_line(S.mkSt(fa, q), C.BT(len, t))) == o : B.Opts},
        PB.false_ne_true(DS.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd({opt(W.feed_line(S.mkSt(fa, q), C.BT(len, t))) == o : B.Opts},
        PB.false_ne_true(DS.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      Equal.cong(B.Opts & (Bool & (Nat & (Norm.Win & Maybe<&2, List<&2, Pr.Req>>))), B.Opts, z => opt.k(z),
        stK(Norm.feed.k(o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)),
        (o, (BN.fast_left(S.mkMd(md), fneed), (back, (PC.mkWin(fa, wp), None{})))),
        fk(dfs, o, S.mkMd(md), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed))

# The state a fed piece leads to keeps the opts.
law fed_o:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +len: U32
  for +t: AT.Tree<U32>
  for +p1: S.StP
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +e1: {W.feed_line(S.mkSt(fa, p), C.BT(len, t)) == S.mkSt(fa, p1) : Norm.St}
  {S.StP.o(p1) == S.StP.o(p) : B.Opts}

def fed_o(fa, p, len, t, p1, hm, e1):
  Equal.trans(B.Opts, S.StP.o(p1), opt(S.mkSt(fa, p1)), S.StP.o(p),
    Equal.sym(B.Opts, opt(S.mkSt(fa, p1)), S.StP.o(p1), opt_mk(fa, p1)),
    Equal.trans(B.Opts, opt(S.mkSt(fa, p1)), opt(W.feed_line(S.mkSt(fa, p), C.BT(len, t))), S.StP.o(p),
      Equal.cong(Norm.St, B.Opts, z => opt(z), S.mkSt(fa, p1), W.feed_line(S.mkSt(fa, p), C.BT(len, t)), Equal.sym(Norm.St, W.feed_line(S.mkSt(fa, p), C.BT(len, t)), S.mkSt(fa, p1), e1)),
      opt_fl(fa, p, len, t, hm)))
