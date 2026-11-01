import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./norm_run.bend as NR
import lawful-bytes@0.1.1.0/proof_core.bend as C
import ./proof_b_lines_str.bend as LSS
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_lem.bend as BL
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_base.bend as PB

# The budget walk's byte-mode leaves (proof_b_budget_adv.bend's c.mb.sb).

# ---------------------------------------------------------------------------
# A line's share
# ---------------------------------------------------------------------------

def pk_le(+b: Bool, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(BN.pick(b, x), y) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      N.le_zero_l(y)

def pk_mono(+b: Bool, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(BN.pick(b, x), BN.pick(b, y)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

# What a line has left is at most its allowance.
def rem_le(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line) ->
  {Nat.is_le(BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l), BN.LA(fa, l)) == True{} : Bool}:
  +RW = BN.RW(l)
  +ZW = BN.ZW(fa)
  pk_mono(BN.lgate(l), Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW)),
      Nat.add(BN.pick(Nat.is_eq(back, 0n), ZW), BN.pick(Nat.is_lt(back, BN.lpos(l)), ZW))),
    Nat.add(Nat.add(RW, RW), Nat.add(ZW, ZW)),
    PB.le_add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW)), Nat.add(RW, RW),
      Nat.add(BN.pick(Nat.is_eq(back, 0n), ZW), BN.pick(Nat.is_lt(back, BN.lpos(l)), ZW)), Nat.add(ZW, ZW),
      PB.le_add(BN.pick(fl, RW), RW, BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW), RW,
        pk_le(fl, RW, RW, N.le_refl(RW)), pk_le(Bool.not(BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW, RW, N.le_refl(RW))),
      PB.le_add(BN.pick(Nat.is_eq(back, 0n), ZW), ZW, BN.pick(Nat.is_lt(back, BN.lpos(l)), ZW), ZW,
        pk_le(Nat.is_eq(back, 0n), ZW, ZW, N.le_refl(ZW)), pk_le(Nat.is_lt(back, BN.lpos(l)), ZW, ZW, N.le_refl(ZW)))))

# WA of the lines after the first, with any state, is at most WA with it.
def wa_tail(+fa: List<&2, B.Contig>, +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>,
  +fl2: Bool, +back2: Nat, +wp2: PC.WP, +m2: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line, +ls: List<&2, B.Line>) ->
  {Nat.is_le(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, l <> ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      N.le_zero_l(Nat.add(BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l), 0n))
    case +l2 <> +t:
      +R1 = BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l)
      N.le_trans(Nat.add(BN.rem(fa, fl2, back2, PC.mkWin(fa, wp2), m2, l2), BN.LAs(fa, t)), BN.LAs(fa, l2 <> t), Nat.add(R1, BN.LAs(fa, l2 <> t)),
        N.le_add_mono_r(BN.LAs(fa, t), BN.rem(fa, fl2, back2, PC.mkWin(fa, wp2), m2, l2), BN.LA(fa, l2), rem_le(fa, fl2, back2, wp2, m2, l2)),
        N.le_add_l(BN.LAs(fa, l2 <> t), R1))

# The same with the extra allowances: XA of the lines after the first is at
# most XA with it.
def wax_tail(+fa: List<&2, B.Contig>, +o: B.Opts, +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>,
  +fl2: Bool, +back2: Nat, +wp2: PC.WP, +m2: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line, +ls: List<&2, B.Line>) ->
  {Nat.is_le(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, ls), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, l <> ls)) == True{} : Bool}:
  PB.le_add(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, l <> ls),
    BN.XA(o, fa, ls), Nat.add(BN.xa(o, fa, l), BN.XA(o, fa, ls)),
    wa_tail(fa, fl, back, wp, m, fl2, back2, wp2, m2, l, ls), N.le_add_l(BN.XA(o, fa, ls), BN.xa(o, fa, l)))

# The same lines: WAX follows WA.
def wax_le(+fa: List<&2, B.Contig>, +o: B.Opts, +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>,
  +fl2: Bool, +back2: Nat, +wp2: PC.WP, +m2: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>,
  +h: {Nat.is_le(BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls), BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls)) == True{} : Bool}) ->
  {Nat.is_le(BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, ls), BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, ls)) == True{} : Bool}:
  N.le_add_mono_r(BN.XA(o, fa, ls), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls), BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls), h)

# A Want on the same lines: what it pays from WA it pays from WAX.
def wax_want(+fa: List<&2, B.Contig>, +o: B.Opts, +K: Nat, +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>,
  +fl2: Bool, +back2: Nat, +wp2: PC.WP, +m2: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>,
  +h: {Nat.is_le(Nat.add(K, BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls)), BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(K, BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, ls)), BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, ls)) == True{} : Bool}:
  +A = BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls)
  +X = BN.XA(o, fa, ls)
  AB.subst(Nat, z => {Nat.is_le(z, Nat.add(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls), X)) == True{} : Bool}, Nat.add(Nat.add(K, A), X), Nat.add(K, Nat.add(A, X)),
    N.add_assoc(K, A, X), N.le_add_mono_r(X, Nat.add(K, A), BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, ls), h))

def TP(+p: S.StP, +cs: List<&2, String>) -> String:
  String.append(BN.srcT(P.mkSrcs(S.StP.src(p))), String.append(BN.pdT(P.mkPd(BL.pdp(p))), S.concat_if(S.StP.eof(p), cs)))

# The text still to come starts with the line (its LF at j), then the text
# from j + 1 (as LI.itx, on the state's text).
def tpx(+dfs: B.Defs, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j)) ->
  {String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", TP(BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2), cs)))
    == TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs) : String}:
  +A = P.btext(len, t, at, (j - at : U32))
  +S1 = P.srctext(P.SBP{len, t, d, (j + 1 : U32)})
  +R0 = BN.srcT(P.mkSrcs(rest))
  +X = String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))
  %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), String.append(A, String.append("\n", S1)), hs) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(String.append(_, R0), X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append("\n", S1)), R0), String.append(A, String.append(String.append("\n", S1), R0)), LSS.sassoc(A, String.append("\n", S1), R0)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(_, X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append(String.append("\n", S1), R0)), X), String.append(A, String.append(String.append(String.append("\n", S1), R0), X)), LSS.sassoc(A, String.append(String.append("\n", S1), R0), X)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == _ : String}
  {==}

# The lines still to come: the line, then those from j + 1.
def tpl(+dfs: B.Defs, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {B.Text.lines(TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs))
    == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2), cs)) : List<&2, B.Line>}:
  +A = P.btext(len, t, at, (j - at : U32))
  +T1 = TP(BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2), cs)
  +T0 = TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs)
  Equal.trans(List<&2, B.Line>, B.Text.lines(T0), B.Text.lines(String.append(A, String.append("\n", T1))), B.Text.line(A) <> B.Text.lines(T1),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), T0, String.append(A, String.append("\n", T1)),
      Equal.sym(String, String.append(A, String.append("\n", T1)), T0, tpx(dfs, cs, o, md, md2, len, t, d, at, j, rest, pd, eof, back, back2, wp, wp2, asked, asked2, fneed, fneed2, hs))),
    LSS.lines_cons(A, T1, hn))

# A byte-mode line handled (the source moves past its LF): WA drops, whatever
# the state after it.
def went_done(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {Nat.is_le(BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2)), cs),
    BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)), cs)) == True{} : Bool}:
  +pre = BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +post = BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2)
  +A = P.btext(len, t, at, (j - at : U32))
  +fl = BN.fast_left(S.mkMd(md), fneed)
  +fl2 = BN.fast_left(S.mkMd(md2), fneed2)
  +LP = B.Text.lines(TP(post, cs))
  +e1 = tpl(dfs, cs, o, md, md2, len, t, d, at, j, rest, pd, eof, back, back2, wp, wp2, asked, asked2, fneed, fneed2, hs, hn)
  AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), asked2, LP), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), asked, z)) == True{} : Bool},
    B.Text.line(A) <> LP, B.Text.lines(TP(pre, cs)), Equal.sym(List<&2, B.Line>, B.Text.lines(TP(pre, cs)), B.Text.line(A) <> LP, e1),
    wax_tail(fa, o, fl, back, wp, asked, fl2, back2, wp2, asked2, B.Text.line(A), LP))

# bi holds once back is 0 (after a line).
def bi0(+fa: List<&2, B.Contig>, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>) ->
  {BN.bi.ls(0n, PC.mkWin(fa, wp), m, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      {==}

# The text still to come starts with the line (its LF at j), then the rest
# (the source from j + 1).
def lines_head(+dfs: B.Defs, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {B.Text.lines(TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs))
    == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(dfs, o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2), cs)) : List<&2, B.Line>}:
  tpl(dfs, cs, o, md, md2, len, t, d, at, j, rest, pd, eof, back, back2, wp, wp2, asked, asked2, fneed, fneed2, hs, hn)

# WA of a state whose source starts with the line: the line's rem, then the
# rest's allowances.
def wa_split(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {BN.WAS(fa, S.mkSt(fa, BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)), cs)
    == BN.WAX(fa, o, BN.fast_left(S.mkMd(md), fneed), back, PC.mkWin(fa, wp), asked,
      B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed), cs))) : Nat}:
  +fl = BN.fast_left(S.mkMd(md), fneed)
  Equal.cong(List<&2, B.Line>, Nat, z => BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), asked, z),
    B.Text.lines(TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs)),
    B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(dfs, o, md, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed), cs)),
    lines_head(dfs, cs, o, md, md, len, t, d, at, j, rest, pd, eof, back, back, wp, wp, asked, asked, fneed, fneed, hs, hn))

# bi with back = 0.
def bi_b0(+fa: List<&2, B.Contig>, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +ls: List<&2, B.Line>, +h: {Nat.is_eq(back, 0n) == True{} : Bool}) ->
  {BN.bi.ls(back, PC.mkWin(fa, wp), m, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      h
    case +l <> +t:
      AB.subst(Bool, z => {Bool.or(z, BN.heldZ(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lend(l))) == True{} : Bool}, True{}, Nat.is_eq(back, 0n),
        Equal.sym(Bool, Nat.is_eq(back, 0n), True{}, h), {==})

# With no window held, bi says back = 0.
def bz_none(+back: Nat, +ls: List<&2, B.Line>, +h: {BN.bi.ls(back, Norm.WNone{}, None{}, ls) == True{} : Bool}) -> {Nat.is_eq(back, 0n) == True{} : Bool}:
  match ls:
    case Nil{}:
      h
    case +l <> +t:
      Equal.trans(Bool, Nat.is_eq(back, 0n), Bool.or(Nat.is_eq(back, 0n), False{}), True{}, Equal.sym(Bool, Bool.or(Nat.is_eq(back, 0n), False{}), Nat.is_eq(back, 0n), N.or_false_r(Nat.is_eq(back, 0n))), h)

# The fast path's Want pays from the line's fast term: the gate holds, the
# Ask covers the line's window, and 1 + |rs| <= RW.
def want_rem(+fa: List<&2, B.Contig>, +back: Nat, +wp: PC.WP, +rs: List<&2, Pr.Req>, +l: B.Line,
  +hg: {BN.lgate(l) == True{} : Bool},
  +hc: {BN.coversA(Some{rs}, BN.lchrom(l), BN.lp1(l), BN.lend(l)) == True{} : Bool},
  +hk: {Nat.is_le(1n+List.length(&2, Pr.Req, rs), BN.RW(l)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, rs), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), Some{rs}, l)), BN.rem(fa, True{}, back, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool}:
  +K = {1n+List.length(&2, Pr.Req, rs) : Nat}
  +RW = BN.RW(l)
  +H = BN.pick(Bool.not(BN.heldA(PC.mkWin(fa, wp), None{}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW)
  +Z = Nat.add(BN.pick(Nat.is_eq(back, 0n), BN.ZW(fa)), BN.pick(Nat.is_lt(back, BN.lpos(l)), BN.ZW(fa)))
  +h1 = N.le_add_mono_r(Z, K, Nat.add(RW, H), N.le_trans(K, RW, Nat.add(RW, H), hk, N.le_add_r(RW, H)))
  +h2 = AB.subst(Bool, z => {Nat.is_le(Nat.add(K, Nat.add(Nat.add(0n, BN.pick(Bool.not(z), RW)), Z)), Nat.add(Nat.add(RW, H), Z)) == True{} : Bool}, True{},
    BN.coversA(Some{rs}, BN.lchrom(l), BN.lp1(l), BN.lend(l)), Equal.sym(Bool, BN.coversA(Some{rs}, BN.lchrom(l), BN.lp1(l), BN.lend(l)), True{}, hc), h1)
  AB.subst(Bool, z => {Nat.is_le(Nat.add(K, BN.pick(z, Nat.add(Nat.add(0n, BN.pick(Bool.not(BN.coversA(Some{rs}, BN.lchrom(l), BN.lp1(l), BN.lend(l))), RW)), Z))), BN.pick(z, Nat.add(Nat.add(RW, H), Z))) == True{} : Bool},
    True{}, BN.lgate(l), Equal.sym(Bool, BN.lgate(l), True{}, hg), h2)

# ---------------------------------------------------------------------------
# The line at a byte or record source (hold: a record of a split line, -m)
# ---------------------------------------------------------------------------

# Every line still to come from a state whose first source is the bytes of
# the line at x (SXP: plain, or records).
def AP(+hold: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +x: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>) -> List<&2, B.Line>:
  BN.ALL(P.mkSrcs(Con{LI.SXP(hold, len, t, d, x), rest}), P.mkPd(pd), eof, cs)

def TX0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>) -> String:
  String.append(BN.srcT(P.mkSrcs(Con{P.SBP{len, t, d, x}, rest})), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs)))

def tpx0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>,
  +hs: LI.SPLIT(len, t, d, at, j)) ->
  {String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", TX0(len, t, d, (j + 1 : U32), rest, pd, eof, cs))) == TX0(len, t, d, at, rest, pd, eof, cs) : String}:
  +A = P.btext(len, t, at, (j - at : U32))
  +S1 = P.srctext(P.SBP{len, t, d, (j + 1 : U32)})
  +R0 = BN.srcT(P.mkSrcs(rest))
  +X = String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))
  %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), String.append(A, String.append("\n", S1)), hs) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(String.append(_, R0), X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append("\n", S1)), R0), String.append(A, String.append(String.append("\n", S1), R0)), LSS.sassoc(A, String.append("\n", S1), R0)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(_, X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append(String.append("\n", S1), R0)), X), String.append(A, String.append(String.append(String.append("\n", S1), R0), X)), LSS.sassoc(A, String.append(String.append("\n", S1), R0), X)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == _ : String}
  {==}

# The lines from the line at at: the line, then those from j + 1 (any hold).
law allx:
  for +hold: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +j: U32
  for +rest: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +cs: List<&2, String>
  for +hs: LI.SPLIT(len, t, d, at, j)
  for +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}
  {AP(hold, len, t, d, at, rest, pd, eof, cs) == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs) : List<&2, B.Line>}

def allx(hold, len, t, d, at, j, rest, pd, eof, cs, hs, hn):
  match hold:
    case False{}:
      +A = P.btext(len, t, at, (j - at : U32))
      +T1 = TX0(len, t, d, (j + 1 : U32), rest, pd, eof, cs)
      +T0 = TX0(len, t, d, at, rest, pd, eof, cs)
      Equal.trans(List<&2, B.Line>, B.Text.lines(T0), B.Text.lines(String.append(A, String.append("\n", T1))), B.Text.line(A) <> B.Text.lines(T1),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), T0, String.append(A, String.append("\n", T1)),
          Equal.sym(String, String.append(A, String.append("\n", T1)), T0, tpx0(len, t, d, at, j, rest, pd, eof, cs, hs))),
        LSS.lines_cons(A, T1, hn))
    case True{}:
      +A = P.btext(len, t, at, (j - at : U32))
      +S0 = P.srctext(P.SBP{len, t, d, at})
      +S1 = P.srctext(P.SBP{len, t, d, (j + 1 : U32)})
      +R = BN.ALL(P.mkSrcs(rest), P.mkPd(pd), eof, cs)
      Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => List.append(&2, B.Line, z, R), B.Text.lines(S0), B.Text.line(A) <> B.Text.lines(S1),
        Equal.trans(List<&2, B.Line>, B.Text.lines(S0), B.Text.lines(String.append(A, String.append("\n", S1))), B.Text.line(A) <> B.Text.lines(S1),
          Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S0, String.append(A, String.append("\n", S1)), hs),
          LSS.lines_cons(A, S1, hn)))

# The line at at consumed (any hold): WAX drops, whatever the state after it.
def went_ap(+hold: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>,
  +fl: Bool, +back: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +fl2: Bool, +back2: Nat, +wp2: PC.WP, +m2: Maybe<&2, List<&2, Pr.Req>>,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {Nat.is_le(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs)), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, AP(hold, len, t, d, at, rest, pd, eof, cs))) == True{} : Bool}:
  +L1 = AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs)
  +A = B.Text.line(P.btext(len, t, at, (j - at : U32)))
  AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, L1), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, z)) == True{} : Bool},
    A <> L1, AP(hold, len, t, d, at, rest, pd, eof, cs), Equal.sym(List<&2, B.Line>, AP(hold, len, t, d, at, rest, pd, eof, cs), A <> L1, allx(hold, len, t, d, at, j, rest, pd, eof, cs, hs, hn)),
    wax_tail(fa, o, fl, back, wp, m, fl2, back2, wp2, m2, A, L1))

# WAS of a state whose first source holds the line at at (any hold): its
# rem, then the rest's allowances, with XA.
def wa_split_h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), cs)
    == BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), asked, B.Text.line(P.btext(len, t, at, (j - at : U32))) <> AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs)) : Nat}:
  Equal.cong(List<&2, B.Line>, Nat, z => BN.WAX(fa, o, Bool.not(fneed), back, PC.mkWin(fa, wp), asked, z),
    AP(hold, len, t, d, at, rest, pd, eof, cs), B.Text.line(P.btext(len, t, at, (j - at : U32))) <> AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs),
    allx(hold, len, t, d, at, j, rest, pd, eof, cs, hs, hn))

# The machine's state after the line at at (done.b, any hold): WAS and bi.
def went_of(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +wp2: PC.WP, +fneed: Bool, x: NR.Run,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {Nat.is_le(BN.WAS(fa, Norm.St{o, Norm.MB{x}, Con{Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp2), None{}, False{}, dfs}, cs),
    BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool}:
  %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrc(LI.SXP(hold, len, t, d, (j + 1 : U32))), HX.so_eq(hold, len, t, d, (j + 1 : U32))) :
    {Nat.is_le(BN.WAS(fa, Norm.St{o, Norm.MB{x}, Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp2), None{}, False{}, dfs}, cs),
      BN.WAS(fa, S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs)) == True{} : Bool}
  went_ap(hold, fa, o, cs, Bool.not(fneed), back, wp, None{}, True{}, 0n, wp2, None{}, len, t, d, at, j, rest, pd, eof, hs, hn)

def bi_of(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp2: PC.WP, x: NR.Run) ->
  {BN.biS(Norm.St{o, Norm.MB{x}, Con{Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp2), None{}, False{}, dfs}, cs) == True{} : Bool}:
  %Equal.sym(Norm.Src, Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrc(LI.SXP(hold, len, t, d, (j + 1 : U32))), HX.so_eq(hold, len, t, d, (j + 1 : U32))) :
    {BN.biS(Norm.St{o, Norm.MB{x}, Con{_, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp2), None{}, False{}, dfs}, cs) == True{} : Bool}
  bi0(fa, wp2, None{}, AP(hold, len, t, d, (j + 1 : U32), rest, pd, eof, cs))
