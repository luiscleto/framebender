import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_adv_line.bend as LI
import ./proof_b_lines_str.bend as LSS
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_lem.bend as BL
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
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

def TP(+p: S.StP, +cs: List<&2, String>) -> String:
  String.append(BN.srcT(P.mkSrcs(S.StP.src(p))), String.append(BN.pdT(P.mkPd(BL.pdp(p))), S.concat_if(S.StP.eof(p), cs)))

# A byte-mode line handled (the source moves past its LF): WA drops, whatever
# the state after it.
def went_done(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {Nat.is_le(BN.WAS(fa, S.mkSt(fa, BD.StM(o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2)), cs),
    BN.WAS(fa, S.mkSt(fa, BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)), cs)) == True{} : Bool}:
  +pre = BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +post = BD.StM(o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2)
  +A = P.btext(len, t, at, (j - at : U32))
  +fl = BN.fast_left(S.mkMd(md), fneed)
  +fl2 = BN.fast_left(S.mkMd(md2), fneed2)
  +LP = B.Text.lines(TP(post, cs))
  +e1 = Equal.trans(List<&2, B.Line>, B.Text.lines(TP(pre, cs)), B.Text.lines(S.intext(pre, cs)), B.Text.line(A) <> LP,
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), TP(pre, cs), S.intext(pre, cs), BL.text_pic(pre, cs)),
    Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(pre, cs)), B.Text.lines(String.append(A, String.append("\n", S.intext(post, cs)))), B.Text.line(A) <> LP,
      Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(pre, cs), String.append(A, String.append("\n", S.intext(post, cs))),
        Equal.sym(String, String.append(A, String.append("\n", S.intext(post, cs))), S.intext(pre, cs), LI.itx(o, md, md2, rest, pd, eof, back, back2, wp, asked, asked2, fneed, fneed2, cs, len, t, d, at, j, hs))),
      Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(A, String.append("\n", S.intext(post, cs)))), B.Text.line(A) <> B.Text.lines(S.intext(post, cs)), B.Text.line(A) <> LP,
        LSS.lines_cons(A, S.intext(post, cs), hn),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.line(A) <> B.Text.lines(z), S.intext(post, cs), TP(post, cs), Equal.sym(String, TP(post, cs), S.intext(post, cs), BL.text_pic(post, cs))))))
  AB.subst(List<&2, B.Line>, z => {Nat.is_le(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), asked2, LP), BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), asked, z)) == True{} : Bool},
    B.Text.line(A) <> LP, B.Text.lines(TP(pre, cs)), Equal.sym(List<&2, B.Line>, B.Text.lines(TP(pre, cs)), B.Text.line(A) <> LP, e1),
    wa_tail(fa, fl, back, wp, asked, fl2, back2, wp2, asked2, B.Text.line(A), LP))

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
def lines_head(+cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +md2: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +back2: Nat, +wp: PC.WP, +wp2: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +asked2: Maybe<&2, List<&2, Pr.Req>>,
  +fneed: Bool, +fneed2: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {B.Text.lines(TP(BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs))
    == B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2), cs)) : List<&2, B.Line>}:
  +pre = BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +post = BD.StM(o, md2, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back2, wp2, asked2, fneed2)
  +A = P.btext(len, t, at, (j - at : U32))
  +LP = B.Text.lines(TP(post, cs))
  Equal.trans(List<&2, B.Line>, B.Text.lines(TP(pre, cs)), B.Text.lines(S.intext(pre, cs)), B.Text.line(A) <> LP,
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), TP(pre, cs), S.intext(pre, cs), BL.text_pic(pre, cs)),
    Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(pre, cs)), B.Text.lines(String.append(A, String.append("\n", S.intext(post, cs)))), B.Text.line(A) <> LP,
      Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(pre, cs), String.append(A, String.append("\n", S.intext(post, cs))),
        Equal.sym(String, String.append(A, String.append("\n", S.intext(post, cs))), S.intext(pre, cs), LI.itx(o, md, md2, rest, pd, eof, back, back2, wp, asked, asked2, fneed, fneed2, cs, len, t, d, at, j, hs))),
      Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(A, String.append("\n", S.intext(post, cs)))), B.Text.line(A) <> B.Text.lines(S.intext(post, cs)), B.Text.line(A) <> LP,
        LSS.lines_cons(A, S.intext(post, cs), hn),
        Equal.cong(String, List<&2, B.Line>, z => B.Text.line(A) <> B.Text.lines(z), S.intext(post, cs), TP(post, cs), Equal.sym(String, TP(post, cs), S.intext(post, cs), BL.text_pic(post, cs))))))

# WA of a state whose source starts with the line: the line's rem, then the
# rest's allowances.
def wa_split(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +o: B.Opts, +md: S.MdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  {BN.WAS(fa, S.mkSt(fa, BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)), cs)
    == Nat.add(BN.rem(fa, BN.fast_left(S.mkMd(md), fneed), back, PC.mkWin(fa, wp), asked, B.Text.line(P.btext(len, t, at, (j - at : U32)))),
      BN.LAs(fa, B.Text.lines(TP(BD.StM(o, md, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed), cs)))) : Nat}:
  +fl = BN.fast_left(S.mkMd(md), fneed)
  Equal.cong(List<&2, B.Line>, Nat, z => BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), asked, z),
    B.Text.lines(TP(BD.StM(o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), cs)),
    B.Text.line(P.btext(len, t, at, (j - at : U32))) <> B.Text.lines(TP(BD.StM(o, md, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed), cs)),
    lines_head(cs, o, md, md, len, t, d, at, j, rest, pd, eof, back, back, wp, wp, asked, asked, fneed, fneed, hs, hn))

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
