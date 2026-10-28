import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ./LAWS.bend as L
import ./norm_line.bend as J
import ./proof_b_budget.bend as BG
import ./proof_b_bud_win.bend as BW
import ./proof_b_bud_fm.bend as FM
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_adv_wf.bend as W
import ./proof_b_cache_lem.bend as X
import ./proof_fast.bend as PF
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
import ./bytes_enc.bend as E
import ./proof_window_lists.bend as WL
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY

# ---------------------------------------------------------------------------
# The verdict's Want pays: tools
# ---------------------------------------------------------------------------

# A line the slow path reaches is not malformed (judge_fs decides those).
def gate_k(+bad: Bool, +skip: Bool, +fs: List<&2, String>, +body: String,
  +hm: {J.judge_in.go(bad, skip, None{}, fs, body) == None{} : Maybe<&2, B.Res>}) -> {bad == False{} : Bool}:
  match bad:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.cong(Maybe<&2, B.Res>, Bool, z => Maybe.is_some(&2, B.Res, z), None{}, J.judge_in.go(True{}, skip, None{}, fs, body),
        Equal.sym(Maybe<&2, B.Res>, J.judge_in.go(True{}, skip, None{}, fs, body), None{}, hm))))

def gate(+l: B.Line, +hm: {J.judge_fs(None{}, BN.lfs(l), B.Line.body(l)) == None{} : Maybe<&2, B.Res>}) -> {BN.lgate(l) == True{} : Bool}:
  %Equal.sym(Bool, B.Rec.malformed(BN.lfs(l)), False{}, gate_k(B.Rec.malformed(BN.lfs(l)), B.Rec.out_of_scope(BN.lfs(l)), BN.lfs(l), B.Line.body(l), hm)) :
    {Bool.not(_) == True{} : Bool}
  {==}

# A window that holds from a holds from any later start.
def hmono(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +a2: Nat, +b: Nat,
  +h: {PC.holds(fa, wp, c, a, b) == True{} : Bool}, +ha: {Nat.is_le(a, a2) == True{} : Bool}) ->
  {PC.holds(fa, wp, c, a2, b) == True{} : Bool}:
  match wp:
    case PC.WPNone{}:
      Empty.absurd({PC.holds(fa, PC.WPNone{}, c, a2, b) == True{} : Bool}, N.false_ne_true(h))
    case PC.WPUnk{+c0}:
      h
    case PC.WPKnown{+c0, +a0, +b0}:
      +S0 = Maybe.is_some(&2, String, B.Fasta.find(fa, c0))
      +E0 = String.eq(c0, c)
      +K0 = PC.wp.clen(fa, c0)
      +Lb = Nat.is_le(Nat.min(b, K0), Nat.min(b0, K0))
      +I1 = W.and_r(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), h)
      +I2 = W.and_l(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1)
      W.and_tt(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a2)), Lb), W.and_l(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), h),
        W.and_tt(Bool.and(E0, Nat.is_le(a0, a2)), Lb,
          W.and_tt(E0, Nat.is_le(a0, a2), W.and_l(E0, Nat.is_le(a0, a), I2), N.le_trans(a0, a, a2, W.and_r(E0, Nat.is_le(a0, a), I2), ha)),
          W.and_r(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1)))
    case PC.WPStr{+c0, +a0, +b0}:
      +S0 = Maybe.is_some(&2, String, B.Fasta.find(fa, c0))
      +E0 = String.eq(c0, c)
      +K0 = PC.wp.clen(fa, c0)
      +Lb = Nat.is_le(Nat.min(b, K0), Nat.min(b0, K0))
      +I1 = W.and_r(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), h)
      +I2 = W.and_l(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1)
      W.and_tt(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a2)), Lb), W.and_l(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), h),
        W.and_tt(Bool.and(E0, Nat.is_le(a0, a2)), Lb,
          W.and_tt(E0, Nat.is_le(a0, a2), W.and_l(E0, Nat.is_le(a0, a), I2), N.le_trans(a0, a, a2, W.and_r(E0, Nat.is_le(a0, a), I2), ha)),
          W.and_r(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1)))

def nlt_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nlt_le(p, q, h)

def le_gr(+b: Nat) -> {Nat.is_le(b, Nat.add(Nat.mul(b, 2n), 1n)) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      N.le_trans(p, Nat.add(Nat.mul(p, 2n), 1n), 1n+Nat.add(Nat.mul(p, 2n), 1n), le_gr(p), N.le_add_l(Nat.add(Nat.mul(p, 2n), 1n), 1n))

# With the window not held at a, the miss's read a .. e.
def nh.k(+v: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +e: Nat,
  +hv: {BN.holdsW(PC.mkWin(fa, wp), c, a, e) == v : Bool},
  +hh: {PC.holds(fa, wp, c, a, e) == False{} : Bool}) ->
  {BN.holdsW(PC.mkWin(fa, wp), c, a, e) == False{} : Bool}:
  match v:
    case False{}:
      hv
    case True{}:
      Empty.absurd({BN.holdsW(PC.mkWin(fa, wp), c, a, e) == False{} : Bool},
        N.false_ne_true(Equal.trans(Bool, False{}, PC.holds(fa, wp, c, a, e), True{}, Equal.sym(Bool, PC.holds(fa, wp, c, a, e), False{}, hh), BW.hold_of(fa, wp, c, a, e, hv))))

def nh(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +e: Nat, +hh: {PC.holds(fa, wp, c, a, e) == False{} : Bool}) ->
  {BN.holdsW(PC.mkWin(fa, wp), c, a, e) == False{} : Bool}:
  nh.k(BN.holdsW(PC.mkWin(fa, wp), c, a, e), fa, wp, c, a, e, {==}, hh)

# "Too small" means REF fits its contig, so the line's end is within FM.
def efm.k(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +body: String, +a: Nat,
  +hf: {B.Fasta.find(fa, MSX.TC(body)) == m : Maybe<&2, String>},
  +hF: {J.fast(Some{PC.jtruth.k(m, a, MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(MSX.TE(body), BN.FM(fa)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_le(MSX.TE(body), BN.FM(fa)) == True{} : Bool},
        BW.nope(J.fast(Some{J.Unknown{}}, J.pfs(body), body), BW.unk_on(B.Rec.malformed(J.pfs(body)), B.Rec.out_of_scope(J.pfs(body)), J.pfs(body), body), hF))
    case Some{+r}:
      N.le_trans(MSX.TE(body), String.length(r), BN.FM(fa),
        BW.fast_none_fits(String.length(r), Nat.min(a, String.length(r)), PC.letters(r, a, MSX.TE(body)), J.pfs(body), body, hF),
        FM.find_fm(fa, MSX.TC(body), r, hf))

def efm(+fa: List<&2, B.Contig>, +body: String, +a: Nat,
  +hF: {J.fast(Some{PC.jtruth(fa, MSX.TC(body), a, MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(MSX.TE(body), BN.FM(fa)) == True{} : Bool}:
  efm.k(B.Fasta.find(fa, MSX.TC(body)), fa, body, a, {==}, hF)

# With the answer from 0, J.fast decides (as in zero_decides).
def zfast(+fa: List<&2, B.Contig>, +body: String, +a: Nat, +hta: {a == 0n : Nat}) ->
  {BW.isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), a, MSX.TE(body))}, J.pfs(body), body)) == False{} : Bool}:
  +C0 = B.Rec.field(B.Rec.fields(body), 0n)
  +E1 = Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(B.Rec.field(B.Rec.fields(body), 3n)))
  +hF0 = BW.zm(B.Fasta.find(fa, C0), fa, body, {==})
  +hF1 = AB.subst(String, z => {BW.isON(J.fast(Some{PC.jtruth(fa, z, 0n, E1)}, J.pfs(body), body)) == False{} : Bool}, C0, MSX.TC(body),
    Equal.sym(String, MSX.TC(body), C0, PF.pfs_field(body, 0n, {==})), hF0)
  +hF2 = AB.subst(Nat, z => {BW.isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), z, E1)}, J.pfs(body), body)) == False{} : Bool}, 0n, a,
    Equal.sym(Nat, a, 0n, hta), hF1)
  AB.subst(Nat, z => {BW.isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), a, z)}, J.pfs(body), body)) == False{} : Bool}, E1, MSX.TE(body),
    Equal.sym(Nat, MSX.TE(body), E1, BW.eqTE(body)), hF2)

# A try at back b that says "too small" had b < POS - 1 (from b >= POS - 1 the
# try starts at 0 and decides).
def blt.k(+v: Bool, +fa: List<&2, B.Contig>, +body: String, +b: Nat,
  +hv: {Nat.is_lt(b, Nat.sub(B.Rec.pos(J.pfs(body)), 1n)) == v : Bool},
  +hF: {J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(b, body), MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_lt(b, Nat.sub(B.Rec.pos(J.pfs(body)), 1n)) == True{} : Bool}:
  match v:
    case True{}:
      hv
    case False{}:
      +P1 = Nat.sub(B.Rec.pos(J.pfs(body)), 1n)
      Empty.absurd({Nat.is_lt(b, P1) == True{} : Bool},
        BW.nope(J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(b, body), MSX.TE(body))}, J.pfs(body), body),
          zfast(fa, body, MSX.TA(b, body), BW.subz(P1, b, nlt_le(b, P1, hv))), hF))

def blt(+fa: List<&2, B.Contig>, +body: String, +b: Nat,
  +hF: {J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(b, body), MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_lt(b, Nat.sub(B.Rec.pos(J.pfs(body)), 1n)) == True{} : Bool}:
  blt.k(Nat.is_lt(b, Nat.sub(B.Rec.pos(J.pfs(body)), 1n)), fa, body, b, {==}, hF)

def pk(+b: Bool, +n: Nat) -> {Nat.is_le(BN.pick(b, n), n) == True{} : Bool}:
  match b:
    case True{}:
      N.le_refl(n)
    case False{}:
      N.le_zero_l(n)

def am(+a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +h1: {Nat.is_le(a1, b1) == True{} : Bool}, +h2: {Nat.is_le(a2, b2) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a1, a2), Nat.add(b1, b2)) == True{} : Bool}:
  N.le_trans(Nat.add(a1, a2), Nat.add(b1, a2), Nat.add(b1, b2), N.le_add_mono_r(a2, a1, b1, h1), N.le_add_mono_l(b1, a2, b2, h2))

# The window that served a try saying "too small" fits the line: it is the
# line's contig's, and REF ends within it (Z1).
def zwk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +e: Nat) ->
  {BN.zfit(Norm.win_of.k(c0, a0, b0, clen, off, r), c, e) == Bool.and(String.eq(c0, c), Nat.is_le(e, clen)) : Bool}:
  match r:
    case (raw, rl):
      {==}

def zk2(+r: String, +c0: String, +a0: Nat, +b0: Nat, +str: Bool, +c: String, +e: Nat,
  +hc: {String.eq(c0, c) == True{} : Bool}, +hle: {Nat.is_le(e, String.length(r)) == True{} : Bool}) ->
  {BN.zfit(PC.mkWin.k(Some{r}, c0, a0, b0, str), c, e) == True{} : Bool}:
  match str:
    case False{}:
      Equal.trans(Bool, BN.zfit(PC.mkWin.k(Some{r}, c0, a0, b0, False{}), c, e), Bool.and(String.eq(c0, c), Nat.is_le(e, String.length(r))), True{},
        zwk(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0))), c, e),
        W.and_tt(String.eq(c0, c), Nat.is_le(e, String.length(r)), hc, hle))
    case True{}:
      W.and_tt(String.eq(c0, c), Nat.is_le(e, String.length(r)), hc, hle)

def zf_w(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +e: Nat, +r: String,
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hle: {Nat.is_le(e, String.length(r)) == True{} : Bool},
  +hh: {PC.holds(fa, wp, c, a, e) == True{} : Bool}) ->
  {BN.zfit(PC.mkWin(fa, wp), c, e) == True{} : Bool}:
  match wp:
    case PC.WPNone{}:
      Empty.absurd({BN.zfit(PC.mkWin(fa, PC.WPNone{}), c, e) == True{} : Bool}, N.false_ne_true(hh))
    case PC.WPUnk{+c0}:
      +ec = WL.string_eq_sound(c0, c, hh)
      +hn = AB.subst(String, z => {Maybe.is_none(&2, String, B.Fasta.find(fa, z)) == True{} : Bool}, c0, c, ec, hwp)
      +hn2 = AB.subst(Maybe<&2, String>, z => {Maybe.is_none(&2, String, z) == True{} : Bool}, B.Fasta.find(fa, c), Some{r}, hf, hn)
      Empty.absurd({BN.zfit(PC.mkWin(fa, PC.WPUnk{c0}), c, e) == True{} : Bool}, N.false_ne_true(hn2))
    case PC.WPKnown{+c0, +a0, +b0}:
      +S0 = Maybe.is_some(&2, String, B.Fasta.find(fa, c0))
      +E0 = String.eq(c0, c)
      +K0 = PC.wp.clen(fa, c0)
      +Lb = Nat.is_le(Nat.min(e, K0), Nat.min(b0, K0))
      +I1 = W.and_r(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), hh)
      +hc = W.and_l(E0, Nat.is_le(a0, a), W.and_l(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1))
      +ec = WL.string_eq_sound(c0, c, hc)
      +hm = AB.subst(String, z => {B.Fasta.find(fa, z) == Some{r} : Maybe<&2, String>}, c, c0, Equal.sym(String, c0, c, ec), hf)
      AB.subst(Maybe<&2, String>, z => {BN.zfit(PC.mkWin.k(z, c0, a0, b0, False{}), c, e) == True{} : Bool}, Some{r}, B.Fasta.find(fa, c0),
        Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm), zk2(r, c0, a0, b0, False{}, c, e, hc, hle))
    case PC.WPStr{+c0, +a0, +b0}:
      +S0 = Maybe.is_some(&2, String, B.Fasta.find(fa, c0))
      +E0 = String.eq(c0, c)
      +K0 = PC.wp.clen(fa, c0)
      +Lb = Nat.is_le(Nat.min(e, K0), Nat.min(b0, K0))
      +I1 = W.and_r(S0, Bool.and(Bool.and(E0, Nat.is_le(a0, a)), Lb), hh)
      +hc = W.and_l(E0, Nat.is_le(a0, a), W.and_l(Bool.and(E0, Nat.is_le(a0, a)), Lb, I1))
      +ec = WL.string_eq_sound(c0, c, hc)
      +hm = AB.subst(String, z => {B.Fasta.find(fa, z) == Some{r} : Maybe<&2, String>}, c, c0, Equal.sym(String, c0, c, ec), hf)
      AB.subst(Maybe<&2, String>, z => {BN.zfit(PC.mkWin.k(z, c0, a0, b0, True{}), c, e) == True{} : Bool}, Some{r}, B.Fasta.find(fa, c0),
        Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm), zk2(r, c0, a0, b0, True{}, c, e, hc, hle))

def zfi.k(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +wp: PC.WP, +body: String, +a: Nat,
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hf: {B.Fasta.find(fa, MSX.TC(body)) == m : Maybe<&2, String>},
  +hh: {PC.holds(fa, wp, MSX.TC(body), a, MSX.TE(body)) == True{} : Bool},
  +hF: {J.fast(Some{PC.jtruth.k(m, a, MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {BN.zfit(PC.mkWin(fa, wp), MSX.TC(body), MSX.TE(body)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({BN.zfit(PC.mkWin(fa, wp), MSX.TC(body), MSX.TE(body)) == True{} : Bool},
        BW.nope(J.fast(Some{J.Unknown{}}, J.pfs(body), body), BW.unk_on(B.Rec.malformed(J.pfs(body)), B.Rec.out_of_scope(J.pfs(body)), J.pfs(body), body), hF))
    case Some{+r}:
      zf_w(fa, wp, MSX.TC(body), a, MSX.TE(body), r, hwp, hf,
        BW.fast_none_fits(String.length(r), Nat.min(a, String.length(r)), PC.letters(r, a, MSX.TE(body)), J.pfs(body), body, hF), hh)

def zfi(+fa: List<&2, B.Contig>, +wp: PC.WP, +body: String, +a: Nat,
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hh: {PC.holds(fa, wp, MSX.TC(body), a, MSX.TE(body)) == True{} : Bool},
  +hF: {J.fast(Some{PC.jtruth(fa, MSX.TC(body), a, MSX.TE(body))}, J.pfs(body), body) == J.Other{None{}} : J.Fast}) ->
  {BN.zfit(PC.mkWin(fa, wp), MSX.TC(body), MSX.TE(body)) == True{} : Bool}:
  zfi.k(B.Fasta.find(fa, MSX.TC(body)), fa, wp, body, a, hwp, {==}, hh, hF)

# rem with its gate open and its tests known.
def remv(+fa: List<&2, B.Contig>, +fl: Bool, +b: Nat, +wp: PC.WP, +m: Maybe<&2, List<&2, Pr.Req>>, +l: B.Line, +V: Bool, +Z: Bool, +Z2: Bool,
  +hg: {BN.lgate(l) == True{} : Bool},
  +hv: {BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l)) == V : Bool},
  +hz: {Nat.is_eq(b, 0n) == Z : Bool},
  +hz2: {Nat.is_lt(b, BN.lpos(l)) == Z2 : Bool}) ->
  {BN.rem(fa, fl, b, PC.mkWin(fa, wp), m, l) == Nat.add(Nat.add(BN.pick(fl, BN.RW(l)), BN.pick(Bool.not(V), BN.RW(l))), Nat.add(BN.pick(Z, BN.ZW(fa)), BN.pick(Z2, BN.ZW(fa)))) : Nat}:
  +RW = BN.RW(l)
  +ZW = BN.ZW(fa)
  +HD = BN.heldA(PC.mkWin(fa, wp), m, BN.lchrom(l), BN.lp1(l), BN.lend(l))
  +RHS = Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(V), RW)), Nat.add(BN.pick(Z, ZW), BN.pick(Z2, ZW)))
  %Equal.sym(Bool, BN.lgate(l), True{}, hg) :
    {BN.pick(_, Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(HD), RW)), Nat.add(BN.pick(Nat.is_eq(b, 0n), ZW), BN.pick(Nat.is_lt(b, BN.lpos(l)), ZW)))) == RHS : Nat}
  %Equal.sym(Bool, HD, V, hv) :
    {Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(_), RW)), Nat.add(BN.pick(Nat.is_eq(b, 0n), ZW), BN.pick(Nat.is_lt(b, BN.lpos(l)), ZW))) == RHS : Nat}
  %Equal.sym(Bool, Nat.is_eq(b, 0n), Z, hz) :
    {Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(V), RW)), Nat.add(BN.pick(_, ZW), BN.pick(Nat.is_lt(b, BN.lpos(l)), ZW))) == RHS : Nat}
  %Equal.sym(Bool, Nat.is_lt(b, BN.lpos(l)), Z2, hz2) :
    {Nat.add(Nat.add(BN.pick(fl, RW), BN.pick(Bool.not(V), RW)), Nat.add(BN.pick(Z, ZW), BN.pick(_, ZW))) == RHS : Nat}
  {==}

# The Asks cover the line's windows.
def cov_rs(+rs: List<&2, Pr.Req>, +c: String, +a: Nat, +a2: Nat, +e: Nat, +e2: Nat,
  +h1: {X.hd1(rs, c, a) == True{} : Bool},
  +hl: {Norm.last_b(rs, 0n) == e : Nat},
  +ha: {Nat.is_le(a, a2) == True{} : Bool},
  +he: {Nat.is_le(e2, e) == True{} : Bool}) ->
  {BN.coversA(Some{rs}, c, a2, e2) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({BN.coversA(Some{Nil{}}, c, a2, e2) == True{} : Bool}, N.false_ne_true(h1))
    case Con{Pr.Req{+c1, +a1, +b1}, +t}:
      +ea = N.eq_sound(a1, a, W.and_r(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      W.and_tt(Bool.and(String.eq(c1, c), Nat.is_le(a1, a2)), Nat.is_le(e2, Norm.last_b(t, b1)),
        W.and_tt(String.eq(c1, c), Nat.is_le(a1, a2), W.and_l(String.eq(c1, c), Nat.is_eq(a1, a), h1),
          {%Equal.sym(Nat, a1, a, ea) : {Nat.is_le(_, a2) == True{} : Bool}; ha : {Nat.is_le(a1, a2) == True{} : Bool}}),
        {%Equal.sym(Nat, Norm.last_b(t, b1), e, hl) : {Nat.is_le(e2, _) == True{} : Bool}; he : {Nat.is_le(e2, Norm.last_b(t, b1)) == True{} : Bool}})

def cov_parts(+c: String, +a: Nat, +a2: Nat, +e: Nat, +e2: Nat, +ha: {Nat.is_le(a, a2) == True{} : Bool}, +he: {Nat.is_le(e2, e) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.parts(c, a, e)}, c, a2, e2) == True{} : Bool}:
  +x = Nat.sub(e, a)
  cov_rs(Norm.parts(c, a, e), c, a, a2, e, e2, X.ph(x, Norm.le31(x), c, a, e), X.plast(x, Norm.le31(x), c, a, e, 0n), ha, he)

def cov_reqof.k(+one: Bool, +c: String, +a: Nat, +e: Nat, +a3: Nat, +ha: {Nat.is_le(a, a3) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.Req.of.k(one, c, a, e, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead())))}, c, a3, e) == True{} : Bool}:
  match one:
    case True{}:
      +A2 = Nat.sub(a, Norm.margin())
      W.and_tt(Bool.and(String.eq(c, c), Nat.is_le(A2, a3)), Nat.is_le(e, Nat.max(e, Nat.add(a, Norm.ahead()))),
        W.and_tt(String.eq(c, c), Nat.is_le(A2, a3), X.str_eq_refl(c), N.le_trans(A2, a, a3, X.sub_le(a, Norm.margin()), ha)),
        X.le_max_l(e, Nat.add(a, Norm.ahead())))
    case False{}:
      cov_parts(c, a, a3, e, e, ha, N.le_refl(e))

def cov_reqof(+c: String, +a: Nat, +a3: Nat, +e: Nat, +ha: {Nat.is_le(a, a3) == True{} : Bool}) ->
  {BN.coversA(Some{Norm.Req.of(c, a, e)}, c, a3, e) == True{} : Bool}:
  cov_reqof.k(Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))), c, a, e, a3, ha)

# Small Nat facts.
def ne0(+b: Nat, +h: {Nat.is_le(1n, b) == True{} : Bool}) -> {Nat.is_eq(b, 0n) == False{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, N.false_ne_true(h))
    case 1n+p:
      {==}

def lt0(+b: Nat, +h: {Nat.is_le(1n, b) == True{} : Bool}) -> {Nat.is_lt(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+p:
      {==}

def lt0p(+pos: Nat, +h: {Nat.is_lt(0n, Nat.sub(pos, 1n)) == True{} : Bool}) -> {Nat.is_le(1n, pos) == True{} : Bool}:
  match pos:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+q:
      N.le_zero_l(q)

def max1_le2(+x: Nat, +y: Nat, +h: {Nat.is_le(x, 1n+y) == True{} : Bool}) -> {Nat.is_le(BN.max1(x), 1n+y) == True{} : Bool}:
  match x:
    case 0n:
      N.le_zero_l(y)
    case 1n+p:
      h

def sub_add_l(+x: Nat, +y: Nat) -> {Nat.sub(Nat.add(x, y), x) == y : Nat}:
  match x:
    case 0n:
      N.sub_zero(y)
    case 1n+p:
      sub_add_l(p, y)

def pl(+pos: Nat, +r: Nat, +m: Nat, +hp: {Nat.is_le(1n, pos) == True{} : Bool}, +h: {Nat.is_le(Nat.add(Nat.sub(pos, 1n), r), m) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(pos, r), 1n+m) == True{} : Bool}:
  match pos:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(0n, r), 1n+m) == True{} : Bool}, N.false_ne_true(hp))
    case 1n+q:
      AB.subst(Nat, z => {Nat.is_le(Nat.add(z, r), m) == True{} : Bool}, Nat.sub(q, 0n), q, N.sub_zero(q), h)

def ld0(+n: Nat) -> {Nat.is_le(Nat.add(n, 0n), n) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, n, Nat.add(n, 0n), Equal.sym(Nat, Nat.add(n, 0n), n, N.add_zero(n)), N.le_refl(n))

# What a verdict's picture pays (BD.VB on the verdict it stands for).
def PAY(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +v: MSX.VdP) -> Type:
  BD.VB(fa, l, back, PC.mkWin(fa, wp), MSX.mkVd(fa, wp, v))

# The first try's miss: H1 was false, the Ask Req.of covers it.
def pay_w1(+fa: List<&2, B.Contig>, +wp: PC.WP, +l: B.Line,
  +hg: {BN.lgate(l) == True{} : Bool},
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(0n, B.Line.body(l)), BN.lend(l)) == False{} : Bool}) ->
  PAY(fa, wp, 0n, l, MSX.VWP{Norm.slow.reqs(True{}, BN.lchrom(l), MSX.TA(0n, B.Line.body(l)), BN.lend(l)), 0n}):
  +c = BN.lchrom(l)
  +e = BN.lend(l)
  +P1 = BN.lp1(l)
  +A0 = MSX.TA(0n, B.Line.body(l))
  +RQ = Norm.Req.of(c, A0, e)
  +RW = BN.RW(l)
  +ZW = BN.ZW(fa)
  +Z2 = Nat.is_lt(0n, BN.lpos(l))
  +Y = Nat.add(BN.pick(True{}, ZW), BN.pick(Z2, ZW))
  +hnot = AB.subst(Nat, z => {BN.holdsW(PC.mkWin(fa, wp), c, z, e) == False{} : Bool}, A0, P1, N.sub_zero(P1), nh(fa, wp, c, A0, e, hh))
  +hcov = cov_reqof(c, A0, P1, e, X.sub_le(P1, 0n))
  +eo = remv(fa, False{}, 0n, wp, None{}, l, False{}, True{}, Z2, hg, hnot, {==}, {==})
  +en = remv(fa, False{}, 0n, wp, Some{RQ}, l, True{}, True{}, Z2, hg, hcov, {==}, {==})
  +RHSo = Nat.add(Nat.add(BN.pick(False{}, RW), BN.pick(Bool.not(False{}), RW)), Nat.add(BN.pick(True{}, ZW), BN.pick(Z2, ZW)))
  +RHSn = Nat.add(Nat.add(BN.pick(False{}, RW), BN.pick(Bool.not(True{}), RW)), Nat.add(BN.pick(True{}, ZW), BN.pick(Z2, ZW)))
  +elen = Equal.trans(Nat, Nat.sub(e, A0), Nat.sub(e, P1), BN.lref(l),
    Equal.cong(Nat, Nat, z => Nat.sub(e, z), A0, P1, N.sub_zero(P1)), sub_add_l(P1, BN.lref(l)))
  +hlen = AB.subst(Nat, z => {Nat.is_le(List.length(&2, Pr.Req, RQ), BG.max1(z)) == True{} : Bool}, Nat.sub(e, A0), BN.lref(l), elen, BG.reqof_len(c, A0, e))
  +hle = {%Equal.sym(Nat, BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), Some{RQ}, l), RHSn, en) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, RQ), _), BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool};
    %Equal.sym(Nat, BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l), RHSo, eo) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, RQ), RHSn), _) == True{} : Bool};
    N.le_add_mono_r(Y, 1n+List.length(&2, Pr.Req, RQ), RW, hlen) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, RQ), BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), Some{RQ}, l)), BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool}}
  (hle, {==})

# The grown miss (back was 0, the try's back b >= 1): [back = 0] pays.
def pay_w2(+fa: List<&2, B.Contig>, +wp: PC.WP, +l: B.Line, +b: Nat,
  +hg: {BN.lgate(l) == True{} : Bool},
  +hp1: {Nat.is_lt(0n, BN.lp1(l)) == True{} : Bool},
  +hfm: {Nat.is_le(BN.lend(l), BN.FM(fa)) == True{} : Bool},
  +hb1: {Nat.is_le(1n, b) == True{} : Bool},
  +hzf: {BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)) == True{} : Bool}) ->
  PAY(fa, wp, 0n, l, MSX.VWP{Norm.parts(BN.lchrom(l), 0n, BN.lend(l)), b}):
  +c = BN.lchrom(l)
  +e = BN.lend(l)
  +P1 = BN.lp1(l)
  +PR = Norm.parts(c, 0n, e)
  +RW = BN.RW(l)
  +ZW = BN.ZW(fa)
  +HW = BN.holdsW(PC.mkWin(fa, wp), c, P1, e)
  +Zb = BN.pick(Nat.is_lt(b, BN.lpos(l)), ZW)
  +RWt = BN.pick(Bool.not(HW), RW)
  +hcov = cov_parts(c, 0n, P1, e, e, N.le_zero_l(P1), N.le_refl(e))
  +hpos = lt0(BN.lpos(l), lt0p(BN.lpos(l), hp1))
  +en = remv(fa, False{}, b, wp, Some{PR}, l, True{}, False{}, Nat.is_lt(b, BN.lpos(l)), hg, hcov, ne0(b, hb1), {==})
  +eo = remv(fa, False{}, 0n, wp, None{}, l, HW, True{}, True{}, hg, {==}, {==}, hpos)
  +RHSn = Nat.add(Nat.add(BN.pick(False{}, RW), BN.pick(Bool.not(True{}), RW)), Nat.add(BN.pick(False{}, ZW), Zb))
  +RHSo = Nat.add(Nat.add(BN.pick(False{}, RW), RWt), Nat.add(BN.pick(True{}, ZW), BN.pick(True{}, ZW)))
  +hlen0 = AB.subst(Nat, z => {Nat.is_le(List.length(&2, Pr.Req, PR), BG.max1(z)) == True{} : Bool}, Nat.sub(e, 0n), e, N.sub_zero(e), BG.parts_len(c, 0n, e))
  +hlen = N.le_trans(List.length(&2, Pr.Req, PR), BN.max1(e), 1n+BN.FM(fa), hlen0,
    max1_le2(e, BN.FM(fa), N.le_trans(e, BN.FM(fa), 1n+BN.FM(fa), hfm, N.le_add_l(BN.FM(fa), 1n))))
  +hle = {%Equal.sym(Nat, BN.rem(fa, False{}, b, PC.mkWin(fa, wp), Some{PR}, l), RHSn, en) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, PR), _), BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool};
    %Equal.sym(Nat, BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l), RHSo, eo) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, PR), RHSn), _) == True{} : Bool};
    N.le_trans(Nat.add(1n+List.length(&2, Pr.Req, PR), Zb), Nat.add(ZW, ZW), Nat.add(RWt, Nat.add(ZW, ZW)),
      am(1n+List.length(&2, Pr.Req, PR), ZW, Zb, ZW, hlen, pk(Nat.is_lt(b, BN.lpos(l)), ZW)), N.le_add_l(Nat.add(ZW, ZW), RWt)) :
      {Nat.is_le(Nat.add(1n+List.length(&2, Pr.Req, PR), BN.rem(fa, False{}, b, PC.mkWin(fa, wp), Some{PR}, l)), BN.rem(fa, False{}, 0n, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool}}
  (hle, W.or_r(Nat.is_eq(b, 0n), BN.heldZ(PC.mkWin(fa, wp), Some{PR}, c, e),
    W.and_tt(BN.zfit(PC.mkWin(fa, wp), c, e), BN.coversA(Some{PR}, c, 0n, e), hzf, cov_parts(c, 0n, 0n, e, e, {==}, N.le_refl(e)))))

# Out of tries (back := POS): [back < POS] pays.
def pay_w3(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +b: Nat,
  +hg: {BN.lgate(l) == True{} : Bool},
  +hlt: {Nat.is_lt(back, BN.lp1(l)) == True{} : Bool},
  +hfm: {Nat.is_le(BN.lend(l), BN.FM(fa)) == True{} : Bool},
  +hzf: {BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)) == True{} : Bool}) ->
  PAY(fa, wp, back, l, MSX.vxP(B.Line.body(l), MSX.XA{b})):
  +c = BN.lchrom(l)
  +e = BN.lend(l)
  +P1 = BN.lp1(l)
  +pos = BN.lpos(l)
  +E3 = Nat.add(pos, BN.lref(l))
  +PR = Norm.parts(c, 0n, E3)
  +RW = BN.RW(l)
  +ZW = BN.ZW(fa)
  +HW = BN.holdsW(PC.mkWin(fa, wp), c, P1, e)
  +Zz = BN.pick(Nat.is_eq(back, 0n), ZW)
  +RWt = BN.pick(Bool.not(HW), RW)
  +hp0 = N.le_lt_trans(0n, back, P1, N.le_zero_l(back), hlt)
  +hp1 = lt0p(pos, hp0)
  +he3 = N.le_add_mono_r(BN.lref(l), P1, pos, X.sub_le(pos, 1n))
  +hcov = cov_parts(c, 0n, P1, E3, e, N.le_zero_l(P1), he3)
  +hltp = N.lt_le_trans(back, P1, pos, hlt, X.sub_le(pos, 1n))
  +en = remv(fa, False{}, pos, wp, Some{PR}, l, True{}, False{}, False{}, hg, hcov, ne0(pos, hp1), N.lt_irrefl(pos))
  +eo = remv(fa, False{}, back, wp, None{}, l, HW, Nat.is_eq(back, 0n), True{}, hg, {==}, {==}, hltp)
  +RHSn = Nat.add(Nat.add(BN.pick(False{}, RW), BN.pick(Bool.not(True{}), RW)), Nat.add(BN.pick(False{}, ZW), BN.pick(False{}, ZW)))
  +RHSo = Nat.add(Nat.add(BN.pick(False{}, RW), RWt), Nat.add(Zz, BN.pick(True{}, ZW)))
  +L3 = List.length(&2, Pr.Req, PR)
  +hlen0 = AB.subst(Nat, z => {Nat.is_le(L3, BG.max1(z)) == True{} : Bool}, Nat.sub(E3, 0n), E3, N.sub_zero(E3), BG.parts_len(c, 0n, E3))
  +hlen = N.le_trans(L3, BN.max1(E3), 1n+BN.FM(fa), hlen0, max1_le2(E3, BN.FM(fa), pl(pos, BN.lref(l), BN.FM(fa), hp1, hfm)))
  +hle = {%Equal.sym(Nat, BN.rem(fa, False{}, pos, PC.mkWin(fa, wp), Some{PR}, l), RHSn, en) :
      {Nat.is_le(Nat.add(1n+L3, _), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool};
    %Equal.sym(Nat, BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, l), RHSo, eo) :
      {Nat.is_le(Nat.add(1n+L3, RHSn), _) == True{} : Bool};
    N.le_trans(Nat.add(1n+L3, 0n), 1n+L3, Nat.add(RWt, Nat.add(Zz, ZW)), ld0(1n+L3),
      N.le_trans(1n+L3, Nat.add(Zz, ZW), Nat.add(RWt, Nat.add(Zz, ZW)),
        N.le_trans(1n+L3, ZW, Nat.add(Zz, ZW), hlen, N.le_add_l(ZW, Zz)), N.le_add_l(Nat.add(Zz, ZW), RWt))) :
      {Nat.is_le(Nat.add(1n+L3, BN.rem(fa, False{}, pos, PC.mkWin(fa, wp), Some{PR}, l)), BN.rem(fa, False{}, back, PC.mkWin(fa, wp), None{}, l)) == True{} : Bool}}
  (hle, W.or_r(Nat.is_eq(pos, 0n), BN.heldZ(PC.mkWin(fa, wp), Some{PR}, c, e),
    W.and_tt(BN.zfit(PC.mkWin(fa, wp), c, e), BN.coversA(Some{PR}, c, 0n, e), hzf, cov_parts(c, 0n, 0n, E3, e, {==}, he3))))

# A decided try: a result, no Want.
def xd_pay(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +f: J.Fast, +b: Nat, +hf: {BW.isON(f) == False{} : Bool}) ->
  PAY(fa, wp, back, l, MSX.vxP(B.Line.body(l), MSX.XD{f, b})):
  match f:
    case J.Same{}:
      Unit{}
    case J.Other{None{}}:
      Empty.absurd(PAY(fa, wp, back, l, MSX.vxP(B.Line.body(l), MSX.XD{J.Other{None{}}, b})), N.false_ne_true(Equal.sym(Bool, True{}, False{}, hf)))
    case J.Other{Some{r}}:
      Unit{}

# What the tries keep: a try to come (XA) after "too small", a decided try,
# or a miss that pays.
def INVX(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +x: MSX.SxP) -> Type:
  match x:
    case MSX.XA{+b}:
      {Nat.is_le(back, b) == True{} : Bool} & ({Nat.is_lt(back, BN.lp1(l)) == True{} : Bool} & ({Nat.is_le(BN.lend(l), BN.FM(fa)) == True{} : Bool} & ({Nat.is_le(1n, b) == True{} : Bool} & {BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)) == True{} : Bool})))
    case MSX.XD{+f, b}:
      {BW.isON(f) == False{} : Bool}
    case MSX.XM{+reqs, +b}:
      PAY(fa, wp, back, l, MSX.VWP{reqs, b})

def gr_b(+cnd: Bool, +b: Nat, +pos: Nat, +back: Nat, +hbb: {Nat.is_le(back, b) == True{} : Bool}, +hbp: {Nat.is_le(back, pos) == True{} : Bool}) ->
  {Nat.is_le(back, Bool.pick(Nat, cnd, pos, Nat.add(Nat.mul(b, 2n), 1n))) == True{} : Bool}:
  match cnd:
    case True{}:
      hbp
    case False{}:
      N.le_trans(back, b, Nat.add(Nat.mul(b, 2n), 1n), hbb, le_gr(b))

def gr_1(+cnd: Bool, +b: Nat, +pos: Nat, +h1: {Nat.is_le(1n, pos) == True{} : Bool}) ->
  {Nat.is_le(1n, Bool.pick(Nat, cnd, pos, Nat.add(Nat.mul(b, 2n), 1n))) == True{} : Bool}:
  match cnd:
    case True{}:
      h1
    case False{}:
      N.le_add_l(1n, Nat.mul(b, 2n))

# A try the window holds: decided, or "too small" (then b < POS - 1 and REF
# fits, and the next back grows).
def held_t.k(+F: J.Fast, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +b: Nat,
  +hbb: {Nat.is_le(back, b) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)) == True{} : Bool},
  +hF: {J.fast(Some{PC.jtruth(fa, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l))}, BN.lfs(l), B.Line.body(l)) == F : J.Fast}) ->
  INVX(fa, wp, back, l, MSX.fP(b, PC.wp.clen(fa, BN.lchrom(l)), BN.lpos(l), F)):
  match F:
    case J.Same{}:
      {==}
    case J.Other{Some{r}}:
      {==}
    case J.Other{None{}}:
      +BDY = B.Line.body(l)
      +pos = BN.lpos(l)
      +P1 = BN.lp1(l)
      +CL = PC.wp.clen(fa, BN.lchrom(l))
      +cnd = Bool.and(Nat.is_le(CL, b), Bool.not(Nat.is_eq(CL, 0n)))
      +hlt = blt(fa, BDY, b, hF)
      +hfm = efm(fa, BDY, MSX.TA(b, BDY), hF)
      +hl2 = N.le_lt_trans(back, b, P1, hbb, hlt)
      +hp1 = lt0p(pos, N.le_lt_trans(0n, back, P1, N.le_zero_l(back), hl2))
      +hbp = N.lt_to_le(back, pos, N.lt_le_trans(back, P1, pos, hl2, X.sub_le(pos, 1n)))
      (gr_b(cnd, b, pos, back, hbb, hbp), (hl2, (hfm, (gr_1(cnd, b, pos, hp1), zfi(fa, wp, BDY, MSX.TA(b, BDY), hwp, hh, hF)))))

def held_t(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +b: Nat, +hbb: {Nat.is_le(back, b) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)) == True{} : Bool}) ->
  INVX(fa, wp, back, l, MSX.fP(b, PC.wp.clen(fa, BN.lchrom(l)), BN.lpos(l), J.fast(Some{PC.jtruth(fa, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l))}, BN.lfs(l), B.Line.body(l)))):
  held_t.k(J.fast(Some{PC.jtruth(fa, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l))}, BN.lfs(l), B.Line.body(l)), fa, wp, back, l, b, hbb, hwp, hh, {==})

# Once back >= 1, bi's zero window holds every try.
def zh(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +a: Nat,
  +hz: {Nat.is_eq(back, 0n) == False{} : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool}) ->
  {PC.holds(fa, wp, BN.lchrom(l), a, BN.lend(l)) == True{} : Bool}:
  +h0 = AB.subst(Bool, k => {Bool.or(k, BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool}, Nat.is_eq(back, 0n), False{}, hz, hbi)
  hmono(fa, wp, BN.lchrom(l), 0n, a, BN.lend(l), BW.hold_of(fa, wp, BN.lchrom(l), 0n, BN.lend(l), h0), N.le_zero_l(a))

def mf.k(+z: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line,
  +hz: {Nat.is_eq(back, 0n) == z : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hg: {BN.lgate(l) == True{} : Bool},
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l)) == False{} : Bool}) ->
  PAY(fa, wp, back, l, MSX.VWP{Norm.slow.reqs(z, BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l)), back}):
  match z:
    case True{}:
      +eb = N.eq_sound(back, 0n, hz)
      +hh0 = AB.subst(Nat, k => {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(k, B.Line.body(l)), BN.lend(l)) == False{} : Bool}, back, 0n, eb, hh)
      AB.subst(Nat, k => PAY(fa, wp, k, l, MSX.VWP{Norm.slow.reqs(True{}, BN.lchrom(l), MSX.TA(k, B.Line.body(l)), BN.lend(l)), k}), 0n, back,
        Equal.sym(Nat, back, 0n, eb), pay_w1(fa, wp, l, hg, hh0))
    case False{}:
      +A = MSX.TA(back, B.Line.body(l))
      Empty.absurd(PAY(fa, wp, back, l, MSX.VWP{Norm.slow.reqs(False{}, BN.lchrom(l), A, BN.lend(l)), back}),
        N.false_ne_true(Equal.trans(Bool, False{}, PC.holds(fa, wp, BN.lchrom(l), A, BN.lend(l)), True{},
          Equal.sym(Bool, PC.holds(fa, wp, BN.lchrom(l), A, BN.lend(l)), False{}, hh), zh(fa, wp, back, l, A, hz, hbi))))

def ml.k(+z: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +b: Nat,
  +hz: {Nat.is_eq(back, 0n) == z : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hg: {BN.lgate(l) == True{} : Bool},
  +hlt: {Nat.is_lt(back, BN.lp1(l)) == True{} : Bool},
  +hfm: {Nat.is_le(BN.lend(l), BN.FM(fa)) == True{} : Bool},
  +hb1: {Nat.is_le(1n, b) == True{} : Bool},
  +hzf: {BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)) == True{} : Bool},
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)) == False{} : Bool}) ->
  PAY(fa, wp, back, l, MSX.VWP{Norm.slow.reqs(Nat.is_eq(b, 0n), BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)), b}):
  match z:
    case True{}:
      +eb = N.eq_sound(back, 0n, hz)
      +hp1 = AB.subst(Nat, k => {Nat.is_lt(k, BN.lp1(l)) == True{} : Bool}, back, 0n, eb, hlt)
      p2 = AB.subst(Bool, k => PAY(fa, wp, 0n, l, MSX.VWP{Norm.slow.reqs(k, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)), b}), False{}, Nat.is_eq(b, 0n),
        Equal.sym(Bool, Nat.is_eq(b, 0n), False{}, ne0(b, hb1)), pay_w2(fa, wp, l, b, hg, hp1, hfm, hb1, hzf))
      AB.subst(Nat, k => PAY(fa, wp, k, l, MSX.VWP{Norm.slow.reqs(Nat.is_eq(b, 0n), BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)), b}), 0n, back,
        Equal.sym(Nat, back, 0n, eb), p2)
    case False{}:
      +A = MSX.TA(b, B.Line.body(l))
      Empty.absurd(PAY(fa, wp, back, l, MSX.VWP{Norm.slow.reqs(Nat.is_eq(b, 0n), BN.lchrom(l), A, BN.lend(l)), b}),
        N.false_ne_true(Equal.trans(Bool, False{}, PC.holds(fa, wp, BN.lchrom(l), A, BN.lend(l)), True{},
          Equal.sym(Bool, PC.holds(fa, wp, BN.lchrom(l), A, BN.lend(l)), False{}, hh), zh(fa, wp, back, l, A, hz, hbi))))

def tf.k(+h: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line,
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l)) == h : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hg: {BN.lgate(l) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool}) ->
  INVX(fa, wp, back, l, Bool.pick(MSX.SxP, h,
    MSX.fP(back, PC.wp.clen(fa, BN.lchrom(l)), BN.lpos(l), J.fast(Some{PC.jtruth(fa, BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l))}, BN.lfs(l), B.Line.body(l))),
    MSX.XM{Norm.slow.reqs(Nat.is_eq(back, 0n), BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l)), back})):
  match h:
    case True{}:
      held_t(fa, wp, back, l, back, N.le_refl(back), hwp, hh)
    case False{}:
      mf.k(Nat.is_eq(back, 0n), fa, wp, back, l, {==}, hbi, hg, hh)

def tl.k(+h: Bool, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line, +b: Nat,
  +hh: {PC.holds(fa, wp, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)) == h : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hg: {BN.lgate(l) == True{} : Bool},
  +hbb: {Nat.is_le(back, b) == True{} : Bool},
  +hlt: {Nat.is_lt(back, BN.lp1(l)) == True{} : Bool},
  +hfm: {Nat.is_le(BN.lend(l), BN.FM(fa)) == True{} : Bool},
  +hb1: {Nat.is_le(1n, b) == True{} : Bool},
  +hzf: {BN.zfit(PC.mkWin(fa, wp), BN.lchrom(l), BN.lend(l)) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool}) ->
  INVX(fa, wp, back, l, Bool.pick(MSX.SxP, h,
    MSX.fP(b, PC.wp.clen(fa, BN.lchrom(l)), BN.lpos(l), J.fast(Some{PC.jtruth(fa, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l))}, BN.lfs(l), B.Line.body(l))),
    MSX.XM{Norm.slow.reqs(Nat.is_eq(b, 0n), BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)), b})):
  match h:
    case True{}:
      held_t(fa, wp, back, l, b, hbb, hwp, hh)
    case False{}:
      ml.k(Nat.is_eq(back, 0n), fa, wp, back, l, b, {==}, hbi, hg, hlt, hfm, hb1, hzf, hh)

# The tries, by fuel.
def sg_pay(+fuel: Nat, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line,
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hg: {BN.lgate(l) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +x: MSX.SxP, hx: INVX(fa, wp, back, l, x)) ->
  PAY(fa, wp, back, l, MSX.vxP(B.Line.body(l), MSX.sgP(fuel, fa, wp, B.Line.body(l), x))):
  match fuel x:
    case 0n MSX.XA{+b}:
      (h1, r1) = hx
      (h2, r2) = r1
      (h3, r3) = r2
      (h4, h5) = r3
      pay_w3(fa, wp, back, l, b, hg, h2, h3, h5)
    case 0n MSX.XD{+f, +b}:
      xd_pay(fa, wp, back, l, f, b, hx)
    case 0n MSX.XM{+reqs, +b}:
      hx
    case 1n+k MSX.XA{+b}:
      (h1, r1) = hx
      (h2, r2) = r1
      (h3, r3) = r2
      (h4, h5) = r3
      sg_pay(k, fa, wp, back, l, hbi, hg, hwp, MSX.tryP(fa, wp, b, B.Line.body(l)),
        tl.k(PC.holds(fa, wp, BN.lchrom(l), MSX.TA(b, B.Line.body(l)), BN.lend(l)), fa, wp, back, l, b, {==}, hbi, hg, h1, h2, h3, h4, h5, hwp))
    case 1n+k MSX.XD{+f, +b}:
      xd_pay(fa, wp, back, l, f, b, hx)
    case 1n+k MSX.XM{+reqs, +b}:
      hx

def vb.m(+m: Maybe<&2, B.Res>, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool},
  +hm: {J.judge_fs(None{}, BN.lfs(l), B.Line.body(l)) == m : Maybe<&2, B.Res>}) ->
  BD.VB(fa, l, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l))):
  match m:
    case Some{+r}:
      AB.subst(Norm.Vd, z => BD.VB(fa, l, back, PC.mkWin(fa, wp), z), MSX.mkVd(fa, wp, MSX.VRP{r}), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l)),
        Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l)), MSX.mkVd(fa, wp, MSX.VRP{r}), MSX.vd_some_eq(r, fa, wp, back, B.Line.body(l), hm)), Unit{})
    case None{}:
      +x1 = MSX.sgP(64n, fa, wp, B.Line.body(l), MSX.XA{back})
      AB.subst(Norm.Vd, z => BD.VB(fa, l, back, PC.mkWin(fa, wp), z), MSX.mkVd(fa, wp, MSX.vxP(B.Line.body(l), x1)), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l)),
        Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l)), MSX.mkVd(fa, wp, MSX.vxP(B.Line.body(l), x1)), MSX.vd_none_eq(fa, wp, back, B.Line.body(l), hb, hwp, hm)),
        sg_pay(63n, fa, wp, back, l, hbi, gate(l, hm), hwp, MSX.tryP(fa, wp, back, B.Line.body(l)),
          tf.k(PC.holds(fa, wp, BN.lchrom(l), MSX.TA(back, B.Line.body(l)), BN.lend(l)), fa, wp, back, l, {==}, hbi, gate(l, hm), hwp)))

# The slow path's verdict and the budget (both modes; notes/bytes_proofs_budget.md).
def vd_bud(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +l: B.Line,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hbi: {Bool.or(Nat.is_eq(back, 0n), BN.holdsW(PC.mkWin(fa, wp), BN.lchrom(l), 0n, BN.lend(l))) == True{} : Bool}) ->
  BD.VB(fa, l, back, PC.mkWin(fa, wp), Norm.verdict(back, PC.mkWin(fa, wp), BN.lfs(l), B.Line.body(l))):
  vb.m(J.judge_fs(None{}, BN.lfs(l), B.Line.body(l)), fa, wp, back, l, hb, hwp, hbi, {==})
