import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_cache.bend as K
import ./proof_b_cache_lem.bend as X
import ./proof_window_defs.bend as WS
import ./proof_window_lists.bend as WL
import ./proof_window.bend as PW
import ./proof_fast.bend as PF
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB
import ./proof_b_lines_str.bend as LS
import ./proof_b_frame.bend as FR
import ./proof_b_frame_fr.bend as FF
import ./proof_b_adv_ms.bend as MS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_str.bend as AS
import ./proof_machine_nat.bend as PN
import ./proof_base.bend as PB
import ./proof_b_run_inv.bend as RI
import ./proof_b_adv_wr.bend as WR
import ./proof_b_judge_bytes.bend as JB
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./proof_b_lines.bend as LN
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_part.bend as DPT
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-bytes/proof_list.bend as BL
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_u32.bend as U

# The String mode's line holes of adv_ok (proof_b_adv.bend: adv.ms.sb,
# adv.ms.sl), and the verdict lemma they share with the byte mode's slow path
# (vd_ok): a body line's verdict from a pictured window is the spec's judge,
# or reads that keep the contract.

# ---------------------------------------------------------------------------
# Reads that keep the contract
# ---------------------------------------------------------------------------

def RQOK(+reqs: List<&2, Pr.Req>) -> Type:
  {E.reqs_ok(reqs) == True{} : Bool}
  & ({reqs == S.rq(reqs) : List<&2, Pr.Req>}
  & {Nat.is_le(1n, List.length(&2, Pr.Req, reqs)) == True{} : Bool})

# A list of reads from a on contig c that ends at e is rq's window.
def rq_of(+rs: List<&2, Pr.Req>, +c: String, +a: Nat, +e: Nat,
  +h1: {X.hd1(rs, c, a) == True{} : Bool},
  +hl: {Norm.last_b(rs, 0n) == e : Nat}) ->
  {S.rq(rs) == Norm.parts(c, a, e) : List<&2, Pr.Req>}:
  match rs:
    case Nil{}:
      Empty.absurd({S.rq(Nil{}) == Norm.parts(c, a, e) : List<&2, Pr.Req>}, N.false_ne_true(h1))
    case Con{Pr.Req{c1, a1, b1}, t}:
      +ec = WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      +ea = N.eq_sound(a1, a, N.and_true_r(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      %ec : {Norm.parts(c1, a1, Norm.last_b(t, b1)) == Norm.parts(_, a, e) : List<&2, Pr.Req>}
      %ea : {Norm.parts(c1, a1, Norm.last_b(t, b1)) == Norm.parts(c1, _, e) : List<&2, Pr.Req>}
      %hl : {Norm.parts(c1, a1, Norm.last_b(t, b1)) == Norm.parts(c1, a1, _) : List<&2, Pr.Req>}
      {==}

def parts_rq.k(+c: String, +a: Nat, +e: Nat,
  h: {E.reqs_ok(Norm.parts(c, a, e)) == True{} : Bool}
  & ({Nat.is_le(1n, List.length(&2, Pr.Req, Norm.parts(c, a, e))) == True{} : Bool}
  & {Nat.is_le(List.length(&2, Pr.Req, Norm.parts(c, a, e)), Nat.max(1n, Nat.sub(e, a))) == True{} : Bool})) ->
  RQOK(Norm.parts(c, a, e)):
  (h1, h23) = h
  (h2, h3) = h23
  +x = Nat.sub(e, a)
  (h1, (Equal.sym(List<&2, Pr.Req>, S.rq(Norm.parts(c, a, e)), Norm.parts(c, a, e),
      rq_of(Norm.parts(c, a, e), c, a, e, X.ph(x, Norm.le31(x), c, a, e), X.plast(x, Norm.le31(x), c, a, e, 0n))), h2))

# The reads of a window (Norm.parts) keep the contract.
def parts_rq(+c: String, +a: Nat, +e: Nat) -> RQOK(Norm.parts(c, a, e)):
  parts_rq.k(c, a, e, K.parts_ok(c, a, e))

def rqof.ok(+c: String, +a2: Nat, +e2: Nat, +ho: {Norm.le31(Nat.sub(e2, a2)) == True{} : Bool}) ->
  {E.reqs_ok([Pr.Req{c, a2, e2}]) == True{} : Bool}:
  %Equal.sym(Bool, Norm.le31(Nat.sub(e2, a2)), True{}, ho) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def rqof.rq(+c: String, +a2: Nat, +e2: Nat, +ho: {Norm.le31(Nat.sub(e2, a2)) == True{} : Bool}) ->
  {[Pr.Req{c, a2, e2}] == S.rq([Pr.Req{c, a2, e2}]) : List<&2, Pr.Req>}:
  %Equal.sym(Bool, Norm.le31(Nat.sub(e2, a2)), True{}, ho) : {[Pr.Req{c, a2, e2}] == Norm.parts.go(Nat.sub(e2, a2), _, c, a2, e2) : List<&2, Pr.Req>}
  Equal.sym(List<&2, Pr.Req>, Norm.parts.go(Nat.sub(e2, a2), True{}, c, a2, e2), [Pr.Req{c, a2, e2}], X.pp_true(Nat.sub(e2, a2), c, a2, e2))

def rqof.k(+one: Bool, +c: String, +a: Nat, +e: Nat, +a2: Nat, +e2: Nat,
  +ho: {Norm.le31(Nat.sub(e2, a2)) == one : Bool}) ->
  RQOK(Norm.Req.of.k(one, c, a, e, a2, e2)):
  match one:
    case True{}:
      (rqof.ok(c, a2, e2, ho), (rqof.rq(c, a2, e2, ho), {==}))
    case False{}:
      parts_rq(c, a, e)

# The reads the slow path asks keep the contract.
def reqof_rq(+c: String, +a: Nat, +e: Nat) -> RQOK(Norm.Req.of(c, a, e)):
  +a2 = Nat.sub(a, Norm.margin())
  +e2 = Nat.max(e, Nat.add(a, Norm.ahead()))
  rqof.k(Norm.le31(Nat.sub(e2, a2)), c, a, e, a2, e2, {==})

def slreqs_rq(+first: Bool, +c: String, +a: Nat, +e: Nat) -> RQOK(Norm.slow.reqs(first, c, a, e)):
  match first:
    case True{}:
      reqof_rq(c, a, e)
    case False{}:
      parts_rq(c, 0n, e)

# The first read's contig.
def fst_c(+rs: List<&2, Pr.Req>) -> Maybe<&2, String>:
  match rs:
    case Nil{}:
      None{}
    case Con{Pr.Req{+c, a, b}, t}:
      Some{c}

def fc_hd1(+rs: List<&2, Pr.Req>, +c: String, +a: Nat, +h1: {X.hd1(rs, c, a) == True{} : Bool}) ->
  {fst_c(rs) == Some{c} : Maybe<&2, String>}:
  match rs:
    case Nil{}:
      Empty.absurd({fst_c(Nil{}) == Some{c} : Maybe<&2, String>}, N.false_ne_true(h1))
    case Con{Pr.Req{c1, a1, b1}, t}:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, c1, c, WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), h1)))

# The reads of a window, and those the slow path asks, are on its contig.
def parts_c(+c: String, +a: Nat, +e: Nat) -> {fst_c(Norm.parts(c, a, e)) == Some{c} : Maybe<&2, String>}:
  +x = Nat.sub(e, a)
  fc_hd1(Norm.parts(c, a, e), c, a, X.ph(x, Norm.le31(x), c, a, e))

def rqofc.k(+one: Bool, +c: String, +a: Nat, +e: Nat, +a2: Nat, +e2: Nat) ->
  {fst_c(Norm.Req.of.k(one, c, a, e, a2, e2)) == Some{c} : Maybe<&2, String>}:
  match one:
    case True{}:
      {==}
    case False{}:
      parts_c(c, a, e)

def slreqs_c(+first: Bool, +c: String, +a: Nat, +e: Nat) -> {fst_c(Norm.slow.reqs(first, c, a, e)) == Some{c} : Maybe<&2, String>}:
  match first:
    case True{}:
      rqofc.k(Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))), c, a, e, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead())))
    case False{}:
      parts_c(c, 0n, e)

# ---------------------------------------------------------------------------
# The slow path's tries, pictured
# ---------------------------------------------------------------------------

type SxP is Data:
  XA{b: Nat}
  XD{f: J.Fast, b: Nat}
  XM{reqs: List<&2, Pr.Req>, b: Nat}

def mkSx(+fa: List<&2, B.Contig>, +wp: CD.WP, +x: SxP) -> Norm.Sx:
  match x:
    case XA{b}:
      Norm.SAgain{CD.mkWin(fa, wp), b}
    case XD{f, b}:
      Norm.SDone{CD.mkWin(fa, wp), f, b}
    case XM{reqs, b}:
      Norm.SMiss{CD.mkWin(fa, wp), reqs, b}

# What a try's outcome says: nothing (try again), the spec's judge
# (decided), or reads that keep the contract.
def xOK(+fa: List<&2, B.Contig>, +body: String, +x: SxP) -> Type:
  match x:
    case XA{b}:
      {True{} == True{} : Bool}
    case XD{+f, b}:
      {PF.fr_res(f, B.Rec.pos(B.Rec.fields(body)), body) == Some{L.judge(fa, body)} : Maybe<&2, B.Res>}
    case XM{+reqs, b}:
      RQOK(reqs) & {fst_c(reqs) == Some{B.Rec.field(J.pfs(body), 0n)} : Maybe<&2, String>}

def fP(+back: Nat, +clen: Nat, +pos: Nat, +f: J.Fast) -> SxP:
  match f:
    case J.Other{None{}}:
      XA{Norm.grow(clen, back, pos)}
    case f:
      XD{f, back}

# One try, pictured (slow.try with serve_ok's answer).
def FS(+body: String) -> List<&2, String>:
  J.pfs(body)

def TC(+body: String) -> String:
  B.Rec.field(J.pfs(body), 0n)

def TA(+back: Nat, +body: String) -> Nat:
  Nat.sub(Nat.sub(B.Rec.pos(J.pfs(body)), 1n), back)

def TE(+body: String) -> Nat:
  Nat.add(Nat.sub(B.Rec.pos(J.pfs(body)), 1n), String.length(B.Rec.field(J.pfs(body), 3n)))

def tryP(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String) -> SxP:
  Bool.pick(SxP, CD.holds(fa, wp, TC(body), TA(back, body), TE(body)),
    fP(back, CD.wp.clen(fa, TC(body)), B.Rec.pos(J.pfs(body)), J.fast(Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, J.pfs(body), body)),
    XM{Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), back})

def fP_eq(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +clen: Nat, +pos: Nat, +f: J.Fast) ->
  {Norm.slow.f(back, clen, pos, CD.mkWin(fa, wp), f) == mkSx(fa, wp, fP(back, clen, pos, f)) : Norm.Sx}:
  match f:
    case J.Same{}:
      {==}
    case J.Other{None{}}:
      {==}
    case J.Other{Some{r}}:
      {==}

def try_eq.k(+h: Bool, +fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String) ->
  {Norm.slow.sv(back, Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), J.pfs(body), body,
     Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, h, Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, None{}), Bool.pick(Nat, h, CD.wp.clen(fa, TC(body)), 0n)})
   == mkSx(fa, wp, Bool.pick(SxP, h, fP(back, CD.wp.clen(fa, TC(body)), B.Rec.pos(J.pfs(body)), J.fast(Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, J.pfs(body), body)), XM{Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), back})) : Norm.Sx}:
  match h:
    case True{}:
      fP_eq(fa, wp, back, CD.wp.clen(fa, TC(body)), B.Rec.pos(J.pfs(body)), J.fast(Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, J.pfs(body), body))
    case False{}:
      {==}

def try_eq.h(+h: Bool, +fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hh: {CD.holds(fa, wp, TC(body), TA(back, body), TE(body)) == h : Bool}) ->
  {Norm.slow.sv(back, Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), J.pfs(body), body,
     Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, wp, TC(body), TA(back, body), TE(body)), Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, None{}), Bool.pick(Nat, CD.holds(fa, wp, TC(body), TA(back, body), TE(body)), CD.wp.clen(fa, TC(body)), 0n)})
   == mkSx(fa, wp, tryP(fa, wp, back, body)) : Norm.Sx}:
  +REQS = Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body))
  +JT = CD.jtruth(fa, TC(body), TA(back, body), TE(body))
  +CL = CD.wp.clen(fa, TC(body))
  +F = J.fast(Some{JT}, J.pfs(body), body)
  %Equal.sym(Bool, CD.holds(fa, wp, TC(body), TA(back, body), TE(body)), h, hh) :
    {Norm.slow.sv(back, REQS, J.pfs(body), body, Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, _, Some{JT}, None{}), Bool.pick(Nat, _, CL, 0n)})
      == mkSx(fa, wp, Bool.pick(SxP, _, fP(back, CL, B.Rec.pos(J.pfs(body)), F), XM{REQS, back})) : Norm.Sx}
  try_eq.k(h, fa, wp, back, body)

# One try on a pictured window is its picture.
def try_eq(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  {Norm.slow.try(CD.mkWin(fa, wp), back, J.pfs(body), body) == mkSx(fa, wp, tryP(fa, wp, back, body)) : Norm.Sx}:
  +c = TC(body)
  +a = TA(back, body)
  +e = TE(body)
  %Equal.sym(Norm.Sv, Norm.serve(CD.mkWin(fa, wp), c, a, e), Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, wp, c, a, e), Some{CD.jtruth(fa, c, a, e)}, None{}), Bool.pick(Nat, CD.holds(fa, wp, c, a, e), CD.wp.clen(fa, c), 0n)},
    K.serve_ok(fa, wp, c, a, e, hb, hv)) :
    {Norm.slow.sv(back, Norm.slow.reqs(Nat.is_eq(back, 0n), c, a, e), J.pfs(body), body, _) == mkSx(fa, wp, tryP(fa, wp, back, body)) : Norm.Sx}
  try_eq.h(CD.holds(fa, wp, c, a, e), fa, wp, back, body, {==})

def jres_inj(+x: B.Res, +y: B.Res, e: {Some{x} == Some{y} : Maybe<&2, B.Res>}) -> {x == y : B.Res}:
  Equal.cong(Maybe<&2, B.Res>, B.Res, m => Maybe.default(&2, B.Res, m, x), Some{x}, Some{y}, e)

# A decided answer from J.fast is the spec's judge (J.fast says what judge_in
# gives, and a truthful answer's judge_in is the judge).
def fp_ok(+f: J.Fast, +fa: List<&2, B.Contig>, +body: String, +back: Nat, +clen: Nat, +pos: Nat, +jt: J.Ans,
  +e1: {PF.fr_res(f, B.Rec.pos(B.Rec.fields(body)), body) == J.judge_in(Some{jt}, body) : Maybe<&2, B.Res>},
  +ht: {WS.truthful(fa, WS.chrom_of(body), Some{jt}) == True{} : Bool}) ->
  xOK(fa, body, fP(back, clen, pos, f)):
  match f:
    case J.Same{}:
      +r0 = {B.Res{B.Normalized{}, B.Rec.pos(B.Rec.fields(body)), body, False{}} : B.Res}
      Equal.cong(B.Res, Maybe<&2, B.Res>, z => Some{z}, r0, L.judge(fa, body),
        PW.window(fa, body, Some{jt}, r0, ht, Equal.sym(Maybe<&2, B.Res>, Some{r0}, J.judge_in(Some{jt}, body), e1)))
    case J.Other{None{}}:
      {==}
    case J.Other{Some{r}}:
      Equal.cong(B.Res, Maybe<&2, B.Res>, z => Some{z}, r, L.judge(fa, body),
        PW.window(fa, body, Some{jt}, r, ht, Equal.sym(Maybe<&2, B.Res>, Some{r}, J.judge_in(Some{jt}, body), e1)))

def try_ok.k(+h: Bool, +fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String) ->
  xOK(fa, body, Bool.pick(SxP, h, fP(back, CD.wp.clen(fa, TC(body)), B.Rec.pos(J.pfs(body)), J.fast(Some{CD.jtruth(fa, TC(body), TA(back, body), TE(body))}, J.pfs(body), body)), XM{Norm.slow.reqs(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), back})):
  match h:
    case True{}:
      +JT = CD.jtruth(fa, TC(body), TA(back, body), TE(body))
      +ht = AB.subst(String, z => {WS.truthful(fa, z, Some{JT}) == True{} : Bool}, TC(body), WS.chrom_of(body), PF.pfs_field(body, 0n, {==}),
        K.jtruth_ok(fa, TC(body), TA(back, body), TE(body)))
      fp_ok(J.fast(Some{JT}, J.pfs(body), body), fa, body, back, CD.wp.clen(fa, TC(body)), B.Rec.pos(J.pfs(body)), JT, PF.fast_judge(Some{JT}, body), ht)
    case False{}:
      (slreqs_rq(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)), slreqs_c(Nat.is_eq(back, 0n), TC(body), TA(back, body), TE(body)))

def try_ok(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String) -> xOK(fa, body, tryP(fa, wp, back, body)):
  try_ok.k(CD.holds(fa, wp, TC(body), TA(back, body), TE(body)), fa, wp, back, body)

# The tries, pictured.
def sgP(fuel: Nat, +fa: List<&2, B.Contig>, +wp: CD.WP, +body: String, +x: SxP) -> SxP:
  match fuel x:
    case 1n+k XA{+b}:
      sgP(k, fa, wp, body, tryP(fa, wp, b, body))
    case _ x:
      x

def sg_eq(+fuel: Nat, +fa: List<&2, B.Contig>, +wp: CD.WP, +body: String, +x: SxP,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  {Norm.slow.go(fuel, mkSx(fa, wp, x), J.pfs(body), body) == mkSx(fa, wp, sgP(fuel, fa, wp, body, x)) : Norm.Sx}:
  match fuel x:
    case 1n+k XA{b}:
      %Equal.sym(Norm.Sx, Norm.slow.try(CD.mkWin(fa, wp), b, J.pfs(body), body), mkSx(fa, wp, tryP(fa, wp, b, body)), try_eq(fa, wp, b, body, hb, hv)) :
        {Norm.slow.go(k, _, J.pfs(body), body) == mkSx(fa, wp, sgP(k, fa, wp, body, tryP(fa, wp, b, body))) : Norm.Sx}
      sg_eq(k, fa, wp, body, tryP(fa, wp, b, body), hb, hv)
    case 0n _:
      {==}
    case 1n+k XD{f, b}:
      {==}
    case 1n+k XM{reqs, b}:
      {==}

def sg_ok(+fuel: Nat, +fa: List<&2, B.Contig>, +wp: CD.WP, +body: String, +x: SxP, hx: xOK(fa, body, x)) ->
  xOK(fa, body, sgP(fuel, fa, wp, body, x)):
  match fuel x:
    case 1n+k XA{b}:
      sg_ok(k, fa, wp, body, tryP(fa, wp, b, body), try_ok(fa, wp, b, body))
    case 0n _:
      hx
    case 1n+k XD{f, b}:
      hx
    case 1n+k XM{reqs, b}:
      hx

# ---------------------------------------------------------------------------
# The verdict
# ---------------------------------------------------------------------------

type VdP is Data:
  VRP{r: B.Res}
  VSP{}
  VWP{reqs: List<&2, Pr.Req>, b: Nat}

def mkVd(+fa: List<&2, B.Contig>, +wp: CD.WP, +v: VdP) -> Norm.Vd:
  match v:
    case VRP{r}:
      Norm.VRes{CD.mkWin(fa, wp), r}
    case VSP{}:
      Norm.VSame{CD.mkWin(fa, wp)}
    case VWP{reqs, b}:
      Norm.VWant{CD.mkWin(fa, wp), reqs, b}

# What a verdict says: the spec's judge, Normalized as it is, or reads that
# keep the contract.
def vdOK(+fa: List<&2, B.Contig>, +body: String, +v: VdP) -> Type:
  match v:
    case VRP{+r}:
      {r == L.judge(fa, body) : B.Res}
    case VSP{}:
      {B.Res{B.Normalized{}, B.Rec.pos(J.pfs(body)), body, False{}} == L.judge(fa, body) : B.Res}
    case VWP{+reqs, b}:
      RQOK(reqs) & {fst_c(reqs) == Some{B.Rec.field(J.pfs(body), 0n)} : Maybe<&2, String>}

def VPARTS(+body: String) -> List<&2, Pr.Req>:
  Norm.parts(B.Rec.field(J.pfs(body), 0n), 0n, Nat.add(B.Rec.pos(J.pfs(body)), String.length(B.Rec.field(J.pfs(body), 3n))))

def vxP(+body: String, +x: SxP) -> VdP:
  match x:
    case XA{b}:
      VWP{VPARTS(body), B.Rec.pos(J.pfs(body))}
    case XD{J.Same{}, b}:
      VSP{}
    case XD{J.Other{Some{r}}, b}:
      VRP{r}
    case XD{J.Other{None{}}, b}:
      VWP{VPARTS(body), B.Rec.pos(J.pfs(body))}
    case XM{reqs, b}:
      VWP{reqs, b}

def vx_eq(+fa: List<&2, B.Contig>, +wp: CD.WP, +body: String, +x: SxP) ->
  {Norm.vd.x(mkSx(fa, wp, x), J.pfs(body)) == mkVd(fa, wp, vxP(body, x)) : Norm.Vd}:
  match x:
    case XA{b}:
      {==}
    case XD{J.Same{}, b}:
      {==}
    case XD{J.Other{Some{r}}, b}:
      {==}
    case XD{J.Other{None{}}, b}:
      {==}
    case XM{reqs, b}:
      {==}

def VP0(+body: String) -> vdOK(Nil{}, body, VWP{VPARTS(body), 0n}):
  +E0 = Nat.add(B.Rec.pos(J.pfs(body)), String.length(B.Rec.field(J.pfs(body), 3n)))
  (parts_rq(B.Rec.field(J.pfs(body), 0n), 0n, E0), parts_c(B.Rec.field(J.pfs(body), 0n), 0n, E0))

def vx_ok(+fa: List<&2, B.Contig>, +body: String, +x: SxP, hx: xOK(fa, body, x)) -> vdOK(fa, body, vxP(body, x)):
  match x:
    case XA{b}:
      VP0(body)
    case XD{J.Same{}, b}:
      %Equal.sym(Nat, B.Rec.pos(J.pfs(body)), B.Rec.pos(B.Rec.fields(body)), PF.pfs_pos(body)) :
        {B.Res{B.Normalized{}, _, body, False{}} == L.judge(fa, body) : B.Res}
      jres_inj(B.Res{B.Normalized{}, B.Rec.pos(B.Rec.fields(body)), body, False{}}, L.judge(fa, body), hx)
    case XD{J.Other{Some{r}}, b}:
      jres_inj(r, L.judge(fa, body), hx)
    case XD{J.Other{None{}}, b}:
      VP0(body)
    case XM{reqs, b}:
      hx

def VdG(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String) -> Type:
  &v: VdP -> ({Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, v) : Norm.Vd} & vdOK(fa, body, v))

def vd_none_eq(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool},
  +hm: {J.judge_fs(None{}, J.pfs(body), body) == None{} : Maybe<&2, B.Res>}) ->
  {Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, vxP(body, sgP(64n, fa, wp, body, XA{back}))) : Norm.Vd}:
  +x1 = sgP(64n, fa, wp, body, XA{back})
  %Equal.sym(Maybe<&2, B.Res>, J.judge_fs(None{}, J.pfs(body), body), None{}, hm) :
    {Norm.vd.m(_, back, CD.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, vxP(body, x1)) : Norm.Vd}
  %Equal.sym(Norm.Sx, Norm.slow.go(64n, mkSx(fa, wp, XA{back}), J.pfs(body), body), mkSx(fa, wp, x1), sg_eq(64n, fa, wp, body, XA{back}, hb, hv)) :
    {Norm.vd.x(_, J.pfs(body)) == mkVd(fa, wp, vxP(body, x1)) : Norm.Vd}
  vx_eq(fa, wp, body, x1)

def vd_some_eq(+r: B.Res, +fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hm: {J.judge_fs(None{}, J.pfs(body), body) == Some{r} : Maybe<&2, B.Res>}) ->
  {Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, VRP{r}) : Norm.Vd}:
  %Equal.sym(Maybe<&2, B.Res>, J.judge_fs(None{}, J.pfs(body), body), Some{r}, hm) :
    {Norm.vd.m(_, back, CD.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, VRP{r}) : Norm.Vd}
  {==}

def vd_ok.m(+m: Maybe<&2, B.Res>, +fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool},
  +hm: {J.judge_fs(None{}, J.pfs(body), body) == m : Maybe<&2, B.Res>}) ->
  VdG(fa, wp, back, body):
  match m:
    case Some{r}:
      (VRP{r}, (vd_some_eq(r, fa, wp, back, body, hm), PW.window(fa, body, None{}, r, {==}, Equal.trans(Maybe<&2, B.Res>, J.judge_in(None{}, body), J.judge_fs(None{}, J.pfs(body), body), Some{r}, Equal.sym(Maybe<&2, B.Res>, J.judge_fs(None{}, J.pfs(body), body), J.judge_in(None{}, body), PF.judge_none(body)), hm))))
    case None{}:
      +x1 = sgP(64n, fa, wp, body, XA{back})
      (vxP(body, x1), (vd_none_eq(fa, wp, back, body, hb, hv, hm), vx_ok(fa, body, x1, sg_ok(64n, fa, wp, body, XA{back}, {==}))))

# The verdict lemma: from a pictured window (a truthful reference), a body
# line's verdict leaves the window as it was and is the spec's judge,
# Normalized as it is, or reads that keep the contract.
def vd_ok(+fa: List<&2, B.Contig>, +wp: CD.WP, +back: Nat, +body: String,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  VdG(fa, wp, back, body):
  vd_ok.m(J.judge_fs(None{}, J.pfs(body), body), fa, wp, back, body, hb, hv, {==})

# ---------------------------------------------------------------------------
# One String-mode line: the queued text, and the state the spec steps from
# ---------------------------------------------------------------------------

def X0(+qs: List<&2, String>) -> String:
  Norm.cat(List.reverse(&2, String, qs))

# (rev_acc .. cat_rev_cons: copied from proof_b_drive_finms.bend.)
def rev_acc(+xs: List<&2, String>, +acc: List<&2, String>) ->
  {List.reverse.go(&2, String, xs, acc) == List.append(&2, String, List.reverse.go(&2, String, xs, Nil{}), acc) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +Rv = List.reverse.go(&2, String, t, Nil{})
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, t, y <> acc), List.append(&2, String, Rv, y <> acc), List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc),
        rev_acc(t, y <> acc),
        Equal.sym(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, Rv, y <> acc),
          Equal.trans(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, List.append(&2, String, Rv, [y]), acc), List.append(&2, String, Rv, y <> acc),
            Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, acc), List.reverse.go(&2, String, t, [y]), List.append(&2, String, Rv, [y]), rev_acc(t, [y])),
            PB.append_assoc(String, Rv, [y], acc))))

def catgo_snoc(+t: List<&2, String>, +hd: String, +a: String) ->
  {Norm.cat.go(List.append(&2, String, t, [a]), hd) == String.append(Norm.cat.go(t, hd), a) : String}:
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(String, Norm.cat.go(List.append(&2, String, r, [a]), y), String.append(Norm.cat.go(r, y), a), catgo_snoc(r, y, a)) :
        {String.append(hd, _) == String.append(String.append(hd, Norm.cat.go(r, y)), a) : String}
      Equal.sym(String, String.append(String.append(hd, Norm.cat.go(r, y)), a), String.append(hd, String.append(Norm.cat.go(r, y), a)), PN.str_assoc(hd, Norm.cat.go(r, y), a))

def cat_snoc(+xs: List<&2, String>, +a: String) -> {Norm.cat(List.append(&2, String, xs, [a])) == String.append(Norm.cat(xs), a) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      catgo_snoc(t, y, a)

def cat_rev_cons(+a: String, +qs: List<&2, String>) -> {Norm.cat(List.reverse(&2, String, a <> qs)) == String.append(X0(qs), a) : String}:
  Equal.trans(String, Norm.cat(List.reverse.go(&2, String, qs, [a])), Norm.cat(List.append(&2, String, List.reverse.go(&2, String, qs, Nil{}), [a])), String.append(X0(qs), a),
    Equal.cong(List<&2, String>, String, z => Norm.cat(z), List.reverse.go(&2, String, qs, [a]), List.append(&2, String, List.reverse.go(&2, String, qs, Nil{}), [a]), rev_acc(qs, [a])),
    cat_snoc(List.reverse.go(&2, String, qs, Nil{}), a))

def emp_str(+x: String, +h: {String.is_empty(x) == True{} : Bool}) -> {x == "" : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == "" : String}, N.false_ne_true(h))

# A state with nothing written, the queued text put in front.
def wo_pre(+s: R.RunSt, +x: String, +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool}) ->
  {S.with_out(s, x) == S.pre(x, Nil{}, s) : R.RunSt}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +xh}:
      %Equal.sym(String, o, "", emp_str(o, hout)) : {R.RunSt{n, i, h, c, e, l, b, k, x, ns, xh} == R.RunSt{n, i, h, c, e, l, b, k, String.append(x, _), ns, xh} : R.RunSt}
      %Equal.sym(String, String.append(x, ""), x, X.str_nil(x)) : {R.RunSt{n, i, h, c, e, l, b, k, x, ns, xh} == R.RunSt{n, i, h, c, e, l, b, k, _, ns, xh} : R.RunSt}
      {==}

# What the String mode stands for after a line (ms.out): the queued text in
# front of the line's state.
def smd_pre(+st: R.RunSt, +qs: List<&2, String>, +ql: Nat) -> {S.smd(MS.msO(st, qs, ql)) == S.pre(X0(qs), Nil{}, st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %Equal.sym(String, Norm.cat(List.reverse(&2, String, o <> qs)), String.append(X0(qs), o), cat_rev_cons(o, qs)) :
        {R.RunSt{n, i, h, c, e, l, b, k, _, ns, x} == R.RunSt{n, i, h, c, e, l, b, k, String.append(X0(qs), o), ns, x} : R.RunSt}
      {==}

def ib_msO(+st: R.RunSt, +qs: List<&2, String>, +ql: Nat) -> {R.RunSt.inbody(S.smd(MS.msO(st, qs, ql))) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

def ib_wo(+st: R.RunSt, +x: String) -> {R.RunSt.inbody(S.with_out(st, x)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +xh}:
      {==}

def ib_step.k(+xh: Bool, +i: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o0: String, +ns: List<&2, B.Note>, +l: B.Line,
  +hi: {i == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, o, R.RunSt{n, i, h, c, e, la, b, k, o0, ns, xh}, l)) == True{} : Bool}:
  match xh i:
    case True{} _:
      hi
    case False{} True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      FF.ib_body_line(L.judge(fa, B.Line.body(l)), R.RunSt{1n+n, True{}, h, c, e, la, b, k, o0, ns, False{}}, o, l, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
    case False{} False{}:
      Empty.absurd({R.RunSt.inbody(L.line_step(fa, o, R.RunSt{n, False{}, h, c, e, la, b, k, o0, ns, False{}}, l)) == True{} : Bool}, N.false_ne_true(hi))

# Once in the body, a line keeps the run in the body.
def ib_step(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +hi: {R.RunSt.inbody(s) == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, o, s, l)) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o0, +ns, +xh}:
      ib_step.k(xh, i, fa, o, n, h, c, e, la, b, k, o0, ns, l, hi)

# The text still to come, the first line split off.
def itx_split(+src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: List<&2, String>, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String}) ->
  {MS.ITX(src, pd, eof, cs) == String.append(q, String.append("\n", MS.ITX(src2, pd, eof, cs))) : String}:
  +R0 = String.append(P.pdtext(pd), S.concat_if(eof, cs))
  +S2 = P.srcstext(src2)
  %Equal.sym(String, P.srcstext(src), String.append(q, String.append("\n", S2)), hst) : {String.append(_, R0) == String.append(q, String.append("\n", MS.ITX(src2, pd, eof, cs))) : String}
  %Equal.sym(String, String.append(String.append(q, String.append("\n", S2)), R0), String.append(q, String.append(String.append("\n", S2), R0)), PN.str_assoc(q, String.append("\n", S2), R0)) : {_ == String.append(q, String.append("\n", MS.ITX(src2, pd, eof, cs))) : String}
  %Equal.sym(String, String.append(String.append("\n", S2), R0), String.append("\n", String.append(S2, R0)), PN.str_assoc("\n", S2, R0)) : {String.append(q, _) == String.append(q, String.append("\n", MS.ITX(src2, pd, eof, cs))) : String}
  {==}

def SO(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed}

def rep_line.eq(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool,
  +hg: {Bool.or(R.RunSt.inbody(S.with_out(s, X0(qs))), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool}) ->
  {R.finish(L.run.go(B.Text.lines(MS.ITX(src2, pd, eof, cs)), fa, o, S.pre(O, N, S.pre(X0(qs), Nil{}, L.line_step(fa, o, s, B.Text.line(q))))))
    == R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, o, S.pre(O, N, S.with_out(s, X0(qs))))) : R.Report}:
  +l = B.Text.line(q)
  +Y = MS.ITX(src2, pd, eof, cs)
  +x = X0(qs)
  +LHS = R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, S.pre(x, Nil{}, L.line_step(fa, o, s, l)))))
  +hg2 = AB.subst(Bool, z => {Bool.or(R.RunSt.inbody(s), z) == True{} : Bool}, String.is_empty(x), Bool.and(String.is_empty(x), True{}),
    Equal.sym(Bool, Bool.and(String.is_empty(x), True{}), String.is_empty(x), N.and_true_r_id(String.is_empty(x))), h5)
  %Equal.sym(String, MS.ITX(src, pd, eof, cs), String.append(q, String.append("\n", Y)), itx_split(src, src2, pd, eof, cs, q, hst)) :
    {LHS == R.finish(L.run.go(B.Text.lines(_), fa, o, S.pre(O, N, S.with_out(s, x)))) : R.Report}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(q, String.append("\n", Y))), l <> B.Text.lines(Y), LS.lines_cons(q, Y, hq)) :
    {LHS == R.finish(L.run.go(_, fa, o, S.pre(O, N, S.with_out(s, x)))) : R.Report}
  %Equal.sym(R.RunSt, L.line_step(fa, o, S.pre(O, N, S.with_out(s, x)), l), S.pre(O, N, L.line_step(fa, o, S.with_out(s, x), l)), FR.step_pre(fa, o, O, N, S.with_out(s, x), l, hg)) :
    {LHS == R.finish(L.run.go(B.Text.lines(Y), fa, o, _)) : R.Report}
  %Equal.sym(R.RunSt, S.with_out(s, x), S.pre(x, Nil{}, s), wo_pre(s, x, hout)) :
    {LHS == R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, L.line_step(fa, o, _, l)))) : R.Report}
  %Equal.sym(R.RunSt, L.line_step(fa, o, S.pre(x, Nil{}, s), l), S.pre(x, Nil{}, L.line_step(fa, o, s, l)), FR.step_pre(fa, o, x, Nil{}, s, l, hg2)) :
    {LHS == R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, _))) : R.Report}
  {==}

def bytes_app(+x: String, +y: String, +hx: {E.is_bytes(x) == True{} : Bool}, +hy: {E.is_bytes(y) == True{} : Bool}) ->
  {E.is_bytes(String.append(x, y)) == True{} : Bool}:
  match x:
    case SNil{}:
      hy
    case SCon{c, t}:
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(t, y)), W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), hx),
        bytes_app(t, y, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), hx), hy))

def len_ok(+ql: Nat, +x: String, +o: String, +hql: {Nat.is_eq(ql, String.length(x)) == True{} : Bool}) ->
  {Nat.is_eq(Nat.add(ql, String.length(o)), String.length(String.append(x, o))) == True{} : Bool}:
  %Equal.sym(Nat, String.length(String.append(x, o)), Nat.add(String.length(x), String.length(o)), PN.str_len_append(x, o)) : {Nat.is_eq(Nat.add(ql, String.length(o)), _) == True{} : Bool}
  %Equal.sym(Nat, ql, String.length(x), N.eq_sound(ql, String.length(x), hql)) : {Nat.is_eq(Nat.add(_, String.length(o)), Nat.add(String.length(x), String.length(o))) == True{} : Bool}
  N.eq_refl(Nat.add(String.length(x), String.length(o)))

# The String mode after ms.out is good, given the facts about the line's
# state.
def mdok_msO(+st: R.RunSt, +qs: List<&2, String>, +ql: Nat,
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(st) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(st), String.is_empty(String.append(X0(qs), P.RunSt.out(st)))) == True{} : Bool},
  +h6: {Bool.or(R.RunSt.inbody(st), List.is_empty(&2, B.Note, P.RunSt.notes(st))) == True{} : Bool}) ->
  {S.md_ok(MS.msO(st, qs, ql)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +q2 = String.append(X0(qs), o)
      +s0 = {R.RunSt{n, i, h, c, e, l, b, k, "", ns, x} : R.RunSt}
      +A1 = Nat.is_eq(Nat.add(ql, String.length(o)), String.length(q2))
      +A2 = Bool.and(A1, E.is_bytes(q2))
      +A3 = Bool.and(A2, P.st_bytes(s0))
      +A4 = Bool.and(A3, String.is_empty(""))
      +A5 = Bool.and(A4, Bool.or(i, String.is_empty(q2)))
      +hb1 = W.and_l(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hsb)
      +hob = W.and_r(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hsb)
      +hlen = len_ok(ql, X0(qs), o, hql)
      %Equal.sym(String, Norm.cat(List.reverse(&2, String, o <> qs)), q2, cat_rev_cons(o, qs)) :
        {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_eq(Nat.add(ql, String.length(o)), String.length(_)), E.is_bytes(_)), P.st_bytes(s0)), String.is_empty("")), Bool.or(i, String.is_empty(_))), Bool.or(i, List.is_empty(&2, B.Note, ns))) == True{} : Bool}
      W.and_tt(A5, Bool.or(i, List.is_empty(&2, B.Note, ns)),
        W.and_tt(A4, Bool.or(i, String.is_empty(q2)),
          W.and_tt(A3, String.is_empty(""),
            W.and_tt(A2, P.st_bytes(s0),
              W.and_tt(A1, E.is_bytes(q2), hlen, bytes_app(X0(qs), o, hxb, hob)),
              W.and_tt(Bool.and(E.is_bytes(h), P.items_bytes(b)), True{}, hb1, {==})),
            {==}),
          h5),
        h6)

def SM2(+o: B.Opts, +s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP) -> S.StP:
  S.StP{o, MS.msO(s2, qs, ql), src2, pd, eof, 0n, wp, None{}, False{}}

# The state after a consumed line is good: its String mode is (hmd), the
# rest is as in the state with the new sources (hw2).
def wf_went(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP,
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hmd: {S.md_ok(MS.msO(s2, qs, ql)) == True{} : Bool}) ->
  {S.WF(fa, SM2(o, s2, qs, ql, src2, pd, eof, wp)) == True{} : Bool}:
  +pm = SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})
  +p2 = SM2(o, s2, qs, ql, src2, pd, eof, wp)
  +h = Equal.trans(Bool, W.C9(W.W0(fa, pm), W.W1(fa, pm), W.W2(fa, pm), W.W3(fa, pm), W.W4(fa, pm), W.W5(fa, pm), W.W6(fa, pm), W.W7(fa, pm), W.W8(fa, pm)), S.WF(fa, pm), True{},
    Equal.sym(Bool, S.WF(fa, pm), W.C9(W.W0(fa, pm), W.W1(fa, pm), W.W2(fa, pm), W.W3(fa, pm), W.W4(fa, pm), W.W5(fa, pm), W.W6(fa, pm), W.W7(fa, pm), W.W8(fa, pm)), W.wf_c9(fa, pm)), hw2)
  Equal.trans(Bool, S.WF(fa, p2), W.C9(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2)), True{}, W.wf_c9(fa, p2),
    W.c9_m(W.W0(fa, pm), W.W0(fa, p2), W.W1(fa, pm), W.W2(fa, pm), W.W3(fa, pm), W.W4(fa, pm), W.W5(fa, pm), W.W6(fa, pm), W.W7(fa, pm), W.W7(fa, p2), W.W8(fa, pm), h, hmd, MS.mbw_msO(s2, qs, ql, wp)))

def rep_went(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +s2: R.RunSt,
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hs2: {s2 == L.line_step(fa, o, s, B.Text.line(q)) : R.RunSt}) ->
  {S.report(fa, cs, O, N, SM2(o, s2, qs, ql, src2, pd, eof, wp)) == T : R.Report}:
  +Y = MS.ITX(src2, pd, eof, cs)
  %MS.rep_msO(fa, cs, O, N, o, s2, qs, ql, src2, pd, eof, 0n, wp, None{}, False{}) : {_ == T : R.Report}
  %Equal.sym(R.RunSt, S.smd(MS.msO(s2, qs, ql)), S.pre(X0(qs), Nil{}, s2), smd_pre(s2, qs, ql)) : {R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, _))) == T : R.Report}
  %Equal.sym(R.RunSt, s2, L.line_step(fa, o, s, B.Text.line(q)), hs2) : {R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, S.pre(X0(qs), Nil{}, _)))) == T : R.Report}
  Equal.trans(R.Report, R.finish(L.run.go(B.Text.lines(Y), fa, o, S.pre(O, N, S.pre(X0(qs), Nil{}, L.line_step(fa, o, s, B.Text.line(q)))))),
    R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, o, S.pre(O, N, S.with_out(s, X0(qs))))), T,
    rep_line.eq(fa, cs, O, N, o, s, qs, q, src, src2, pd, eof, hg, hst, hq, hout, h5), hr)

def guard_went(+O: String, +N: List<&2, B.Note>, +o: B.Opts, +s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP,
  +hgd: {Bool.or(R.RunSt.inbody(s2), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}) ->
  {S.guard(O, N, SM2(o, s2, qs, ql, src2, pd, eof, wp)) == True{} : Bool}:
  %Equal.sym(Bool, R.RunSt.inbody(S.smd(MS.msO(s2, qs, ql))), R.RunSt.inbody(s2), ib_msO(s2, qs, ql)) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  hgd

def est_went(+fa: List<&2, B.Contig>, +o: B.Opts, +s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP) ->
  {Norm.St{o, Norm.ms.out(s2, qs, ql), P.mkSrcs(src2), P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}} == S.mkSt(fa, SM2(o, s2, qs, ql, src2, pd, eof, wp)) : Norm.St}:
  %MS.mk_msO(s2, qs, ql) : {Norm.St{o, _, P.mkSrcs(src2), P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}} == S.mkSt(fa, SM2(o, s2, qs, ql, src2, pd, eof, wp)) : Norm.St}
  {==}

def meas_went(+o: B.Opts, +s2: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: CD.WP,
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool}) ->
  {Nat.is_lt(S.measure(SM2(o, s2, qs, ql, src2, pd, eof, wp)), S.msrc(src)) == True{} : Bool}:
  %MS.meas_msO(o, s2, qs, ql, src2, pd, eof, 0n, wp, None{}, False{}) : {Nat.is_lt(_, S.msrc(src)) == True{} : Bool}
  hm2

# A consumed line (ms.done): the next state is good and stands for T.
def wentL(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +s2: R.RunSt,
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hs2: {s2 == L.line_step(fa, o, s, B.Text.line(q)) : R.RunSt},
  +hmd: {S.md_ok(MS.msO(s2, qs, ql)) == True{} : Bool},
  +hgd: {Bool.or(R.RunSt.inbody(s2), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.done(o, s2, qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  +p2 = SM2(o, s2, qs, ql, src2, pd, eof, wp)
  +est = est_went(fa, o, s2, qs, ql, src2, pd, eof, wp)
  +emeas = meas_went(o, s2, qs, ql, src, src2, pd, eof, wp, hm2)
  (p2, (est, (wf_went(fa, o, s, s2, qs, ql, src2, pd, eof, wp, hw2, hmd),
    (rep_went(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, s2, hr, hg, hst, hq, hout, h5, hs2),
    (emeas, (MS.asked_msO(o, s2, qs, ql, src2, pd, eof, 0n, wp, None{}, False{}), ({==}, (guard_went(O, N, o, s2, qs, ql, src2, pd, eof, wp, hgd), ({==}, (Unit{}, Unit{}))))))))))

# ---------------------------------------------------------------------------
# A text line q in the String mode: header line, body line, or reads asked
# ---------------------------------------------------------------------------

# The machine reads its line with Norm.line, the spec with B.Text.line.
def mline_eq(+o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +back: Nat, cx: Norm.Cx, win: Norm.Win) ->
  {Norm.ms.line(o, s, qs, ql, q, back, cx, win) == Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, q, B.Text.line(q), back, cx, win) : Norm.Adv}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      %LS.line_eq(q) : {Norm.ms.line(o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, qs, ql, q, back, cx, win) == Norm.ms.line.k(i, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, qs, ql, q, _, back, cx, win) : Norm.Adv}
      {==}

# A run that has not stopped takes the line.
def spec_eq(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  {L.line_step(fa, o, s, l) == L.line_in(R.RunSt.inbody(s), fa, o, R.tick(s), l) : R.RunSt}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) : {L.line_step(fa, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, _}, l) == L.line_in(i, fa, o, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, _}), l) : R.RunSt}
      {==}

# The body line the machine writes is the spec's, given the judge's result.
def bl_eq(+r: B.Res, +fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +hrj: {r == L.judge(fa, B.Line.body(l)) : B.Res}) ->
  {R.body_line(r, R.tick(s), o, l, Norm.at_of(R.RunSt.n(R.tick(s)), J.pfs(B.Line.body(l))), B.Rec.pos(J.pfs(B.Line.body(l)))) == L.line_in(True{}, fa, o, R.tick(s), l) : R.RunSt}:
  +BD = B.Line.body(l)
  +RN = R.RunSt.n(R.tick(s))
  +LHS = R.body_line(r, R.tick(s), o, l, Norm.at_of(RN, J.pfs(BD)), B.Rec.pos(J.pfs(BD)))
  %hrj : {LHS == R.body_line(_, R.tick(s), o, l, B.At{RN, B.Rec.field(B.Rec.fields(BD), 0n), B.Rec.field(B.Rec.fields(BD), 1n)}, B.Rec.pos(B.Rec.fields(BD))) : R.RunSt}
  %PF.pfs_pos(BD) : {LHS == R.body_line(r, R.tick(s), o, l, B.At{RN, B.Rec.field(B.Rec.fields(BD), 0n), B.Rec.field(B.Rec.fields(BD), 1n)}, _) : R.RunSt}
  %PF.pfs_field(BD, 0n, {==}) : {LHS == R.body_line(r, R.tick(s), o, l, B.At{RN, _, B.Rec.field(B.Rec.fields(BD), 1n)}, B.Rec.pos(J.pfs(BD))) : R.RunSt}
  %PF.pfs_field(BD, 1n, {==}) : {LHS == R.body_line(r, R.tick(s), o, l, B.At{RN, B.Rec.field(J.pfs(BD), 0n), _}, B.Rec.pos(J.pfs(BD))) : R.RunSt}
  {==}

# ---------------------------------------------------------------------------
# The run's texts stay bytes (run.bend, String mode)
# ---------------------------------------------------------------------------

# The judge's text is bytes, for a record of bytes and a reference of bytes
# (pb-lines' proof_b_judge_bytes.bend).
def judge_bytes(+fa: List<&2, B.Contig>, +body: String,
  hb: {CD.fa_bytes(fa) == True{} : Bool},
  hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge(fa, body))) == True{} : Bool}:
  JB.judge_bytes(fa, body, hb, hbd)

def stop_b(+st: R.RunSt, +out: String, +nt: B.Note, +hs: {P.st_bytes(st) == True{} : Bool}, +ho: {E.is_bytes(out) == True{} : Bool}) ->
  {P.st_bytes(R.stop(st, out, nt)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      W.and_tt(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(String.append(o, out)),
        W.and_l(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hs),
        bytes_app(o, out, W.and_r(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hs), ho))

def ins_put(+le: Bool, +k2: Nat, +p2: Nat, +a2: B.At, +t2: String, +k: Nat, +p: Nat, +a: B.At, +t: String, +tl: List<&2, R.Item>,
  +he: {E.is_bytes(t) == True{} : Bool},
  +h2: {E.is_bytes(t2) == True{} : Bool},
  +htl: {P.items_bytes(tl) == True{} : Bool},
  +ih: {P.items_bytes(R.insert(R.Item{k, p, a, t}, tl)) == True{} : Bool}) ->
  {P.items_bytes(R.insert.put(le, R.Item{k2, p2, a2, t2}, R.Item{k, p, a, t}, tl, R.insert(R.Item{k, p, a, t}, tl))) == True{} : Bool}:
  match le:
    case True{}:
      W.and_tt(E.is_bytes(t2), P.items_bytes(R.insert(R.Item{k, p, a, t}, tl)), h2, ih)
    case False{}:
      W.and_tt(E.is_bytes(t), P.items_bytes(Con{R.Item{k2, p2, a2, t2}, tl}), he, W.and_tt(E.is_bytes(t2), P.items_bytes(tl), h2, htl))

def ins_b(+k: Nat, +p: Nat, +a: B.At, +t: String, +buf: List<&2, R.Item>,
  +he: {E.is_bytes(t) == True{} : Bool},
  +hb: {P.items_bytes(buf) == True{} : Bool}) ->
  {P.items_bytes(R.insert(R.Item{k, p, a, t}, buf)) == True{} : Bool}:
  match buf:
    case Nil{}:
      W.and_tt(E.is_bytes(t), True{}, he, {==})
    case Con{R.Item{+k2, +p2, +a2, +t2}, +tl}:
      +h2 = W.and_l(E.is_bytes(t2), P.items_bytes(tl), hb)
      +htl = W.and_r(E.is_bytes(t2), P.items_bytes(tl), hb)
      ins_put(Nat.is_le(k2, k), k2, p2, a2, t2, k, p, a, t, tl, he, h2, htl, ins_b(k, p, a, t, tl, he, htl))

def tk_b(+buf: List<&2, R.Item>, +ok: Bool, +w: Nat, +ip: Nat, +hb: {P.items_bytes(buf) == True{} : Bool}) ->
  {P.items_bytes(R.take_ready.go(buf, ok, w, ip)) == True{} : Bool}:
  match buf ok:
    case Nil{} _:
      {==}
    case Con{R.Item{+k, +p, +a, +t}, +tl} True{}:
      W.and_tt(E.is_bytes(t), P.items_bytes(R.take_ready.go(tl, R.head_ready(w, ip, tl), w, ip)), W.and_l(E.is_bytes(t), P.items_bytes(tl), hb),
        tk_b(tl, R.head_ready(w, ip, tl), w, ip, W.and_r(E.is_bytes(t), P.items_bytes(tl), hb)))
    case Con{+x, +tl} False{}:
      {==}

def dr_b(+buf: List<&2, R.Item>, +ok: Bool, +w: Nat, +ip: Nat, +hb: {P.items_bytes(buf) == True{} : Bool}) ->
  {P.items_bytes(R.drop_ready.go(buf, ok, w, ip)) == True{} : Bool}:
  match buf ok:
    case Nil{} _:
      {==}
    case Con{R.Item{+k, +p, +a, +t}, +tl} True{}:
      dr_b(tl, R.head_ready(w, ip, tl), w, ip, W.and_r(E.is_bytes(t), P.items_bytes(tl), hb))
    case Con{+x, +tl} False{}:
      hb

def fbytes(+f: R.Flush) -> Bool:
  match f:
    case R.Flushed{+o, l}:
      E.is_bytes(o)
    case R.Broke{+o, b, p}:
      E.is_bytes(o)

def pre_b(+s: String, +f: R.Flush, +hs: {E.is_bytes(s) == True{} : Bool}, +hf: {fbytes(f) == True{} : Bool}) ->
  {fbytes(R.Flush.pre(s, f)) == True{} : Bool}:
  match f:
    case R.Flushed{+o, +l}:
      bytes_app(s, o, hs, hf)
    case R.Broke{+o, +b, +p}:
      bytes_app(s, o, hs, hf)

def fput(+ok: Bool, +k: Nat, +p: Nat, +a: B.At, +t: String, +last: Maybe<&2, R.Item>, +rest: R.Flush,
  +ht: {E.is_bytes(t) == True{} : Bool}, +hr: {fbytes(rest) == True{} : Bool}) ->
  {fbytes(R.flush.put(ok, R.Item{k, p, a, t}, last, rest)) == True{} : Bool}:
  match ok:
    case True{}:
      pre_b(t, rest, ht, hr)
    case False{}:
      {==}

def fl_b(+xs: List<&2, R.Item>, +last: Maybe<&2, R.Item>, +hb: {P.items_bytes(xs) == True{} : Bool}) ->
  {fbytes(R.flush(xs, last)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{R.Item{+k, +p, +a, +t}, +tl}:
      fput(R.flush.ok(last, k), k, p, a, t, last, R.flush(tl, Some{R.Item{k, p, a, t}}), W.and_l(E.is_bytes(t), P.items_bytes(tl), hb),
        fl_b(tl, Some{R.Item{k, p, a, t}}, W.and_r(E.is_bytes(t), P.items_bytes(tl), hb)))

def em_b(+f: R.Flush, +st: R.RunSt, +rest: List<&2, R.Item>, +at: B.At,
  +hf: {fbytes(f) == True{} : Bool}, +hs: {P.st_bytes(st) == True{} : Bool}, +hr: {P.items_bytes(rest) == True{} : Bool}) ->
  {P.st_bytes(R.emit.ready(f, st, rest, at)) == True{} : Bool}:
  match f:
    case R.Broke{+o, +bad, +prev}:
      stop_b(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev}, hs, hf)
    case R.Flushed{+o2, +l2}:
      match st:
        case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
          +H0 = Bool.and(E.is_bytes(h), P.items_bytes(b))
          W.and_tt(Bool.and(E.is_bytes(h), P.items_bytes(rest)), E.is_bytes(String.append(o, o2)),
            W.and_tt(E.is_bytes(h), P.items_bytes(rest), W.and_l(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(o), hs)), hr),
            bytes_app(o, o2, W.and_r(H0, E.is_bytes(o), hs), hf))

def sr_b(+st: R.RunSt, +w: Nat, +key: Nat, +inpos: Nat, +at: B.At, +text: String,
  +hs: {P.st_bytes(st) == True{} : Bool}, +ht: {E.is_bytes(text) == True{} : Bool}) ->
  {P.st_bytes(R.same_run(st, w, R.Item{key, inpos, at, text})) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +H0 = Bool.and(E.is_bytes(h), P.items_bytes(b))
      +hh = W.and_l(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(o), hs))
      +hbi = W.and_r(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(o), hs))
      +ho = W.and_r(H0, E.is_bytes(o), hs)
      +buf = R.insert(R.Item{key, inpos, at, text}, b)
      +hbuf = ins_b(key, inpos, at, text, b, ht, hbi)
      em_b(R.flush(R.take_ready(w, inpos, buf), l), R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, R.drop_ready(w, inpos, buf), at,
        fl_b(R.take_ready(w, inpos, buf), l, tk_b(buf, R.head_ready(w, inpos, buf), w, inpos, hbuf)),
        W.and_tt(Bool.and(E.is_bytes(h), True{}), E.is_bytes(o), W.and_tt(E.is_bytes(h), True{}, hh, {==}), ho),
        dr_b(buf, R.head_ready(w, inpos, buf), w, inpos, hbuf))

def nr.go(+f: R.Flush, +again: Bool, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool,
  +w: Nat, +chrom: String, +key: Nat, +inpos: Nat, +at: B.At, +text: String,
  +hf: {fbytes(f) == True{} : Bool},
  +hs: {P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
  +ht: {E.is_bytes(text) == True{} : Bool}) ->
  {P.st_bytes(R.new_run.go(f, again, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, R.Item{key, inpos, at, text})) == True{} : Bool}:
  match f again:
    case R.Broke{+o1, +bad, +prev} _:
      stop_b(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o1, B.Stop{B.Unsorted{}, Some{bad}, prev}, hs, hf)
    case R.Flushed{+o2, +l2} True{}:
      stop_b(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, o2, B.Stop{B.Unsorted{}, Some{at}, None{}}, hs, hf)
    case R.Flushed{+o2, +l2} False{}:
      +H0 = Bool.and(E.is_bytes(h), P.items_bytes(b))
      +hh = W.and_l(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(o), hs))
      +ho = W.and_r(H0, E.is_bytes(o), hs)
      sr_b(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), ns, x}, w, key, inpos, at, text,
        W.and_tt(Bool.and(E.is_bytes(h), True{}), E.is_bytes(String.append(o, o2)), W.and_tt(E.is_bytes(h), True{}, hh, {==}), bytes_app(o, o2, ho, hf)), ht)

def nr_b(+st: R.RunSt, +w: Nat, +chrom: String, +key: Nat, +inpos: Nat, +at: B.At, +text: String,
  +hs: {P.st_bytes(st) == True{} : Bool}, +ht: {E.is_bytes(text) == True{} : Bool}) ->
  {P.st_bytes(R.new_run(st, w, chrom, R.Item{key, inpos, at, text})) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +H0 = Bool.and(E.is_bytes(h), P.items_bytes(b))
      +hbi = W.and_r(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(o), hs))
      nr.go(R.flush(b, l), R.has(chrom, e), n, i, h, c, e, l, b, k, o, ns, x, w, chrom, key, inpos, at, text, fl_b(b, l, hbi), hs, ht)

def kg_b(+same: Bool, +st2: R.RunSt, +w: Nat, +chrom: String, +key: Nat, +inpos: Nat, +at: B.At, +text: String,
  +hs: {P.st_bytes(st2) == True{} : Bool}, +ht: {E.is_bytes(text) == True{} : Bool}) ->
  {P.st_bytes(R.keyed.go(same, st2, w, chrom, R.Item{key, inpos, at, text})) == True{} : Bool}:
  match same:
    case True{}:
      sr_b(st2, w, key, inpos, at, text, hs, ht)
    case False{}:
      nr_b(st2, w, chrom, key, inpos, at, text, hs, ht)

def ky_b(+st: R.RunSt, +w: Nat, +key: Nat, +inpos: Nat, +at: B.At, +text: String, +nts: List<&2, B.Note>, +k2: R.Cnt,
  +hs: {P.st_bytes(st) == True{} : Bool}, +ht: {E.is_bytes(text) == True{} : Bool}) ->
  {P.st_bytes(R.keyed(st, w, R.Item{key, inpos, at, text}, nts, k2)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      kg_b(R.is_cur(c, R.Item.chrom(R.Item{key, inpos, at, text})), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, R.Item.chrom(R.Item{key, inpos, at, text}),
        key, inpos, at, text, hs, ht)

def pl_b(+strict: Bool, +st: R.RunSt, +w: Nat, +c: B.Code, +l: B.Line, +at: B.At, +inpos: Nat,
  +hs: {P.st_bytes(st) == True{} : Bool}, +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) ->
  {P.st_bytes(R.problem_line(strict, st, w, c, l, at, inpos)) == True{} : Bool}:
  match strict:
    case True{}:
      stop_b(st, "", B.Stop{c, Some{at}, None{}}, hs, {==})
    case False{}:
      ky_b(st, w, inpos, inpos, at, B.Line.text(l), [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}), hs, hlt)

def bl_b.k(+oc: B.Outcome, +key: Nat, +t: String, +sl: Bool, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +hs: {P.st_bytes(st) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool},
  +hrt: {E.is_bytes(t) == True{} : Bool}) ->
  {P.st_bytes(R.body_line(B.Res{oc, key, t, sl}, st, o, l, at, inpos)) == True{} : Bool}:
  match oc:
    case B.Broken{}:
      stop_b(st, "", B.Stop{B.Malformed{}, Some{at}, None{}}, hs, {==})
    case B.NoContig{}:
      stop_b(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}}, hs, {==})
    case B.Problem{+c}:
      pl_b(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos, hs, hlt)
    case B.Skipped{}:
      ky_b(st, R.Opts.w(o), inpos, inpos, at, B.Line.text(l), Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}), hs, hlt)
    case B.Normalized{}:
      ky_b(st, R.Opts.w(o), key, inpos, at, String.append(t, B.Line.term(l)), R.stale_note(sl, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}), hs,
        bytes_app(t, B.Line.term(l), hrt, htm))

def bl_b(+r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +hs: {P.st_bytes(st) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool},
  +hrt: {E.is_bytes(P.res_text(r)) == True{} : Bool}) ->
  {P.st_bytes(R.body_line(r, st, o, l, at, inpos)) == True{} : Bool}:
  match r:
    case B.Res{+oc, +key, +t, +sl}:
      bl_b.k(oc, key, t, sl, st, o, l, at, inpos, hs, hlt, htm, hrt)

def hd_b.m(+isc: Bool, +l: B.Line, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool, +o: B.Opts,
  +hh: {E.is_bytes(h) == True{} : Bool},
  +hbi: {P.items_bytes(b) == True{} : Bool},
  +ho: {E.is_bytes(out) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hbd: {E.is_bytes(B.Line.body(l)) == True{} : Bool},
  +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) ->
  {P.st_bytes(R.head_line(isc, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, o, l)) == True{} : Bool}:
  match isc l:
    case True{} B.Line{+bd, +term}:
      W.and_tt(Bool.and(E.is_bytes(""), P.items_bytes(b)), E.is_bytes(String.append(h, String.append(R.added(o, term), String.append(bd, term)))),
        W.and_tt(E.is_bytes(""), P.items_bytes(b), {==}, hbi),
        bytes_app(h, String.append(R.added(o, term), String.append(bd, term)), hh,
          bytes_app(R.added(o, term), String.append(bd, term), WR.added_bytes(o, term, hob, htm), bytes_app(bd, term, hbd, htm))))
    case False{} _:
      W.and_tt(Bool.and(E.is_bytes(String.append(h, B.Line.text(l))), P.items_bytes(b)), E.is_bytes(out),
        W.and_tt(E.is_bytes(String.append(h, B.Line.text(l))), P.items_bytes(b), bytes_app(h, B.Line.text(l), hh, hlt), hbi), ho)

def hd_b.k(+isc: Bool, +l: B.Line, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool, +o: B.Opts,
  +hs: {P.st_bytes(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hbd: {E.is_bytes(B.Line.body(l)) == True{} : Bool},
  +htm: {E.is_bytes(B.Line.term(l)) == True{} : Bool},
  +hlt: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) ->
  {P.st_bytes(R.head_line(isc, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, o, l)) == True{} : Bool}:
  +H0 = Bool.and(E.is_bytes(h), P.items_bytes(b))
  +hh = W.and_l(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(out), hs))
  +hbi = W.and_r(E.is_bytes(h), P.items_bytes(b), W.and_l(H0, E.is_bytes(out), hs))
  +ho = W.and_r(H0, E.is_bytes(out), hs)
  hd_b.m(isc, l, n, i, h, c, e, la, b, k, out, ns, x, o, hh, hbi, ho, hob, hbd, htm, hlt)

def bd_k(+cr: Bool, +q: String, +h: {E.is_bytes(q) == True{} : Bool}) -> {E.is_bytes(B.Line.body(B.Text.line.if(cr, q))) == True{} : Bool}:
  match cr:
    case True{}:
      RI.take_bytes(q, Nat.sub(String.length(q), 1n), h)
    case False{}:
      h

def tx_k(+cr: Bool, +q: String, +h: {E.is_bytes(q) == True{} : Bool}) -> {E.is_bytes(B.Line.text(B.Text.line.if(cr, q))) == True{} : Bool}:
  match cr:
    case True{}:
      bytes_app(String.take(q, Nat.sub(String.length(q), 1n)), "\r\n", RI.take_bytes(q, Nat.sub(String.length(q), 1n), h), {==})
    case False{}:
      bytes_app(q, "\n", h, {==})

def stp.k(+x: Bool, +i: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +fa: List<&2, B.Contig>, +o: B.Opts, +q: String,
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hsb: {P.st_bytes(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool}) ->
  {P.st_bytes(L.line_step(fa, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, B.Text.line(q))) == True{} : Bool}:
  match x i:
    case True{} _:
      hsb
    case False{} False{}:
      hd_b.k(R.is_chrom_line(B.Line.body(B.Text.line(q))), B.Text.line(q), 1n+n, False{}, h, c, e, la, b, k, out, ns, False{}, o, hsb, hob,
        bd_k(String.ends_with(q, "\r"), q, hqb), WR.tb(String.ends_with(q, "\r"), q), tx_k(String.ends_with(q, "\r"), q, hqb))
    case False{} True{}:
      +BD = B.Line.body(B.Text.line(q))
      +S1 = R.tick(R.RunSt{n, True{}, h, c, e, la, b, k, out, ns, False{}})
      bl_b(L.judge(fa, BD), S1, o, B.Text.line(q), B.At{R.RunSt.n(S1), B.Rec.field(B.Rec.fields(BD), 0n), B.Rec.field(B.Rec.fields(BD), 1n)}, B.Rec.pos(B.Rec.fields(BD)),
        hsb, tx_k(String.ends_with(q, "\r"), q, hqb), WR.tb(String.ends_with(q, "\r"), q), judge_bytes(fa, BD, hfb, bd_k(String.ends_with(q, "\r"), q, hqb)))

# The state after a line holds bytes (the line's, the options', the judge's).
def step_bytes(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +q: String,
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  {P.st_bytes(L.line_step(fa, o, s, B.Text.line(q))) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      stp.k(x, i, n, h, c, e, la, b, k, out, ns, fa, o, q, hfb, hob, hsb, hqb)

def bytes2(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +q: String, +s2: R.RunSt,
  +hs2: {s2 == L.line_step(fa, o, s, B.Text.line(q)) : R.RunSt},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  {P.st_bytes(s2) == True{} : Bool}:
  %Equal.sym(R.RunSt, s2, L.line_step(fa, o, s, B.Text.line(q)), hs2) : {P.st_bytes(_) == True{} : Bool}
  step_bytes(fa, o, s, q, hfb, hob, hsb, hqb, hq)

def ib2(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +s2: R.RunSt,
  +hs2: {s2 == L.line_step(fa, o, s, l) : R.RunSt},
  +hib: {R.RunSt.inbody(s) == True{} : Bool}) ->
  {R.RunSt.inbody(s2) == True{} : Bool}:
  %Equal.sym(R.RunSt, s2, L.line_step(fa, o, s, l), hs2) : {R.RunSt.inbody(_) == True{} : Bool}
  ib_step(fa, o, s, l, hib)

# A consumed line, the String mode's facts given for the new state.
def wentS(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +s2: R.RunSt,
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hs2: {s2 == L.line_step(fa, o, s, B.Text.line(q)) : R.RunSt},
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +h52: {Bool.or(R.RunSt.inbody(s2), String.is_empty(String.append(X0(qs), P.RunSt.out(s2)))) == True{} : Bool},
  +h62: {Bool.or(R.RunSt.inbody(s2), List.is_empty(&2, B.Note, P.RunSt.notes(s2))) == True{} : Bool},
  +hgd: {Bool.or(R.RunSt.inbody(s2), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.done(o, s2, qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  wentL(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, s2, hr, hg, hst, hq, hout, h5, hw2, hm2, hs2,
    mdok_msO(s2, qs, ql, hql, hxb, bytes2(fa, o, s, q, s2, hs2, hfb, hob, hsb, hqb, hq), h52, h62), hgd)

# Header lines: the state is in the body after a #CHROM line, else out and
# notes stay as they were.
def hd5.k(+isc: Bool, +i: Bool, +l: B.Line, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool, +o: B.Opts, +X: String,
  +h5: {Bool.or(i, String.is_empty(X)) == True{} : Bool},
  +hout: {String.is_empty(out) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}), o, l)), String.is_empty(String.append(X, P.RunSt.out(R.head_line(isc, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}), o, l))))) == True{} : Bool}:
  match isc i l:
    case True{} _ B.Line{+bd, +term}:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} _:
      %Equal.sym(String, X, "", emp_str(X, h5)) : {String.is_empty(String.append(_, out)) == True{} : Bool}
      hout

def hd5(+isc: Bool, +s: R.RunSt, +l: B.Line, +o: B.Opts, +X: String,
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X)) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(s), o, l)), String.is_empty(String.append(X, P.RunSt.out(R.head_line(isc, R.tick(s), o, l))))) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      hd5.k(isc, i, l, n, h, c, e, la, b, k, out, ns, x, o, X, h5, hout)

def hd6.k(+isc: Bool, +i: Bool, +l: B.Line, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool, +o: B.Opts,
  +h6: {Bool.or(i, List.is_empty(&2, B.Note, ns)) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}), o, l)), List.is_empty(&2, B.Note, P.RunSt.notes(R.head_line(isc, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}), o, l)))) == True{} : Bool}:
  match isc i l:
    case True{} _ B.Line{+bd, +term}:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} _:
      h6

def hd6(+isc: Bool, +s: R.RunSt, +l: B.Line, +o: B.Opts,
  +h6: {Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(s), o, l)), List.is_empty(&2, B.Note, P.RunSt.notes(R.head_line(isc, R.tick(s), o, l)))) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      hd6.k(isc, i, l, n, h, c, e, la, b, k, out, ns, x, o, h6)

def hdz.k(+isc: Bool, +i: Bool, +l: B.Line, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool, +o: B.Opts, +Z: Bool,
  +hz: {Bool.or(i, Z) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}), o, l)), Z) == True{} : Bool}:
  match isc i l:
    case True{} _ B.Line{+bd, +term}:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} _:
      hz

def hdz(+isc: Bool, +s: R.RunSt, +l: B.Line, +o: B.Opts, +Z: Bool,
  +hz: {Bool.or(R.RunSt.inbody(s), Z) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(R.head_line(isc, R.tick(s), o, l)), Z) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      hdz.k(isc, i, l, n, h, c, e, la, b, k, out, ns, x, o, Z, hz)

def g_of(+O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool}) ->
  {Bool.or(R.RunSt.inbody(s), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}:
  %ib_wo(s, X0(qs)) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  hg

# The reads asked for a body line: the line goes back in front.
def rep_want(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +bk: Nat, +reqs: List<&2, Pr.Req>,
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String}) ->
  {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, bk, wp, Some{reqs}, False{})) == T : R.Report}:
  +R0 = String.append(P.pdtext(pd), S.concat_if(eof, cs))
  +S2 = P.srcstext(src2)
  +e = Equal.trans(String, P.srcstext(src), String.append(q, String.append("\n", S2)), P.srcstext(Con{P.SLP{q}, src2}), hst,
    Equal.sym(String, String.append(String.append(q, "\n"), S2), String.append(q, String.append("\n", S2)), PN.str_assoc(q, "\n", S2)))
  %e : {R.finish(L.run.go(B.Text.lines(String.append(_, R0)), fa, o, S.pre(O, N, S.smd(S.MSP{s, qs, ql, None{}})))) == T : R.Report}
  hr

def asked_some(+reqs: List<&2, Pr.Req>, +h3: {Nat.is_le(1n, List.length(&2, Pr.Req, reqs)) == True{} : Bool}) ->
  {Some{reqs} == S.asked_of(reqs) : Maybe<&2, List<&2, Pr.Req>>}:
  match reqs:
    case Nil{}:
      Empty.absurd({Some{Nil{}} == S.asked_of(Nil{}) : Maybe<&2, List<&2, Pr.Req>>}, N.false_ne_true(h3))
    case Con{+r, +t}:
      {==}

def stop_f(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  {S.stopped(S.MSP{s, qs, ql, None{}}) == False{} : Bool}:
  %Equal.sym(Bool, R.RunSt.halt(s), False{}, hx) : {Bool.or(_, Maybe.is_some(&2, Nat, None{})) == False{} : Bool}
  {==}

def wantL(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +reqs: List<&2, Pr.Req>, +bk: Nat,
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  hok: RQOK(reqs)) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.want(o, s, qs, ql, q, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp), reqs, bk)):
  (h1, h23) = hok
  (h2, h3) = h23
  (SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, bk, wp, Some{reqs}, False{}), ({==}, (hw3,
    (rep_want(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, bk, reqs, hr, hst),
    (h1, (h2, (asked_some(reqs, h3), (stop_f(s, qs, ql, hx), ({==}, ({==}, (hg, ({==}, (Unit{}, Unit{})))))))))))))

# A body line judged r (the spec's judge): the line is consumed.
def bodyW(+r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hrj: {r == L.judge(fa, B.Line.body(B.Text.line(q))) : B.Res},
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hsp: {L.line_step(fa, o, s, B.Text.line(q)) == L.line_in(True{}, fa, o, R.tick(s), B.Text.line(q)) : R.RunSt},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.done(o, R.body_line(r, R.tick(s), o, B.Text.line(q), Norm.at_of(R.RunSt.n(R.tick(s)), J.pfs(B.Line.body(B.Text.line(q)))), B.Rec.pos(J.pfs(B.Line.body(B.Text.line(q))))), qs, ql, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  +L0 = B.Text.line(q)
  +s2 = R.body_line(r, R.tick(s), o, L0, Norm.at_of(R.RunSt.n(R.tick(s)), J.pfs(B.Line.body(L0))), B.Rec.pos(J.pfs(B.Line.body(L0))))
  +hs2 = Equal.trans(R.RunSt, s2, L.line_in(True{}, fa, o, R.tick(s), L0), L.line_step(fa, o, s, L0), bl_eq(r, fa, o, s, L0, hrj),
    Equal.sym(R.RunSt, L.line_step(fa, o, s, L0), L.line_in(True{}, fa, o, R.tick(s), L0), hsp))
  +hi2 = ib2(fa, o, s, L0, s2, hs2, hib)
  wentS(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, s2, hr, hg, hst, hq, hqb, hout, h5, hw2, hm2, hs2, hql, hxb, hsb, hob, hfb,
    W.or_l(R.RunSt.inbody(s2), String.is_empty(String.append(X0(qs), P.RunSt.out(s2))), hi2),
    W.or_l(R.RunSt.inbody(s2), List.is_empty(&2, B.Note, P.RunSt.notes(s2)), hi2),
    W.or_l(R.RunSt.inbody(s2), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hi2))

# A body line, by its verdict.
def msline.v(+v: VdP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  hok: vdOK(fa, B.Line.body(B.Text.line(q)), v),
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hsp: {L.line_step(fa, o, s, B.Text.line(q)) == L.line_in(True{}, fa, o, R.tick(s), B.Text.line(q)) : R.RunSt},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.body(o, s, qs, ql, q, B.Text.line(q), J.pfs(B.Line.body(B.Text.line(q))), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, mkVd(fa, wp, v))):
  match v:
    case VRP{r}:
      bodyW(r, fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, hok, hib, hsp, hr, hg, hst, hq, hqb, hout, h5, hw2, hm2, hql, hxb, hsb, hob, hfb)
    case VSP{}:
      bodyW(B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(B.Text.line(q)))), B.Line.body(B.Text.line(q)), False{}}, fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed,
        hok, hib, hsp, hr, hg, hst, hq, hqb, hout, h5, hw2, hm2, hql, hxb, hsb, hob, hfb)
    case VWP{reqs, bk}:
      (hq1, hc) = hok
      wantL(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, reqs, bk, hr, hg, hx, hst, hw3, hq1)

def msline.g(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  g: VdG(fa, wp, back, B.Line.body(B.Text.line(q))),
  +hib: {R.RunSt.inbody(s) == True{} : Bool},
  +hsp: {L.line_step(fa, o, s, B.Text.line(q)) == L.line_in(True{}, fa, o, R.tick(s), B.Text.line(q)) : R.RunSt},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.line.k(True{}, o, s, qs, ql, q, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  (v, pr) = g
  (heq, hok) = pr
  +BD = B.Line.body(B.Text.line(q))
  AB.subst(Norm.Vd, z => S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), Norm.ms.body(o, s, qs, ql, q, B.Text.line(q), J.pfs(BD), Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, z)),
    mkVd(fa, wp, v), Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(BD), BD), Equal.sym(Norm.Vd, Norm.verdict(back, CD.mkWin(fa, wp), J.pfs(BD), BD), mkVd(fa, wp, v), heq),
    msline.v(v, fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, hok, hib, hsp, hr, hg, hx, hst, hq, hqb, hout, h5, hw2, hw3, hm2, hql, hxb, hsb, hob, hfb))

# A line, header or body.
def msline.i(+ib: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hib: {R.RunSt.inbody(s) == ib : Bool},
  +hsp: {L.line_step(fa, o, s, B.Text.line(q)) == L.line_in(ib, fa, o, R.tick(s), B.Text.line(q)) : R.RunSt},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hout: {String.is_empty(P.RunSt.out(s)) == True{} : Bool},
  +h5: {Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool},
  +h6: {Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hql: {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool},
  +hxb: {E.is_bytes(X0(qs)) == True{} : Bool},
  +hsb: {P.st_bytes(s) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.line.k(ib, o, s, qs, ql, q, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  match ib:
    case True{}:
      msline.g(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, vd_ok(fa, wp, back, B.Line.body(B.Text.line(q)), hfb, hv),
        hib, hsp, hr, hg, hx, hst, hq, hqb, hout, h5, hw2, hw3, hm2, hql, hxb, hsb, hob, hfb)
    case False{}:
      +L0 = B.Text.line(q)
      +isc = R.is_chrom_line(B.Line.body(L0))
      +s2 = R.head_line(isc, R.tick(s), o, L0)
      +hs2 = Equal.sym(R.RunSt, L.line_step(fa, o, s, L0), s2, hsp)
      wentS(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, s2, hr, hg, hst, hq, hqb, hout, h5, hw2, hm2, hs2, hql, hxb, hsb, hob, hfb,
        hd5(isc, s, L0, o, X0(qs), h5, hout), hd6(isc, s, L0, o, h6),
        hdz(isc, s, L0, o, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), g_of(O, N, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, hg)))

# The facts of a good String mode.
def MDF(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat) -> Type:
  {Nat.is_eq(ql, String.length(X0(qs))) == True{} : Bool}
  & ({E.is_bytes(X0(qs)) == True{} : Bool}
  & ({P.st_bytes(s) == True{} : Bool}
  & ({String.is_empty(P.RunSt.out(s)) == True{} : Bool}
  & ({Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs))) == True{} : Bool}
  & {Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s))) == True{} : Bool}))))

def md_facts(+s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +h: {S.md_ok(S.MSP{s, qs, ql, None{}}) == True{} : Bool}) -> MDF(s, qs, ql):
  +M1 = Nat.is_eq(ql, String.length(X0(qs)))
  +M2 = E.is_bytes(X0(qs))
  +M3 = P.st_bytes(s)
  +M4 = String.is_empty(P.RunSt.out(s))
  +M5 = Bool.or(R.RunSt.inbody(s), String.is_empty(X0(qs)))
  +M6 = Bool.or(R.RunSt.inbody(s), List.is_empty(&2, B.Note, P.RunSt.notes(s)))
  +A2 = Bool.and(M1, M2)
  +A3 = Bool.and(A2, M3)
  +A4 = Bool.and(A3, M4)
  +A5 = Bool.and(A4, M5)
  +h5 = W.and_l(A5, M6, h)
  +h4 = W.and_l(A4, M5, h5)
  +h3 = W.and_l(A3, M4, h4)
  +h2 = W.and_l(A2, M3, h3)
  (W.and_l(M1, M2, h2), (W.and_r(M1, M2, h2), (W.and_r(A2, M3, h3), (W.and_r(A3, M4, h4), (W.and_r(A4, M5, h5), W.and_r(A5, M6, h))))))

def wfC(+fa: List<&2, B.Contig>, +p: S.StP, +hw: {S.WF(fa, p) == True{} : Bool}) ->
  {W.C9(W.W0(fa, p), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p)) == True{} : Bool}:
  Equal.trans(Bool, W.C9(W.W0(fa, p), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p)), S.WF(fa, p), True{},
    Equal.sym(Bool, S.WF(fa, p), W.C9(W.W0(fa, p), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p)), W.wf_c9(fa, p)), hw)

def msline.m(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  mf: MDF(s, qs, ql),
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool},
  +hob: {E.all_bytes(S.opts_args(o)) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  (hql, m1) = mf
  (hxb, m2) = m1
  (hsb, m3) = m2
  (hout, m4) = m3
  (h5, h6) = m4
  AB.subst(Norm.Adv, z => S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed), z),
    Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, q, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp)), Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp)),
    Equal.sym(Norm.Adv, Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp)), Norm.ms.line.k(R.RunSt.inbody(s), o, s, qs, ql, q, B.Text.line(q), back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp)), mline_eq(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))),
    msline.i(R.RunSt.inbody(s), fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, {==}, spec_eq(fa, o, s, B.Text.line(q), hx),
      hr, hg, hx, hst, hq, hqb, hout, h5, h6, hw2, hw3, hm2, hql, hxb, hsb, hob, hfb, hv))

# The core: a text line q (no LF, bytes) at the front of the sources src, the
# sources after it src2 (good states with src2 and with q put back in front
# are given by the caller).
def msline(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String,
  +src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hfb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hq: {P.nolf(q) == True{} : Bool},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hw3: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hm2: {Nat.is_lt(S.msrc(src2), S.msrc(src)) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(src2), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  +pp = SO(o, s, qs, ql, src, pd, eof, back, wp, asked, fneed)
  +hc = wfC(fa, pp, hw)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +hv = W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  +hob = W.c9_8(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)
  msline.m(fa, T, cs, O, N, o, s, qs, ql, q, src, src2, pd, eof, back, wp, asked, fneed, md_facts(s, qs, ql, W.c9_0(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
    hfb, hr, hg, hx, hst, hq, hqb, hw2, hw3, hm2, hv, hob)

# ---------------------------------------------------------------------------
# adv.ms.sl: a text line source
# ---------------------------------------------------------------------------

def src_hd(+sp: P.SrcP, +rest: List<&2, P.SrcP>, +h: {S.srcs_ok(Con{sp, rest}) == True{} : Bool}) -> {P.src_ok(sp) == True{} : Bool}:
  match rest:
    case Nil{}:
      h
    case Con{+a, +b}:
      W.and_l(P.src_ok(sp), S.ends_lf(P.srctext(sp)), W.and_l(Bool.and(P.src_ok(sp), S.ends_lf(P.srctext(sp))), S.srcs_ok(Con{a, b}), h))

def srcs_tl(+sp: P.SrcP, +rest: List<&2, P.SrcP>, +h: {S.srcs_ok(Con{sp, rest}) == True{} : Bool}) -> {S.srcs_ok(rest) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      W.and_r(Bool.and(P.src_ok(sp), S.ends_lf(P.srctext(sp))), S.srcs_ok(Con{a, b}), h)

def w5_tl(+eof: Bool, +E0: Bool, +x: String, +y: String,
  +h: {Bool.or(Bool.not(eof), Bool.and(E0, S.ends_lf(String.append(x, y)))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(E0, S.ends_lf(y))) == True{} : Bool}:
  match eof:
    case False{}:
      {==}
    case True{}:
      W.and_tt(E0, S.ends_lf(y), W.and_l(E0, S.ends_lf(String.append(x, y)), h), AS.lf_suf(x, y, W.and_r(E0, S.ends_lf(String.append(x, y)), h)))

def lt2(+m: Nat) -> {Nat.is_lt(m, Nat.add(2n, m)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      lt2(p)

# The state with the line taken off is good.
def wf_sl(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool}) ->
  {S.WF(fa, SO(o, s, qs, ql, rest, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool}:
  +pp = SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)
  +p2 = SO(o, s, qs, ql, rest, pd, eof, 0n, wp, None{}, False{})
  +hc = wfC(fa, pp, hw)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +E0 = String.is_empty(P.pdtext(pd))
  Equal.trans(Bool, S.WF(fa, p2), W.C9(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2)), True{}, W.wf_c9(fa, p2),
    W.c9_mk(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2),
      W.c9_0(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      srcs_tl(P.SLP{q}, rest, W.c9_1(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_2(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_3(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.or_r(S.src_empty(rest), E0, W.c9_4(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      w5_tl(eof, E0, String.append(q, "\n"), P.srcstext(rest), W.c9_5(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_7(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_8(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)))

def ms_sl.k(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hsl: {P.src_ok(P.SLP{q}) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  msline(fa, T, cs, O, N, o, s, qs, ql, q, Con{P.SLP{q}, rest}, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx,
    PN.str_assoc(q, "\n", P.srcstext(rest)),
    W.and_r(E.is_bytes(q), P.nolf(q), hsl), W.and_l(E.is_bytes(q), P.nolf(q), hsl),
    wf_sl(fa, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hw), hw, lt2(S.msrc(rest)))

# The String mode, a text line (proof_b_adv.bend's adv.ms.sl).
def ms_sl(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, CD.mkWin(fa, wp))):
  +pp = SO(o, s, qs, ql, Con{P.SLP{q}, rest}, pd, eof, back, wp, asked, fneed)
  +hc = wfC(fa, pp, hw)
  ms_sl.k(fa, T, cs, O, N, o, s, qs, ql, q, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx,
    src_hd(P.SLP{q}, rest, W.c9_1(W.W0(fa, pp), W.W1(fa, pp), W.W2(fa, pp), W.W3(fa, pp), W.W4(fa, pp), W.W5(fa, pp), W.W6(fa, pp), W.W7(fa, pp), W.W8(fa, pp), hc)))

# ---------------------------------------------------------------------------
# adv.ms.sb: a byte source. No LF left: its bytes go to the line end (as
# proof_b_adv_part.bend's DP.* for the byte mode). Else the line before the
# LF is decoded and handled as a text line (msline).
# ---------------------------------------------------------------------------

def meas_drop2(+x: Nat, +m: Nat) -> {Nat.is_lt(m, Nat.add(Nat.add(x, 2n), m)) == True{} : Bool}:
  +K = Nat.add(x, 2n)
  +lt1 = {%Equal.sym(Bool, Nat.is_lt(m, 1n+m), Nat.is_le(m, m), N.lt_succ_iff(m, m)) : {_ == True{} : Bool}; N.le_refl(m) : {Nat.is_lt(m, Nat.add(1n, m)) == True{} : Bool}}
  +le1 = N.le_add_mono_r(m, 1n, K, N.le_trans(1n, 2n, K, {==}, N.le_add_l(2n, x)))
  N.lt_le_trans(m, Nat.add(1n, m), Nat.add(K, m), lt1, le1)

# The dropped text is empty.
def MP.e(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String},
  +hE: {String.is_empty(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), P.mkPd(pd2), eof, back, CD.mkWin(fa, wp), None{}, fneed2}}):
  +p = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MSP{s, qs, ql, None{}})
  +hS = DPT.empty_eq(P.srctext(P.SBP{len, t, d, at}), hE)
  +hA = Equal.trans(String, P.btext(len, t, at, (len - at : U32)), P.srctext(P.SBP{len, t, d, at}), "", Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa), hS)
  +q = {S.StP{o, S.MSP{s, qs, ql, None{}}, rest, pd2, eof, back, wp, None{}, fneed2} : S.StP}
  +h3 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {P.nolf(_) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {P.nolf(String.append(P.pdtext(pd), _)) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), DPT.s_app_nil(P.pdtext(pd))) : {P.nolf(_) == True{} : Bool};
    W.c9_3(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {P.nolf(P.pdtext(pd2)) == True{} : Bool}}
  +hpe = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.is_empty(_) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {String.is_empty(String.append(P.pdtext(pd), _)) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), DPT.s_app_nil(P.pdtext(pd))) : {String.is_empty(_) == True{} : Bool};
    W.c9_4(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {String.is_empty(P.pdtext(pd2)) == True{} : Bool}}
  +h5 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(_), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(String.append(P.pdtext(pd), _)), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), DPT.s_app_nil(P.pdtext(pd))) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(_), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %hS : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(_, P.srcstext(rest))))) == True{} : Bool};
    W.c9_5(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd2)), S.ends_lf(P.srcstext(rest)))) == True{} : Bool}}
  +eqi = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {String.append(P.srcstext(rest), String.append(String.append(P.pdtext(pd), _), S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), DPT.s_app_nil(P.pdtext(pd))) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), "", hS) : {String.append(P.srcstext(rest), String.append(P.pdtext(pd), S.concat_if(eof, cs))) == String.append(String.append(_, P.srcstext(rest)), String.append(P.pdtext(pd), S.concat_if(eof, cs))) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  (q, ({==}, (W.c9_mk(m0, W.W1(fa, q), W.W2(fa, q), W.W3(fa, q), W.W4(fa, q), W.W5(fa, q), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p),
      W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), DPT.srcs_tl(rest, P.SBP{len, t, d, at}, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)), hpd2, h3, W.or_r(S.src_empty(rest), String.is_empty(P.pdtext(pd2)), hpe), h5, W.c9_6(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)),
    (Equal.trans(R.Report, S.report(fa, cs, O, N, q), S.report(fa, cs, O, N, p), T,
      Equal.cong(String, R.Report, z => R.finish(L.run.go(B.Text.lines(z), fa, o, S.pre(O, N, S.smd(S.MSP{s, qs, ql, None{}})))), S.intext(q, cs), S.intext(p, cs), eqi), hr),
    (meas_drop2(LI.n((len - at : U32)), S.msrc(rest)), ({==}, ({==}, (hg, ({==}, (Unit{}, Unit{}))))))))))

# The last source, before the end: pend was empty and takes its text.
def MP.nn(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, False{}, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, False{}, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, False{}, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, False{}, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, Nil{}, P.mkPd(pd2), False{}, back, CD.mkWin(fa, wp), None{}, fneed2}}):
  +p = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, False{}, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MSP{s, qs, ql, None{}})
  +hP = DPT.empty_eq(P.pdtext(pd), W.c9_4(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +q = {S.StP{o, S.MSP{s, qs, ql, None{}}, Nil{}, pd2, False{}, back, wp, None{}, fneed2} : S.StP}
  +hnA = {%hsa : {P.nolf(_) == True{} : Bool}; hn : {P.nolf(P.btext(len, t, at, (len - at : U32))) == True{} : Bool}}
  +h3 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {P.nolf(_) == True{} : Bool};
    LS.nolf_app(P.pdtext(pd), P.btext(len, t, at, (len - at : U32)), W.c9_3(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), hnA) : {P.nolf(P.pdtext(pd2)) == True{} : Bool}}
  +Y0 = S.concat_if(False{}, cs)
  +eqi = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(_, Y0) == S.intext(p, cs) : String};
    %Equal.sym(String, P.pdtext(pd), "", hP) : {String.append(String.append(_, P.btext(len, t, at, (len - at : U32))), Y0) == String.append(String.append(P.srctext(P.SBP{len, t, d, at}), ""), String.append(_, Y0)) : String};
    %Equal.sym(String, String.append(P.srctext(P.SBP{len, t, d, at}), ""), P.srctext(P.SBP{len, t, d, at}), DPT.s_app_nil(P.srctext(P.SBP{len, t, d, at}))) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  (q, ({==}, (W.c9_mk(m0, W.W1(fa, q), W.W2(fa, q), W.W3(fa, q), W.W4(fa, q), W.W5(fa, q), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p),
      W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), {==}, hpd2, h3, {==}, {==}, W.c9_6(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)),
    (Equal.trans(R.Report, S.report(fa, cs, O, N, q), S.report(fa, cs, O, N, p), T,
      Equal.cong(String, R.Report, z => R.finish(L.run.go(B.Text.lines(z), fa, o, S.pre(O, N, S.smd(S.MSP{s, qs, ql, None{}})))), S.intext(q, cs), S.intext(p, cs), eqi), hr),
    (meas_drop2(LI.n((len - at : U32)), 0n), ({==}, ({==}, (hg, ({==}, (Unit{}, Unit{}))))))))))

def MP.n(+eof: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, Nil{}, P.mkPd(pd2), eof, back, CD.mkWin(fa, wp), None{}, fneed2}}):
  match eof:
    case False{}:
      MP.nn(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)
    case True{}:
      +p = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Nil{}}, pd, True{}, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MSP{s, qs, ql, None{}})
      +hl0 = W.and_r(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(P.srctext(P.SBP{len, t, d, at}), "")), W.c9_5(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
      +hlS = {%DPT.s_app_nil(P.srctext(P.SBP{len, t, d, at})) : {S.ends_lf(_) == True{} : Bool}; hl0 : {S.ends_lf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}}
      MP.e(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, Nil{}, pd, True{}, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx, AS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))

def MP.r(+rest: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), P.mkPd(pd2), eof, back, CD.mkWin(fa, wp), None{}, fneed2}}):
  match rest:
    case Nil{}:
      MP.n(eof, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)
    case Con{+sp2, +r2}:
      +p = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, Con{sp2, r2}}, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MSP{s, qs, ql, None{}})
      +hlS = W.and_r(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at})), W.and_l(Bool.and(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at}))), S.srcs_ok(Con{sp2, r2}), W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)))
      MP.e(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, Con{sp2, r2}, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx, AS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))

def MP.pa(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  pa: DPT.PAW(pd, len, t, at)) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, CD.mkWin(fa, wp), None{}, fneed2}}):
  match pa:
    case (+pd2, q):
      match q:
        case (eadd, q2):
          match q2:
            case (hpd2, htx):
              %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) :
                S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed), Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(rest), _, eof, back, CD.mkWin(fa, wp), None{}, fneed2}})
              MP.r(rest, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)

def MP.sn(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  sn: DPT.SNW(len, t, d, at)) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.part.len(o, s, qs, ql, at, (C.BT(len, t), len), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed2)):
  match sn:
    case (hn, hsa):
      +p = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MSP{s, qs, ql, None{}})
      +hfit = {%Equal.sym(Nat, LI.n((len - at : U32)), Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(len), LI.n(at))), LI.n(len), N.le_sub_add(LI.n(at), LI.n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
        N.le_refl(LI.n(len)) : {Nat.is_le(Nat.add(LI.n(at), LI.n((len - at : U32))), LI.n(len)) == True{} : Bool}}
      MP.pa(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, LN.pend_add(pd, len, t, d, at, (len - at : U32), W.c9_2(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), hok, hfit))

# Bytes s .. s+k-1 as text (as proof_b_adv_dec.bend's text_eq).
def sb_text(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +k: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(LI.n(s), LI.n(k)), LI.n(len)) == True{} : Bool}) ->
  {Norm.text(C.BT(len, t), s, k) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}:
  +SN = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(len, t), s, k))
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(len, t), s, k), (C.BT(len, t), SN), SM.to_list_pair_t(len, t, s, k)) :
    {Norm.text.k(_) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  %Equal.sym(List<&2, U32>, SN, D.slice(D.view(C.BT(len, t)), LI.n(s), LI.n(k)), SM.to_list_view_t(len, t, d, s, k, h, hs)) :
    {(C.BT(len, t), Norm.chars(_)) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  %Equal.sym(String, Norm.chars(D.slice(D.view(C.BT(len, t)), LI.n(s), LI.n(k))), NR.chars(D.slice(D.view(C.BT(len, t)), LI.n(s), LI.n(k))), LS.chars_norm(D.slice(D.view(C.BT(len, t)), LI.n(s), LI.n(k)))) :
    {(C.BT(len, t), _) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  {==}

# The line's LF j lies in at .. len (as proof_b_adv_dec.bend's j_range, j_lt).
def sb_jr(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}) ->
  {Bool.and(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len))) == True{} : Bool}:
  %Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf) : {Bool.and(Nat.is_le(LI.n(at), _), Nat.is_le(_, LI.n(len))) == True{} : Bool}
  BL.first_range(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10, LI.u2n(at, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(LI.n(len), _) == True{} : Bool}; N.le_refl(LI.n(len)))

def sb_jlt(+len: U32, +j: U32, +hle: {Nat.is_le(LI.n(j), LI.n(len)) == True{} : Bool}, +hne: {U32.is_eq(j, len) == False{} : Bool}) ->
  {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool}:
  %N.le_succ_lt(LI.n(j), LI.n(len)) : {_ == True{} : Bool}
  PB.le_ne(LI.n(j), LI.n(len), hle, %U.is_eq_to_nat(j, len) : {_ == False{} : Bool}; hne)

# The source's text: the line, its LF, the source past it.
def hst_sb(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +hsp: LI.SPLIT(len, t, d, at, j)) ->
  {P.srcstext(Con{P.SBP{len, t, d, at}, rest}) == String.append(P.btext(len, t, at, (j - at : U32)), String.append("\n", P.srcstext(Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}))) : String}:
  +A = P.btext(len, t, at, (j - at : U32))
  +S1 = P.srctext(P.SBP{len, t, d, (j + 1 : U32)})
  +R0 = P.srcstext(rest)
  %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), String.append(A, String.append("\n", S1)), hsp) :
    {String.append(_, R0) == String.append(A, String.append("\n", String.append(S1, R0))) : String}
  Equal.trans(String, String.append(String.append(A, String.append("\n", S1)), R0), String.append(A, String.append(String.append("\n", S1), R0)), String.append(A, String.append("\n", String.append(S1, R0))),
    PN.str_assoc(A, String.append("\n", S1), R0),
    Equal.cong(String, String, z => String.append(A, z), String.append(String.append("\n", S1), R0), String.append("\n", String.append(S1, R0)), PN.str_assoc("\n", S1, R0)))

# The state with the source past the line is good.
def wf2_sb(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool}) ->
  {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool}:
  +pp = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +p2 = SO(o, s, qs, ql, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, 0n, wp, None{}, False{})
  +hc = wfC(fa, pp, hw)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  Equal.trans(Bool, S.WF(fa, p2), W.C9(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2)), True{}, W.wf_c9(fa, p2),
    W.c9_mk(W.W0(fa, p2), W.W1(fa, p2), W.W2(fa, p2), W.W3(fa, p2), W.W4(fa, p2), W.W5(fa, p2), W.W6(fa, p2), W.W7(fa, p2), W.W8(fa, p2),
      W.c9_0(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      LI.srcs_next(rest, len, t, d, at, j, hsp, hle, W.c9_1(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_2(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_3(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_4(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      LI.eof_next(eof, rest, pd, len, t, d, at, j, hsp, W.c9_5(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_6(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_7(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      W.c9_8(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)))

# A text line ends with an LF.
def lf_end(+q: String) -> {S.ends_lf(String.append(q, "\n")) == True{} : Bool}:
  +A = String.append(q, "\n")
  %Equal.sym(Bool, S.ends_lf(A), Bool.or(String.is_empty(A), AS.ends_nl(A)), AS.lf_eq(A)) : {_ == True{} : Bool}
  %Equal.sym(Bool, AS.ends_nl(A), AS.ends_nl("\n"), AS.nl_app(q, "\n", {==})) : {Bool.or(String.is_empty(A), _) == True{} : Bool}
  W.or_r(String.is_empty(A), AS.ends_nl("\n"), {==})

def sl_cons(+q: String, +src2: List<&2, P.SrcP>, +hsl: {P.src_ok(P.SLP{q}) == True{} : Bool}, +hs2: {S.srcs_ok(src2) == True{} : Bool}) ->
  {S.srcs_ok(Con{P.SLP{q}, src2}) == True{} : Bool}:
  match src2:
    case Nil{}:
      hsl
    case Con{+a, +b}:
      W.and_tt(Bool.and(P.src_ok(P.SLP{q}), S.ends_lf(P.srctext(P.SLP{q}))), S.srcs_ok(Con{a, b}),
        W.and_tt(P.src_ok(P.SLP{q}), S.ends_lf(P.srctext(P.SLP{q})), hsl, lf_end(q)), hs2)

def st_eq(+src: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>, +q: String,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String}) ->
  {P.srcstext(src) == P.srcstext(Con{P.SLP{q}, src2}) : String}:
  Equal.trans(String, P.srcstext(src), String.append(q, String.append("\n", P.srcstext(src2))), P.srcstext(Con{P.SLP{q}, src2}), hst,
    Equal.sym(String, String.append(String.append(q, "\n"), P.srcstext(src2)), String.append(q, String.append("\n", P.srcstext(src2))), PN.str_assoc(q, "\n", P.srcstext(src2))))

def w5_3(+eof: Bool, +E0: Bool, +src: List<&2, P.SrcP>, +q: String, +src2: List<&2, P.SrcP>,
  +hst: {P.srcstext(src) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +h5: {Bool.or(Bool.not(eof), Bool.and(E0, S.ends_lf(P.srcstext(src)))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(E0, S.ends_lf(P.srcstext(Con{P.SLP{q}, src2})))) == True{} : Bool}:
  %st_eq(src, src2, q, hst) : {Bool.or(Bool.not(eof), Bool.and(E0, S.ends_lf(_))) == True{} : Bool}
  h5

# The state with the line put back in front as a text line is good.
def wf3(+fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +sp0: P.SrcP, +r0: List<&2, P.SrcP>, +src2: List<&2, P.SrcP>,
  +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{sp0, r0}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hw2: {S.WF(fa, SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool},
  +hst: {P.srcstext(Con{sp0, r0}) == String.append(q, String.append("\n", P.srcstext(src2))) : String},
  +hqb: {E.is_bytes(q) == True{} : Bool},
  +hq: {P.nolf(q) == True{} : Bool}) ->
  {S.WF(fa, SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})) == True{} : Bool}:
  +pp = SO(o, s, qs, ql, Con{sp0, r0}, pd, eof, back, wp, asked, fneed)
  +p2 = SO(o, s, qs, ql, src2, pd, eof, 0n, wp, None{}, False{})
  +p3 = SO(o, s, qs, ql, Con{P.SLP{q}, src2}, pd, eof, 0n, wp, None{}, False{})
  +hc = wfC(fa, pp, hw)
  +hc2 = wfC(fa, p2, hw2)
  +a0 = W.W0(fa, pp)
  +a1 = W.W1(fa, pp)
  +a2 = W.W2(fa, pp)
  +a3 = W.W3(fa, pp)
  +a4 = W.W4(fa, pp)
  +a5 = W.W5(fa, pp)
  +a6 = W.W6(fa, pp)
  +a7 = W.W7(fa, pp)
  +a8 = W.W8(fa, pp)
  +b0 = W.W0(fa, p2)
  +b1 = W.W1(fa, p2)
  +b2 = W.W2(fa, p2)
  +b3 = W.W3(fa, p2)
  +b4 = W.W4(fa, p2)
  +b5 = W.W5(fa, p2)
  +b6 = W.W6(fa, p2)
  +b7 = W.W7(fa, p2)
  +b8 = W.W8(fa, p2)
  Equal.trans(Bool, S.WF(fa, p3), W.C9(W.W0(fa, p3), W.W1(fa, p3), W.W2(fa, p3), W.W3(fa, p3), W.W4(fa, p3), W.W5(fa, p3), W.W6(fa, p3), W.W7(fa, p3), W.W8(fa, p3)), True{}, W.wf_c9(fa, p3),
    W.c9_mk(W.W0(fa, p3), W.W1(fa, p3), W.W2(fa, p3), W.W3(fa, p3), W.W4(fa, p3), W.W5(fa, p3), W.W6(fa, p3), W.W7(fa, p3), W.W8(fa, p3),
      W.c9_0(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      sl_cons(q, src2, W.and_tt(E.is_bytes(q), P.nolf(q), hqb, hq), W.c9_1(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2)),
      W.c9_2(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      W.c9_3(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      W.c9_4(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc),
      w5_3(eof, String.is_empty(P.pdtext(pd)), Con{sp0, r0}, q, src2, hst, W.c9_5(a0, a1, a2, a3, a4, a5, a6, a7, a8, hc)),
      W.c9_6(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      W.c9_7(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2),
      W.c9_8(b0, b1, b2, b3, b4, b5, b6, b7, b8, hc2)))

# Less of the source is left past the line.
def meas_sb(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>,
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hat: {U32.is_le(at, len) == True{} : Bool},
  +hinc: {LI.n((j + 1 : U32)) == Nat.add(LI.n(j), 1n) : Nat}) ->
  {Nat.is_lt(S.msrc(Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}), S.msrc(Con{P.SBP{len, t, d, at}, rest})) == True{} : Bool}:
  +M = S.msrc(rest)
  +x1 = LI.n((len - (j + 1 : U32) : U32))
  +x2 = LI.n((len - at : U32))
  +k1 = {%Equal.sym(Nat, x1, Nat.sub(LI.n(len), LI.n((j + 1 : U32))), LP.sub_u(len, (j + 1 : U32), LI.u2n((j + 1 : U32), len, hle))) : {Nat.is_lt(_, x2) == True{} : Bool};
    %Equal.sym(Nat, x2, Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hat))) : {Nat.is_lt(Nat.sub(LI.n(len), LI.n((j + 1 : U32))), _) == True{} : Bool};
    %Equal.sym(Nat, LI.n((j + 1 : U32)), Nat.add(LI.n(j), 1n), hinc) : {Nat.is_lt(Nat.sub(LI.n(len), _), Nat.sub(LI.n(len), LI.n(at))) == True{} : Bool};
    LI.lt_sub1(LI.n(len), LI.n(at), LI.n(j), hal, hlt) : {Nat.is_lt(x1, x2) == True{} : Bool}}
  N.lt_add_mono_r(M, Nat.add(x1, 2n), Nat.add(x2, 2n), N.lt_add_mono_r(2n, x1, x2, k1))

# The decoded line, handled as a text line.
def sb_line(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp))):
  +A = P.btext(len, t, at, (j - at : U32))
  +hfit = {%Equal.sym(Nat, LI.n((j - at : U32)), Nat.sub(LI.n(j), LI.n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(LI.n(at), _), LI.n(len)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(LI.n(at), Nat.sub(LI.n(j), LI.n(at))), LI.n(j), N.le_sub_add(LI.n(at), LI.n(j), hal)) : {Nat.is_le(_, LI.n(len)) == True{} : Bool};
    N.lt_to_le(LI.n(j), LI.n(len), hlt) : {Nat.is_le(Nat.add(LI.n(at), LI.n((j - at : U32))), LI.n(len)) == True{} : Bool}}
  +hw2 = wf2_sb(fa, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hsp, hle)
  +hst = hst_sb(len, t, d, at, j, rest, hsp)
  +hw3 = wf3(fa, o, s, qs, ql, A, P.SBP{len, t, d, at}, rest, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed, hw, hw2, hst, hby, hn)
  +hm2 = meas_sb(len, t, d, at, j, rest, hal, hlt, hle, hs, LP.inc_len(len, t, d, j, hok, hlt))
  %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), A), sb_text(len, t, d, at, (j - at : U32), hok, hfit)) :
    S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
      Norm.ms.sb.k(o, s, qs, ql, at, j, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp)))
  msline(fa, T, cs, O, N, o, s, qs, ql, A, Con{P.SBP{len, t, d, at}, rest}, Con{P.SBP{len, t, d, (j + 1 : U32)}, rest}, pd, eof, back, wp, asked, fneed,
    hb, hw, hr, hg, hx, hst, hn, hby, hw2, hw3, hm2)

def sb_split(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(j), LI.n(len)) == True{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool}))) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb.k(o, s, qs, ql, at, j, Norm.text(C.BT(len, t), at, (j - at : U32)), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp))):
  (hsp, q) = sl
  (hn, q2) = q
  (hle, hby) = q2
  sb_line(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hok, hs, hal, hlt, hsp, hn, hle, hby)

def sb_if(+part: Bool, +j: U32, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb.if(part, o, s, qs, ql, C.BT(len, t), at, j, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed)):
  match part:
    case True{}:
      +hjl = {%U.is_eq_true(j, len, ep) : {LI.n(_) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}; hjf : {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat}}
      MP.sn(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hw, hr, hg, hok, hs,
        LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjl)))
    case False{}:
      +hjr = sb_jr(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr)
      +hlt = sb_jlt(len, j, W.and_r(Nat.is_le(LI.n(at), LI.n(j)), Nat.is_le(LI.n(j), LI.n(len)), hjr), ep)
      sb_split(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hok, hs, hal, hlt,
        LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf), hlt))

def SBW(+len: U32, +t: AT.Tree<U32>, +at: U32) -> Type:
  &j: U32 -> ({NF.lf(C.BT(len, t), at) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
  & {LI.n(j) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat})

def sb_j(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: SBW(len, t, at)) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed)):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, LI.n(j), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
              Norm.ms.sb(o, s, qs, ql, at, _, P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed))
          sb_if(U32.is_eq(j, len), j, fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hok, hs, hjf, {==})

# The String mode, a byte source (proof_b_adv.bend's adv.ms.sb).
def ms_sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {R.RunSt.halt(s) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed),
    Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, CD.mkWin(fa, wp), fneed)):
  +pp = SO(o, s, qs, ql, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)
  +hc = wfC(fa, pp, hw)
  +hso = LI.srcs_head(rest, len, t, d, at, W.c9_1(W.W0(fa, pp), W.W1(fa, pp), W.W2(fa, pp), W.W3(fa, pp), W.W4(fa, pp), W.W5(fa, pp), W.W6(fa, pp), W.W7(fa, pp), W.W8(fa, pp), hc))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  sb_j(fa, T, cs, O, N, o, s, qs, ql, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hok, hs, LN.lf_ok(len, t, d, at, hok, hs))
