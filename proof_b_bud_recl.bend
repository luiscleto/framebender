import Base
import ./types.bend as B
import ./run.bend as R
import ./proof_s_cr.bend as CR
import ./proof_s_chars.bend as CH
import ./proof_s_str.bend as ST
import ./proof_b_budget_rec.bend as Q
import ./proof_b_budget_dig.bend as G
import ./proof_b_cache_lem.bend as CL
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# The records of a split line (B.Rec.parts' Pieces) are no longer than the
# line's body, and there are no more of them than ALTs (the budget charges
# a split line's output to its own text, proof_b_budget_run.bend's out_len).
# A record keeps CHROM POS ID REF QUAL FILTER FORMAT, takes one ALT (a piece
# of ALT), cuts INFO's and the samples' per-allele values (Vals.pick with
# strictly increasing places: a subsequence) and writes each GT allele as
# one character ("0", "1" or "."; an allele is never empty). Every variable
# is reusable.

def Ss() -> Data:
  List<&2, String>

def SL(+s: String) -> Nat:
  String.length(s)

# ---------------------------------------------------------------------------
# Bounds on what the splitters give
# ---------------------------------------------------------------------------

# A text at most L long (a refusal has no text).
def GLE(g: B.Got, +L: Nat) -> Bool:
  match g:
    case B.Got{s}:
      Nat.is_le(String.length(s), L)
    case B.Refuse{c}:
      True{}

# A text shorter than L.
def GL1(g: B.Got, +L: Nat) -> Bool:
  match g:
    case B.Got{s}:
      Nat.is_le(1n+String.length(s), L)
    case B.Refuse{c}:
      True{}

def MLE(m: Maybe<&2, String>, +L: Nat) -> Bool:
  match m:
    case Some{x}:
      Nat.is_le(String.length(x), L)
    case None{}:
      True{}

# A value shorter than L.
def MB(m: Maybe<&2, String>, +L: Nat) -> Bool:
  match m:
    case Some{x}:
      Nat.is_le(1n+String.length(x), L)
    case None{}:
      True{}

# Values whose SN is at most L.
def LB(m: Maybe<&2, Ss()>, +L: Nat) -> Bool:
  match m:
    case Some{xs}:
      Nat.is_le(Q.SN(xs), L)
    case None{}:
      True{}

# The texts gs, each at most as long as the text in the same place of xs,
# no more of them than xs.
def LEP(gs: List<&2, B.Got>, xs: Ss()) -> Bool:
  match gs xs:
    case Nil{} _:
      True{}
    case g <> gt Nil{}:
      False{}
    case g <> gt +x <> xt:
      GLE(g, String.length(x)) && LEP(gt, xt)

# Every text shorter than L.
def PLE1(gs: List<&2, B.Got>, +L: Nat) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> t:
      GL1(g, L) && PLE1(t, L)

def RLT(xs: Ss(), +L: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(1n+String.length(x), L) && RLT(t, L)

# Every text at most L long.
def RLE(xs: Ss(), +L: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(String.length(x), L) && RLE(t, L)

def sn_le(+x: String, +t: Ss()) -> {Nat.is_le(Q.SN(t), Q.SN(x <> t)) == True{} : Bool}:
  N.le_trans(Q.SN(t), Nat.add(SL(x), Q.SN(t)), 1n+Nat.add(SL(x), Q.SN(t)), N.le_add_l(Q.SN(t), SL(x)), N.le_add_l(Nat.add(SL(x), Q.SN(t)), 1n))

def mb_mono(m: Maybe<&2, String>, +a: Nat, +b: Nat, +h: {MB(m, a) == True{} : Bool}, +hab: {Nat.is_le(a, b) == True{} : Bool}) -> {MB(m, b) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      N.le_trans(1n+SL(x), a, b, h, hab)

def lb_mono(m: Maybe<&2, Ss()>, +a: Nat, +b: Nat, +h: {LB(m, a) == True{} : Bool}, +hab: {Nat.is_le(a, b) == True{} : Bool}) -> {LB(m, b) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+xs}:
      N.le_trans(Q.SN(xs), a, b, h, hab)

law rlt_mono:
  for +xs: Ss()
  for +a: Nat
  for +b: Nat
  for +h: {RLT(xs, a) == True{} : Bool}
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  {RLT(xs, b) == True{} : Bool}

def rlt_mono(xs, a, b, h, hab):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      CH.and_tt(Nat.is_le(1n+SL(x), b), RLT(t, b), N.le_trans(1n+SL(x), a, b, AB.and_true_l(Nat.is_le(1n+SL(x), a), RLT(t, a), h), hab),
        rlt_mono(t, a, b, AB.and_true_r(Nat.is_le(1n+SL(x), a), RLT(t, a), h), hab))

law rlt_rle:
  for +xs: Ss()
  for +L: Nat
  for +h: {RLT(xs, 1n+L) == True{} : Bool}
  {RLE(xs, L) == True{} : Bool}

def rlt_rle(xs, L, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      CH.and_tt(Nat.is_le(SL(x), L), RLE(t, L), AB.and_true_l(Nat.is_le(1n+SL(x), 1n+L), RLT(t, 1n+L), h),
        rlt_rle(t, L, AB.and_true_r(Nat.is_le(1n+SL(x), 1n+L), RLT(t, 1n+L), h)))

# Each text of xs is shorter than SN(xs).
law sn_all:
  for +xs: Ss()
  {RLT(xs, Q.SN(xs)) == True{} : Bool}

def sn_all(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      CH.and_tt(Nat.is_le(1n+SL(x), Q.SN(x <> t)), RLT(t, Q.SN(x <> t)), N.le_add_r(SL(x), Q.SN(t)),
        rlt_mono(t, Q.SN(t), Q.SN(x <> t), sn_all(t), sn_le(x, t)))

def pick_got(+c: Bool, +a: B.Got, +b: B.Got, +L: Nat, +ha: {GLE(a, L) == True{} : Bool}, +hb: {GLE(b, L) == True{} : Bool}) -> {GLE(Bool.pick(B.Got, c, a, b), L) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

def got_of(+m: Maybe<&2, String>, +c: B.Code, +L: Nat, +h: {MLE(m, L) == True{} : Bool}) -> {GLE(B.Got.of(m, c), L) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      h

# |"."| or more: a text equal to ".".
def dot_len(+v: String, +e: {String.eq(v, ".") == True{} : Bool}) -> {Nat.is_le(1n, String.length(v)) == True{} : Bool}:
  match v:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.false_ne_true(e))
    case SCon{+h, +t}:
      N.le_zero_l(SL(t))

# |drop(s, m)| = |s| - m.
law drop_len:
  for +s: String
  for +m: Nat
  {String.length(String.drop(s, m)) == Nat.sub(String.length(s), m) : Nat}

def drop_len(s, m):
  match s m:
    case SNil{} _:
      {==}
    case SCon{+h, +t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      drop_len(t, p)

# ---------------------------------------------------------------------------
# Joining texts no longer than the pieces of a split
# ---------------------------------------------------------------------------

def gle_gl1(+g: B.Got, +a: Nat, +b: Nat, +hg: {GLE(g, a) == True{} : Bool}) -> {GL1(g, 1n+Nat.add(a, b)) == True{} : Bool}:
  match g:
    case B.Got{+s}:
      N.le_trans(SL(s), a, Nat.add(a, b), hg, N.le_add_r(a, b))
    case B.Refuse{+c}:
      {==}

def cat_len(+y: String, +sep: String, +z: String, +hs: {SL(sep) == 1n : Nat}) -> {SL(y ++ (sep ++ z)) == Nat.add(SL(y), 1n+SL(z)) : Nat}:
  Equal.trans(Nat, SL(y ++ (sep ++ z)), Nat.add(SL(y), SL(sep ++ z)), Nat.add(SL(y), 1n+SL(z)), G.slen_app(y, sep ++ z),
    Equal.cong(Nat, Nat, w => Nat.add(SL(y), w), SL(sep ++ z), 1n+SL(z),
      Equal.trans(Nat, SL(sep ++ z), Nat.add(SL(sep), SL(z)), 1n+SL(z), G.slen_app(sep, z),
        Equal.cong(Nat, Nat, w => Nat.add(w, SL(z)), SL(sep), 1n, hs))))

def cat1(+g: B.Got, +sep: String, +r: B.Got, +a: Nat, +M: Nat, +hs: {SL(sep) == 1n : Nat},
  +hg: {GLE(g, a) == True{} : Bool}, +hr: {GL1(r, M) == True{} : Bool}) -> {GL1(B.Got.cat(g, sep, r), 1n+Nat.add(a, M)) == True{} : Bool}:
  match g r:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+y} B.Refuse{+c}:
      {==}
    case B.Got{+y} B.Got{+z}:
      %Equal.sym(Nat, SL(y ++ (sep ++ z)), Nat.add(SL(y), 1n+SL(z)), cat_len(y, sep, z, hs)) : {Nat.is_le(1n+_, 1n+Nat.add(a, M)) == True{} : Bool}
      N.le_trans(Nat.add(SL(y), 1n+SL(z)), Nat.add(a, 1n+SL(z)), Nat.add(a, M), N.le_add_mono_r(1n+SL(z), SL(y), a, hg), N.le_add_mono_l(a, 1n+SL(z), M, hr))

# The texts joined with a one-character separator, against a list that is
# not empty: shorter than its SN.
law jl:
  for +gs: List<&2, B.Got>
  for +x: String
  for +xt: Ss()
  for +sep: String
  for +hs: {SL(sep) == 1n : Nat}
  for +h: {LEP(gs, x <> xt) == True{} : Bool}
  {GL1(B.Got.join(gs, sep), Q.SN(x <> xt)) == True{} : Bool}

def jl(gs, x, xt, sep, hs, h):
  match gs:
    case Nil{}:
      N.le_zero_l(Nat.add(SL(x), Q.SN(xt)))
    case Con{+g, +gt}:
      match gt:
        case Nil{}:
          gle_gl1(g, SL(x), Q.SN(xt), AB.and_true_l(GLE(g, SL(x)), LEP(Nil{}, xt), h))
        case Con{+g2, +gt2}:
          match xt:
            case Nil{}:
              Empty.absurd({GL1(B.Got.join(g <> g2 <> gt2, sep), Q.SN([x])) == True{} : Bool}, AB.false_ne_true(AB.and_true_r(GLE(g, SL(x)), False{}, h)))
            case Con{+x2, +xt2}:
              cat1(g, sep, B.Got.join(g2 <> gt2, sep), SL(x), Q.SN(x2 <> xt2), hs, AB.and_true_l(GLE(g, SL(x)), LEP(g2 <> gt2, x2 <> xt2), h),
                jl(g2 <> gt2, x2, xt2, sep, hs, AB.and_true_r(GLE(g, SL(x)), LEP(g2 <> gt2, x2 <> xt2), h)))

def gl1_le(+g: B.Got, +M: Nat, +L: Nat, +h: {GL1(g, M) == True{} : Bool}, +hL: {M == 1n+L : Nat}) -> {GLE(g, L) == True{} : Bool}:
  match g:
    case B.Got{+s}:
      AB.subst(Nat, z => {Nat.is_le(1n+SL(s), z) == True{} : Bool}, M, 1n+L, hL, h)
    case B.Refuse{+c}:
      {==}

def js.k(+gs: List<&2, B.Got>, +ps: Ss(), +sep: String, +hs: {SL(sep) == 1n : Nat}, +h: {LEP(gs, ps) == True{} : Bool},
  +hc: {ST.is_cons(ps) == True{} : Bool}, +L: Nat, +hL: {Q.SN(ps) == 1n+L : Nat}) -> {GLE(B.Got.join(gs, sep), L) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({GLE(B.Got.join(gs, sep), L) == True{} : Bool}, AB.false_ne_true(hc))
    case Con{+x, +xt}:
      gl1_le(B.Got.join(gs, sep), Q.SN(x <> xt), L, jl(gs, x, xt, sep, hs, h), hL)

# Texts no longer than the pieces of s cut at c, joined with one character:
# no longer than s.
law jsplit:
  for +gs: List<&2, B.Got>
  for +s: String
  for +c: Char
  for +sep: String
  for +hs: {SL(sep) == 1n : Nat}
  for +h: {LEP(gs, String.split(s, c)) == True{} : Bool}
  {GLE(B.Got.join(gs, sep), String.length(s)) == True{} : Bool}

def jsplit(gs, s, c, sep, hs, h):
  js.k(gs, String.split(s, c), sep, hs, h, ST.split_cons(s, c), SL(s), Q.split_sn(s, c))

# ---------------------------------------------------------------------------
# Per-allele values: strictly increasing places keep a subsequence
# ---------------------------------------------------------------------------

law get_mb:
  for +vs: Ss()
  for +k: Nat
  {MB(List.get(&2, String, vs, k), Q.SN(vs)) == True{} : Bool}

def get_mb(vs, k):
  match vs k:
    case Nil{} _:
      {==}
    case Con{+v, +t} 0n:
      N.le_add_r(SL(v), Q.SN(t))
    case Con{+v, +t} 1n+j:
      mb_mono(List.get(&2, String, t, j), Q.SN(t), Q.SN(v <> t), get_mb(t, j), sn_le(v, t))

def cons1(+m: Maybe<&2, String>, +L: Nat, +h: {MB(m, L) == True{} : Bool}) -> {LB(B.Vals.pick.cons(m, Some{Nil{}}), L) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Nat, Nat.add(SL(x), 0n), SL(x), N.add_zero(SL(x))) : {Nat.is_le(1n+_, L) == True{} : Bool}
      h

def cons0(+v: String, +m: Maybe<&2, Ss()>, +L: Nat, +h: {LB(m, L) == True{} : Bool}) -> {LB(B.Vals.pick.cons(Some{v}, m), 1n+Nat.add(SL(v), L)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+xs}:
      N.le_add_mono_l(SL(v), Q.SN(xs), L, h)

def one(+vs: Ss(), +k: Nat) -> {LB(B.Vals.pick(vs, [k]), Q.SN(vs)) == True{} : Bool}:
  cons1(List.get(&2, String, vs, k), Q.SN(vs), get_mb(vs, k))

law two:
  for +vs: Ss()
  for +a: Nat
  for +b: Nat
  for +hab: {Nat.is_lt(a, b) == True{} : Bool}
  {LB(B.Vals.pick(vs, [a, b]), Q.SN(vs)) == True{} : Bool}

def two(vs, a, b, hab):
  match vs a b:
    case Nil{} _ _:
      {==}
    case Con{+v, +t} 0n 0n:
      Empty.absurd({LB(B.Vals.pick(v <> t, [0n, 0n]), Q.SN(v <> t)) == True{} : Bool}, AB.false_ne_true(hab))
    case Con{+v, +t} 0n 1n+b1:
      cons0(v, B.Vals.pick(t, [b1]), Q.SN(t), one(t, b1))
    case Con{+v, +t} 1n+a1 0n:
      Empty.absurd({LB(B.Vals.pick(v <> t, [1n+a1, 0n]), Q.SN(v <> t)) == True{} : Bool}, AB.false_ne_true(hab))
    case Con{+v, +t} 1n+a1 1n+b1:
      lb_mono(B.Vals.pick(t, [a1, b1]), Q.SN(t), Q.SN(v <> t), two(t, a1, b1, hab), sn_le(v, t))

def three(+vs: Ss(), +a: Nat, +b: Nat, +h1: {Nat.is_le(1n, a) == True{} : Bool}, +hab: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {LB(B.Vals.pick(vs, [0n, a, b]), Q.SN(vs)) == True{} : Bool}:
  match vs a b:
    case Nil{} _ _:
      {==}
    case Con{+v, +t} 0n _:
      Empty.absurd({LB(B.Vals.pick(v <> t, [0n, 0n, b]), Q.SN(v <> t)) == True{} : Bool}, AB.false_ne_true(h1))
    case Con{+v, +t} 1n+a1 0n:
      Empty.absurd({LB(B.Vals.pick(v <> t, [0n, 1n+a1, 0n]), Q.SN(v <> t)) == True{} : Bool}, AB.false_ne_true(hab))
    case Con{+v, +t} 1n+a1 1n+b1:
      cons0(v, B.Vals.pick(t, [a1, b1]), Q.SN(t), two(t, a1, b1, hab))

# The diploid places of ALT i >= 1: 0 < i(i+1)/2 < i(i+1)/2 + i.
def gt_d(+i1: Nat) -> Nat:
  Nat.div(Nat.mul(1n+i1, 1n+(1n+i1)), 2n)

def gt_one(+i1: Nat) -> {Nat.is_le(1n, B.Gt.index(0n, 1n+i1)) == True{} : Bool}:
  +Y = Nat.add(i1, Nat.mul(i1, 1n+(1n+i1)))
  %Equal.sym(Nat, Nat.add(gt_d(i1), 0n), gt_d(i1), N.add_zero(gt_d(i1))) : {Nat.is_le(1n, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(1n, 2n), Y), 2n), Nat.add(1n, Nat.div(Y, 2n)), N.div_add_mul(1n, 2n, Y, {==})) : {Nat.is_le(1n, _) == True{} : Bool}
  N.le_zero_l(Nat.div(Y, 2n))

def gt_lt(+i1: Nat) -> {Nat.is_lt(B.Gt.index(0n, 1n+i1), B.Gt.index(1n+i1, 1n+i1)) == True{} : Bool}:
  +D = gt_d(i1)
  %Equal.sym(Nat, Nat.add(D, 0n), D, N.add_zero(D)) : {Nat.is_lt(_, Nat.add(D, 1n+i1)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(D, 1n+i1), 1n+Nat.add(D, i1), N.add_succ(D, i1)) : {Nat.is_lt(D, _) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(D, 1n+Nat.add(D, i1)), Nat.is_le(D, Nat.add(D, i1)), N.lt_succ_iff(D, Nat.add(D, i1))) : {_ == True{} : Bool}
  N.le_add_r(D, i1)

def idx_g(+q: Nat, +i1: Nat, +vs: Ss()) -> {LB(B.Vals.pick(vs, B.Vals.idx(B.NumG{}, q, 1n+i1)), Q.SN(vs)) == True{} : Bool}:
  match q:
    case 0n:
      three(vs, B.Gt.index(0n, 1n+i1), B.Gt.index(1n+i1, 1n+i1), gt_one(i1), gt_lt(i1))
    case 1n:
      two(vs, 0n, 1n+i1, {==})
    case 1n+1n+r:
      three(vs, B.Gt.index(0n, 1n+i1), B.Gt.index(1n+i1, 1n+i1), gt_one(i1), gt_lt(i1))

def idx_lb(+num: B.Num, +q: Nat, +i1: Nat, +vs: Ss()) -> {LB(B.Vals.pick(vs, B.Vals.idx(num, q, 1n+i1)), Q.SN(vs)) == True{} : Bool}:
  match num:
    case B.NumA{}:
      one(vs, Nat.sub(1n+i1, 1n))
    case B.NumR{}:
      two(vs, 0n, 1n+i1, {==})
    case B.NumG{}:
      idx_g(q, i1, vs)
    case B.NumOther{}:
      N.le_zero_l(Q.SN(vs))
    case B.NumUnknown{}:
      N.le_zero_l(Q.SN(vs))

def vjoin(+m: Maybe<&2, Ss()>, +L: Nat, +h: {LB(m, 1n+L) == True{} : Bool}) -> {MLE(B.Vals.join(m), L) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+xs}:
      match xs:
        case Nil{}:
          N.le_zero_l(L)
        case Con{+x, +t}:
          N.le_trans(SL(String.join.go(t, x, ",")), Nat.add(SL(x), Q.SN(t)), L, Q.jg(t, x, ",", {==}), h)

def pick_m(+c: Bool, +m: Maybe<&2, String>, +L: Nat, +h: {MLE(m, L) == True{} : Bool}) -> {MLE(Bool.pick(Maybe<&2, String>, c, m, None{}), L) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

def vkeep(+num: B.Num, +n: Nat, +q: Nat, +i1: Nat, +vs: Ss(), +L: Nat, +hv: {Nat.is_le(Q.SN(vs), 1n+L) == True{} : Bool}) ->
  {MLE(B.Vals.keep(num, n, q, 1n+i1, vs), L) == True{} : Bool}:
  +pk = B.Vals.pick(vs, B.Vals.idx(num, q, 1n+i1))
  pick_m(B.Vals.fits(B.Vals.expected_count(num, n, q), List.length(&2, String, vs)), B.Vals.join(pk), L,
    vjoin(pk, L, lb_mono(pk, Q.SN(vs), 1n+L, idx_lb(num, q, i1, vs), hv)))

def vsplit.k(+miss: Bool, +num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +i1: Nat, +v: String, +e: {String.eq(v, ".") == miss : Bool}) ->
  {MLE(B.Vals.split.if(miss, num, n, cp, 1n+i1, v), String.length(v)) == True{} : Bool}:
  match miss:
    case True{}:
      dot_len(v, e)
    case False{}:
      +vs = String.split(v, ',')
      +hv = AB.subst(Nat, z => {Nat.is_le(z, 1n+SL(v)) == True{} : Bool}, 1n+SL(v), Q.SN(vs), Equal.sym(Nat, Q.SN(vs), 1n+SL(v), Q.split_sn(v, ',')), N.le_refl(1n+SL(v)))
      vkeep(num, n, B.Vals.copies(cp, n, List.length(&2, String, vs)), i1, vs, SL(v), hv)

# A per-allele value, split for ALT i >= 1: no longer than the value.
law vsplit:
  for +num: B.Num
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i1: Nat
  for +v: String
  {MLE(B.Vals.split(num, n, cp, 1n+i1, v), String.length(v)) == True{} : Bool}

def vsplit(num, n, cp, i1, v):
  vsplit.k(String.eq(v, "."), num, n, cp, i1, v, {==})

# ---------------------------------------------------------------------------
# INFO
# ---------------------------------------------------------------------------

def eq_cons(+h: Char, +a: String, +b: String) -> {String.eq(SCon{h, a}, SCon{h, b}) == String.eq(a, b) : Bool}:
  match h:
    case Chr{U32{+w}}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, CL.word_cmp_refl(32n, w)) : {Cmp.is_eq(String.order.go(a, b, _)) == String.eq(a, b) : Bool}
      {==}

def key0(ps: Ss()) -> String:
  B.Rec.field(ps, 0n)

def key_push(+h: Char, +ps: Ss()) -> {key0(String.split.push(h, ps)) == SCon{h, key0(ps)} : String}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      {==}

def key.k(+h: Char, +t: String, +c: Bool,
  +hne: {String.eq(key0(String.split.fin(h, String.split(t, '='), c)), SCon{h, t}) == False{} : Bool},
  ih: {String.eq(key0(String.split(t, '=')), t) == False{} : Bool} -> {Nat.is_le(Nat.add(SL(key0(String.split(t, '='))), 1n), SL(t)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(SL(key0(String.split.fin(h, String.split(t, '='), c))), 1n), 1n+SL(t)) == True{} : Bool}:
  match c:
    case True{}:
      N.le_zero_l(SL(t))
    case False{}:
      +ps = String.split(t, '=')
      +ek = key_push(h, ps)
      +hne2 = Equal.trans(Bool, String.eq(key0(ps), t), String.eq(SCon{h, key0(ps)}, SCon{h, t}), False{},
        Equal.sym(Bool, String.eq(SCon{h, key0(ps)}, SCon{h, t}), String.eq(key0(ps), t), eq_cons(h, key0(ps), t)),
        AB.subst(String, z => {String.eq(z, SCon{h, t}) == False{} : Bool}, key0(String.split.push(h, ps)), SCon{h, key0(ps)}, ek, hne))
      %Equal.sym(String, key0(String.split.push(h, ps)), SCon{h, key0(ps)}, ek) : {Nat.is_le(Nat.add(SL(_), 1n), 1n+SL(t)) == True{} : Bool}
      ih(hne2)

# An INFO entry other than its key holds '=' after it: |key| < |entry|.
law key_lt:
  for +e: String
  for +hne: {String.eq(B.Info.key(e), e) == False{} : Bool}
  {Nat.is_le(Nat.add(String.length(B.Info.key(e)), 1n), String.length(e)) == True{} : Bool}

def key_lt(e, hne):
  match e:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.true_ne_false(hne))
    case SCon{+h, +t}:
      key.k(h, t, Char.is_eq(h, '='), hne, hn => key_lt(t, hn))

def ieq_k(+k: String, +e: String, +mv: Maybe<&2, String>,
  +hm: {MLE(mv, SL(String.drop(e, Nat.add(SL(k), 1n)))) == True{} : Bool},
  +hk: {Nat.is_le(Nat.add(SL(k), 1n), SL(e)) == True{} : Bool}) ->
  {GLE(B.Got.cat(B.Got{k}, "=", B.Got.of(mv, B.BadCount{})), SL(e)) == True{} : Bool}:
  match mv:
    case None{}:
      {==}
    case Some{+x}:
      +K1 = Nat.add(SL(k), 1n)
      +e1 = Equal.trans(Nat, SL(k ++ ("=" ++ x)), Nat.add(SL(k), 1n+SL(x)), Nat.add(K1, SL(x)), cat_len(k, "=", x, {==}),
        Equal.sym(Nat, Nat.add(K1, SL(x)), Nat.add(SL(k), Nat.add(1n, SL(x))), N.add_assoc(SL(k), 1n, SL(x))))
      +hx = AB.subst(Nat, z => {Nat.is_le(SL(x), z) == True{} : Bool}, SL(String.drop(e, K1)), Nat.sub(SL(e), K1), drop_len(e, K1), hm)
      %Equal.sym(Nat, SL(k ++ ("=" ++ x)), Nat.add(K1, SL(x)), e1) : {Nat.is_le(_, SL(e)) == True{} : Bool}
      %N.le_sub_add(K1, SL(e), hk) : {Nat.is_le(Nat.add(K1, SL(x)), _) == True{} : Bool}
      N.le_add_mono_l(K1, SL(x), Nat.sub(SL(e), K1), hx)

def ieq.num(+num: B.Num, +k: String, +e: String, +n: Nat, +i1: Nat, +hk: {Nat.is_le(Nat.add(SL(k), 1n), SL(e)) == True{} : Bool}) ->
  {GLE(B.Info.split.eq(Some{num}, k, e, n, 1n+i1), SL(e)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      N.le_refl(SL(e))
    case B.NumA{}:
      ieq_k(k, e, B.Vals.split(B.NumA{}, n, Some{2n}, 1n+i1, String.drop(e, Nat.add(SL(k), 1n))), vsplit(B.NumA{}, n, Some{2n}, i1, String.drop(e, Nat.add(SL(k), 1n))), hk)
    case B.NumR{}:
      ieq_k(k, e, B.Vals.split(B.NumR{}, n, Some{2n}, 1n+i1, String.drop(e, Nat.add(SL(k), 1n))), vsplit(B.NumR{}, n, Some{2n}, i1, String.drop(e, Nat.add(SL(k), 1n))), hk)
    case B.NumG{}:
      ieq_k(k, e, B.Vals.split(B.NumG{}, n, Some{2n}, 1n+i1, String.drop(e, Nat.add(SL(k), 1n))), vsplit(B.NumG{}, n, Some{2n}, i1, String.drop(e, Nat.add(SL(k), 1n))), hk)

def ieq(+m: Maybe<&2, B.Num>, +k: String, +e: String, +n: Nat, +i1: Nat, +hk: {Nat.is_le(Nat.add(SL(k), 1n), SL(e)) == True{} : Bool}) ->
  {GLE(B.Info.split.eq(m, k, e, n, 1n+i1), SL(e)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      ieq.num(num, k, e, n, i1, hk)

def inum.k(+m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i1: Nat, +c: Bool, +ec: {String.eq(B.Info.key(e), e) == c : Bool}) ->
  {GLE(Bool.pick(B.Got, c, Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, B.Info.key(e), e, n, 1n+i1)), SL(e)) == True{} : Bool}:
  match c:
    case True{}:
      pick_got(B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}, SL(e), {==}, N.le_refl(SL(e)))
    case False{}:
      ieq(m, B.Info.key(e), e, n, i1, key_lt(e, ec))

def inum(+m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i1: Nat) -> {GLE(B.Info.split.num(m, e, n, 1n+i1), SL(e)) == True{} : Bool}:
  inum.k(m, e, n, i1, String.eq(B.Info.key(e), e), {==})

law igo:
  for +es: Ss()
  for +info: List<&2, B.Tag>
  for +n: Nat
  for +i1: Nat
  {LEP(B.Info.split.go(es, info, n, 1n+i1), es) == True{} : Bool}

def igo(es, info, n, i1):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      CH.and_tt(GLE(B.Info.split.num(B.Tags.find(info, B.Info.key(e)), e, n, 1n+i1), SL(e)), LEP(B.Info.split.go(t, info, n, 1n+i1), t),
        inum(B.Tags.find(info, B.Info.key(e)), e, n, i1), igo(t, info, n, i1))

# INFO in the record for ALT i >= 1: no longer than INFO.
law info_len:
  for +info: String
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i1: Nat
  {GLE(B.Info.split(info, tags, n, 1n+i1), String.length(info)) == True{} : Bool}

def info_len(info, tags, n, i1):
  jsplit(B.Info.split.go(String.split(info, ';'), tags, n, 1n+i1), info, ';', ";", {==}, igo(String.split(info, ';'), tags, n, i1))

# ---------------------------------------------------------------------------
# GT and FORMAT
# ---------------------------------------------------------------------------

# A genotype allele written: one character.
def rule1(+c1: Bool, +c2: Bool, +c3: Bool, +L: Nat, +h: {Nat.is_le(1n, L) == True{} : Bool}) ->
  {Nat.is_le(SL(B.Gt.show(Bool.pick(Maybe<&2, Nat>, c1, Some{0n}, Bool.pick(Maybe<&2, Nat>, c2, Some{1n}, Bool.pick(Maybe<&2, Nat>, c3, Some{0n}, None{}))))), L) == True{} : Bool}:
  match c1 c2 c3:
    case True{} _ _:
      h
    case False{} True{} _:
      h
    case False{} False{} True{}:
      h
    case False{} False{} False{}:
      h

def gnum(+m: Maybe<&2, Nat>, +over0: Bool, +n: Nat, +i: Nat, +L: Nat, +h: {Nat.is_le(1n, L) == True{} : Bool}) -> {GLE(B.Gt.num(m, over0, n, i), L) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+a}:
      pick_got(Nat.is_le(a, n), B.Got{B.Gt.show(B.Gt.rule(over0, i, Some{a}))}, B.Refuse{B.BadGt{}}, L,
        rule1(Nat.is_eq(a, 0n), Nat.is_eq(a, i), over0, L, h), {==})

def ne_len(+a: String, +h: {Bool.not(String.is_empty(a)) == True{} : Bool}) -> {Nat.is_le(1n, String.length(a)) == True{} : Bool}:
  match a:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case SCon{+c, +t}:
      N.le_zero_l(SL(t))

def ga.c(+over0: Bool, +n: Nat, +i: Nat, +a: String, +c: Bool, +e: {B.Gt.canon(a) == c : Bool}) ->
  {GLE(Bool.pick(B.Got, c, B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}}), SL(a)) == True{} : Bool}:
  match c:
    case True{}:
      +ne = Bool.not(String.is_empty(a))
      gnum(B.Pos.read(a), over0, n, i, SL(a), ne_len(a, AB.and_true_l(ne, B.Text.all_digits(a), AB.and_true_l(Bool.and(ne, B.Text.all_digits(a)), Bool.or(String.eq(a, "0"), Bool.not(String.starts_with(a, "0"))), e))))
    case False{}:
      {==}

def ga.k(+over0: Bool, +n: Nat, +i: Nat, +a: String, +c: Bool, +e: {String.eq(a, ".") == c : Bool}) ->
  {GLE(Bool.pick(B.Got, c, B.Got{"."}, Bool.pick(B.Got, B.Gt.canon(a), B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}})), SL(a)) == True{} : Bool}:
  match c:
    case True{}:
      dot_len(a, e)
    case False{}:
      ga.c(over0, n, i, a, B.Gt.canon(a), {==})

# A genotype allele in the record: no longer than the allele read.
def gallele(+over0: Bool, +n: Nat, +i: Nat, +a: String) -> {GLE(B.Gt.allele(over0, n, i, a), SL(a)) == True{} : Bool}:
  ga.k(over0, n, i, a, String.eq(a, "."), {==})

# A genotype read from the right: the first allele's text and the rest
# written fit in what was read.
def GPL(r: B.Gp, +L: Nat) -> Bool:
  match r:
    case B.Gp{+tk, rs}:
      match rs:
        case B.Got{x}:
          Nat.is_le(Nat.add(String.length(tk), String.length(x)), L)
        case B.Refuse{c}:
          True{}

def app_le(+y: String, +z: String, +a: Nat, +L: Nat, +hy: {Nat.is_le(SL(y), a) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(a, SL(z)), L) == True{} : Bool}) ->
  {Nat.is_le(SL(y ++ z), L) == True{} : Bool}:
  %Equal.sym(Nat, SL(y ++ z), Nat.add(SL(y), SL(z)), G.slen_app(y, z)) : {Nat.is_le(_, L) == True{} : Bool}
  N.le_trans(Nat.add(SL(y), SL(z)), Nat.add(a, SL(z)), L, N.le_add_mono_r(SL(z), SL(y), a, hy), hr)

def gp.k(+h: Char, +tk: String, +ga: B.Got, +rs: B.Got, +L: Nat, +hy: {GLE(ga, SL(tk)) == True{} : Bool}, +hr: {GPL(B.Gp{tk, rs}, L) == True{} : Bool}) ->
  {GPL(B.Gp{"", B.Got.cat(B.Got.cat(B.Got{SCon{h, SNil{}}}, "", ga), "", rs)}, 1n+L) == True{} : Bool}:
  match ga rs:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+y} B.Refuse{+c}:
      {==}
    case B.Got{+y} B.Got{+z}:
      app_le(y, z, SL(tk), L, hy, hr)

def gput(+sep: Bool, +h: Char, +r: B.Gp, +over0: Bool, +n: Nat, +i: Nat, +L: Nat, +hr: {GPL(r, L) == True{} : Bool}) ->
  {GPL(B.Gt.go.put(sep, h, r, over0, n, i), 1n+L) == True{} : Bool}:
  match sep r:
    case True{} B.Gp{+tk, +rs}:
      gp.k(h, tk, B.Gt.allele(over0, n, i, tk), rs, L, gallele(over0, n, i, tk), hr)
    case False{} B.Gp{+tk, +rs}:
      match rs:
        case B.Got{+z}:
          hr
        case B.Refuse{+c}:
          {==}

law ggo:
  for +s: String
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  {GPL(B.Gt.go(s, over0, n, i), String.length(s)) == True{} : Bool}

def ggo(s, over0, n, i):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      gput(B.Gt.is_sep(c), c, B.Gt.go(t, over0, n, i), over0, n, i, SL(t), ggo(t, over0, n, i))

def gof.k(+tk: String, +ga: B.Got, +rs: B.Got, +L: Nat, +hy: {GLE(ga, SL(tk)) == True{} : Bool}, +hr: {GPL(B.Gp{tk, rs}, L) == True{} : Bool}) ->
  {GLE(B.Got.cat(ga, "", rs), L) == True{} : Bool}:
  match ga rs:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+y} B.Refuse{+c}:
      {==}
    case B.Got{+y} B.Got{+z}:
      app_le(y, z, SL(tk), L, hy, hr)

def gof(+r: B.Gp, +over0: Bool, +n: Nat, +i: Nat, +L: Nat, +hr: {GPL(r, L) == True{} : Bool}) -> {GLE(B.Gt.split.of(r, over0, n, i), L) == True{} : Bool}:
  match r:
    case B.Gp{+tk, +rs}:
      gof.k(tk, B.Gt.allele(over0, n, i, tk), rs, L, gallele(over0, n, i, tk), hr)

# GT in the record: no longer than GT.
def gsplit(+over0: Bool, +n: Nat, +i: Nat, +g: String) -> {GLE(B.Gt.split(over0, n, i, g), SL(g)) == True{} : Bool}:
  gof(B.Gt.go(g, over0, n, i), over0, n, i, SL(g), ggo(g, over0, n, i))

def fnum.k(+num: B.Num, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i1: Nat) ->
  {GLE(B.Fmt.split.num(Some{num}, k, v, n, cp, 1n+i1), SL(v)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      N.le_refl(SL(v))
    case B.NumA{}:
      got_of(B.Vals.split(B.NumA{}, n, cp, 1n+i1, v), B.BadCount{}, SL(v), vsplit(B.NumA{}, n, cp, i1, v))
    case B.NumR{}:
      got_of(B.Vals.split(B.NumR{}, n, cp, 1n+i1, v), B.BadCount{}, SL(v), vsplit(B.NumR{}, n, cp, i1, v))
    case B.NumG{}:
      got_of(B.Vals.split(B.NumG{}, n, cp, 1n+i1, v), B.BadCount{}, SL(v), vsplit(B.NumG{}, n, cp, i1, v))

def fnum(+m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i1: Nat) ->
  {GLE(B.Fmt.split.num(m, k, v, n, cp, 1n+i1), SL(v)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      fnum.k(num, k, v, n, cp, i1)

def fone(+k: String, +v: String, +fmt: List<&2, B.Tag>, +over0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i1: Nat) ->
  {GLE(B.Fmt.split.one(k, v, fmt, over0, n, cp, 1n+i1), SL(v)) == True{} : Bool}:
  pick_got(String.eq(k, "GT"), B.Gt.split(over0, n, 1n+i1, v), B.Fmt.split.num(B.Tags.find(fmt, k), k, v, n, cp, 1n+i1), SL(v),
    gsplit(over0, n, 1n+i1, v), fnum(B.Tags.find(fmt, k), k, v, n, cp, i1))

law fgo:
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +over0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i1: Nat
  {LEP(B.Fmt.split.go(ks, vs, fmt, over0, n, cp, 1n+i1), vs) == True{} : Bool}

def fgo(ks, vs, fmt, over0, n, cp, i1):
  match ks vs:
    case _ Nil{}:
      {==}
    case Nil{} Con{+v, +t}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      CH.and_tt(GLE(B.Fmt.split.one(k, v, fmt, over0, n, cp, 1n+i1), SL(v)), LEP(B.Fmt.split.go(kt, vt, fmt, over0, n, cp, 1n+i1), vt),
        fone(k, v, fmt, over0, n, cp, i1), fgo(kt, vt, fmt, over0, n, cp, i1))

# A sample column in the record for ALT i >= 1: no longer than the column.
law fmt_len:
  for +ks: Ss()
  for +col: String
  for +fmt: List<&2, B.Tag>
  for +over0: Bool
  for +n: Nat
  for +i1: Nat
  {GLE(B.Fmt.split(ks, col, fmt, over0, n, 1n+i1), String.length(col)) == True{} : Bool}

def fmt_len(ks, col, fmt, over0, n, i1):
  +vs = String.split(col, ':')
  jsplit(B.Fmt.split.go(ks, vs, fmt, over0, n, B.Gt.copies(B.Fmt.gt(ks, vs)), 1n+i1), col, ':', ":", {==},
    fgo(ks, vs, fmt, over0, n, B.Gt.copies(B.Fmt.gt(ks, vs)), i1))

# ---------------------------------------------------------------------------
# Records
# ---------------------------------------------------------------------------

# The fields from the sixth on (QUAL, FILTER, INFO, FORMAT, the samples).
def pf5(+j: Nat, +f: String, +a: String, +defs: B.Defs, +ks: Ss(), +over0: Bool, +n: Nat, +i1: Nat) ->
  {GLE(B.Rec.piece.field(1n+1n+1n+1n+1n+j, f, a, defs, ks, over0, n, 1n+i1), SL(f)) == True{} : Bool}:
  +j5 = Nat.add(5n, j)
  pick_got(Nat.is_eq(j5, 7n), B.Info.split(f, B.Defs.info(defs), n, 1n+i1), Bool.pick(B.Got, Nat.is_le(9n, j5), B.Fmt.split(ks, f, B.Defs.fmt(defs), over0, n, 1n+i1), B.Got{f}), SL(f),
    info_len(f, B.Defs.info(defs), n, i1),
    pick_got(Nat.is_le(9n, j5), B.Fmt.split(ks, f, B.Defs.fmt(defs), over0, n, 1n+i1), B.Got{f}, SL(f), fmt_len(ks, f, B.Defs.fmt(defs), over0, n, i1), N.le_refl(SL(f))))

law pgo5:
  for +fs: Ss()
  for +j: Nat
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +over0: Bool
  for +n: Nat
  for +i1: Nat
  {LEP(B.Rec.piece.go(fs, 1n+1n+1n+1n+1n+j, a, defs, ks, over0, n, 1n+i1), fs) == True{} : Bool}

def pgo5(fs, j, a, defs, ks, over0, n, i1):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      CH.and_tt(GLE(B.Rec.piece.field(1n+1n+1n+1n+1n+j, f, a, defs, ks, over0, n, 1n+i1), SL(f)), LEP(B.Rec.piece.go(t, 1n+1n+1n+1n+1n+(1n+j), a, defs, ks, over0, n, 1n+i1), t),
        pf5(j, f, a, defs, ks, over0, n, i1), pgo5(t, 1n+j, a, defs, ks, over0, n, i1))

def F5(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss()) -> Ss():
  f0 <> f1 <> f2 <> f3 <> f4 <> rest

# The record for one ALT a (no longer than ALT): shorter than SN of the fields.
def piece_len(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +a: String, +defs: B.Defs, +o0: Bool, +n: Nat, +i1: Nat,
  +ha: {Nat.is_le(SL(a), SL(f4)) == True{} : Bool}) ->
  {GL1(B.Rec.piece(F5(f0, f1, f2, f3, f4, rest), a, defs, o0, n, 1n+i1), Q.SN(F5(f0, f1, f2, f3, f4, rest))) == True{} : Bool}:
  +ks = String.split(B.Rec.field(F5(f0, f1, f2, f3, f4, rest), 8n), ':')
  +i = Nat.add(1n, i1)
  +h4 = CH.and_tt(Nat.is_le(SL(a), SL(f4)), LEP(B.Rec.piece.go(rest, 5n, a, defs, ks, o0, n, i), rest), ha, pgo5(rest, 0n, a, defs, ks, o0, n, i1))
  +h3 = CH.and_tt(Nat.is_le(SL(f3), SL(f3)), LEP(B.Rec.piece.go(f4 <> rest, 4n, a, defs, ks, o0, n, i), f4 <> rest), N.le_refl(SL(f3)), h4)
  +h2 = CH.and_tt(Nat.is_le(SL(f2), SL(f2)), LEP(B.Rec.piece.go(f3 <> f4 <> rest, 3n, a, defs, ks, o0, n, i), f3 <> f4 <> rest), N.le_refl(SL(f2)), h3)
  +h1 = CH.and_tt(Nat.is_le(SL(f1), SL(f1)), LEP(B.Rec.piece.go(f2 <> f3 <> f4 <> rest, 2n, a, defs, ks, o0, n, i), f2 <> f3 <> f4 <> rest), N.le_refl(SL(f1)), h2)
  +h0 = CH.and_tt(Nat.is_le(SL(f0), SL(f0)), LEP(B.Rec.piece.go(f1 <> f2 <> f3 <> f4 <> rest, 1n, a, defs, ks, o0, n, i), f1 <> f2 <> f3 <> f4 <> rest), N.le_refl(SL(f0)), h1)
  jl(B.Rec.piece.go(F5(f0, f1, f2, f3, f4, rest), 0n, a, defs, ks, o0, n, i), f0, f1 <> f2 <> f3 <> f4 <> rest, "\t", {==}, h0)

law pieces_go:
  for +alts: Ss()
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +rest: Ss()
  for +defs: B.Defs
  for +o0: Bool
  for +n: Nat
  for +i1: Nat
  for +ha: {RLT(alts, 1n+String.length(f4)) == True{} : Bool}
  {PLE1(B.Rec.pieces.go(alts, F5(f0, f1, f2, f3, f4, rest), defs, o0, n, 1n+i1), Q.SN(F5(f0, f1, f2, f3, f4, rest))) == True{} : Bool}

def pieces_go(alts, f0, f1, f2, f3, f4, rest, defs, o0, n, i1, ha):
  match alts:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      +fs = F5(f0, f1, f2, f3, f4, rest)
      CH.and_tt(GL1(B.Rec.piece(fs, a, defs, o0, n, 1n+i1), Q.SN(fs)), PLE1(B.Rec.pieces.go(t, fs, defs, o0, n, 1n+(1n+i1)), Q.SN(fs)),
        piece_len(f0, f1, f2, f3, f4, rest, a, defs, o0, n, i1, AB.and_true_l(Nat.is_le(1n+SL(a), 1n+SL(f4)), RLT(t, 1n+SL(f4)), ha)),
        pieces_go(t, f0, f1, f2, f3, f4, rest, defs, o0, n, 1n+i1, AB.and_true_r(Nat.is_le(1n+SL(a), 1n+SL(f4)), RLT(t, 1n+SL(f4)), ha)))

law pg_cnt:
  for +alts: Ss()
  for +fs: Ss()
  for +defs: B.Defs
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  {List.length(&2, B.Got, B.Rec.pieces.go(alts, fs, defs, o0, n, i)) == List.length(&2, String, alts) : Nat}

def pg_cnt(alts, fs, defs, o0, n, i):
  match alts:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Got, B.Rec.pieces.go(t, fs, defs, o0, n, 1n+i)), List.length(&2, String, t), pg_cnt(t, fs, defs, o0, n, 1n+i))

# Parts.of giving Pieces: the texts, each shorter than M, no more than gs.
def OK(+ps: Ss(), +M: Nat, +K: Nat) -> Bool:
  RLT(ps, M) && Nat.is_le(List.length(&2, String, ps), K)

def pcons_k(+x: String, +r: B.Parts, +ps: Ss(), +M: Nat, +K: Nat, +h: {B.Parts.cons(B.Got{x}, r) == B.Pieces{ps} : B.Parts},
  +hx: {Nat.is_le(1n+SL(x), M) == True{} : Bool},
  ih: @+qs: Ss() -> {r == B.Pieces{qs} : B.Parts} -> {OK(qs, M, K) == True{} : Bool}) -> {OK(ps, M, 1n+K) == True{} : Bool}:
  match r:
    case B.Pieces{+qs}:
      %Equal.sym(Ss(), ps, x <> qs, Equal.sym(Ss(), x <> qs, ps, Equal.cong(B.Parts, Ss(), CH.pieces_of, B.Pieces{x <> qs}, B.Pieces{ps}, h))) : {OK(_, M, 1n+K) == True{} : Bool}
      +hq = ih(qs, {==})
      CH.and_tt(Bool.and(Nat.is_le(1n+SL(x), M), RLT(qs, M)), Nat.is_le(List.length(&2, String, qs), K),
        CH.and_tt(Nat.is_le(1n+SL(x), M), RLT(qs, M), hx, AB.and_true_l(RLT(qs, M), Nat.is_le(List.length(&2, String, qs), K), hq)),
        AB.and_true_r(RLT(qs, M), Nat.is_le(List.length(&2, String, qs), K), hq))
    case B.Whole{}:
      Empty.absurd({OK(ps, M, 1n+K) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Whole{}, B.Pieces{ps}, h)))
    case B.Unsplit{+c}:
      Empty.absurd({OK(ps, M, 1n+K) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

def pcons_g(+g: B.Got, +r: B.Parts, +ps: Ss(), +M: Nat, +K: Nat, +h: {B.Parts.cons(g, r) == B.Pieces{ps} : B.Parts},
  +hg: {GL1(g, M) == True{} : Bool},
  ih: @+qs: Ss() -> {r == B.Pieces{qs} : B.Parts} -> {OK(qs, M, K) == True{} : Bool}) -> {OK(ps, M, 1n+K) == True{} : Bool}:
  match g:
    case B.Got{+x}:
      pcons_k(x, r, ps, M, K, h, hg, ih)
    case B.Refuse{+c}:
      Empty.absurd({OK(ps, M, 1n+K) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

law of_ok:
  for +gs: List<&2, B.Got>
  for +ps: Ss()
  for +M: Nat
  for +h: {B.Parts.of(gs) == B.Pieces{ps} : B.Parts}
  for +hg: {PLE1(gs, M) == True{} : Bool}
  {OK(ps, M, List.length(&2, B.Got, gs)) == True{} : Bool}

def of_ok(gs, ps, M, h, hg):
  match gs:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), CH.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {OK(_, M, 0n) == True{} : Bool}
      {==}
    case Con{+g, +t}:
      pcons_g(g, B.Parts.of(t), ps, M, List.length(&2, B.Got, t), h, AB.and_true_l(GL1(g, M), PLE1(t, M), hg),
        +qs => hq => of_ok(t, qs, M, hq, AB.and_true_r(GL1(g, M), PLE1(t, M), hg)))

def RC(+ps: Ss(), +fs: Ss()) -> Bool:
  OK(ps, Q.SN(fs), List.length(&2, String, B.Rec.alts(fs)))

# A line split into records: at least 5 fields (it is not MALFORMED).
def sp_ok(+fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(), +h: {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts}, +hm: {Bool.not(B.Rec.malformed(fs)) == True{} : Bool}) ->
  {RC(ps, fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({RC(ps, Nil{}) == True{} : Bool}, AB.false_ne_true(hm))
    case Con{+f0, Nil{}}:
      Empty.absurd({RC(ps, [f0]) == True{} : Bool}, AB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({RC(ps, [f0, f1]) == True{} : Bool}, AB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({RC(ps, [f0, f1, f2]) == True{} : Bool}, AB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({RC(ps, [f0, f1, f2, f3]) == True{} : Bool}, AB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, +rest}}}}}:
      +fs5 = F5(f0, f1, f2, f3, f4, rest)
      +al = String.split(f4, ',')
      +gs = B.Rec.pieces.go(al, fs5, defs, o0, List.length(&2, String, al), 1n)
      +ha = AB.subst(Nat, z => {RLT(al, z) == True{} : Bool}, Q.SN(al), 1n+SL(f4), Q.split_sn(f4, ','), sn_all(al))
      +ho = of_ok(gs, ps, Q.SN(fs5), h, pieces_go(al, f0, f1, f2, f3, f4, rest, defs, o0, List.length(&2, String, al), 0n, ha))
      +hc = AB.subst(Nat, z => {Nat.is_le(List.length(&2, String, ps), z) == True{} : Bool}, List.length(&2, B.Got, gs), List.length(&2, String, al),
        pg_cnt(al, fs5, defs, o0, List.length(&2, String, al), 1n), AB.and_true_r(RLT(ps, Q.SN(fs5)), Nat.is_le(List.length(&2, String, ps), List.length(&2, B.Got, gs)), ho))
      CH.and_tt(RLT(ps, Q.SN(fs5)), Nat.is_le(List.length(&2, String, ps), List.length(&2, String, al)),
        AB.and_true_l(RLT(ps, Q.SN(fs5)), Nat.is_le(List.length(&2, String, ps), List.length(&2, B.Got, gs)), ho), hc)

def pa_split(+d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hm: {Bool.not(B.Rec.malformed(B.Rec.fields(body))) == True{} : Bool}) ->
  {RC(ps, B.Rec.fields(body)) == True{} : Bool}:
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({RC(ps, fs) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%ed : {B.Rec.parts.split(_, al, fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, al, fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      sp_ok(fs, defs, o0, ps, h2, hm)

def pa_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {CH.COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(CH.COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  {RC(ps, B.Rec.fields(body)) == True{} : Bool}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({RC(ps, fs) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      +nm = Bool.not(B.Rec.malformed(fs))
      +two = Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs)))
      +hm = AB.and_true_r(sp, nm, AB.and_true_l(Bool.and(sp, nm), two, e))
      pa_split(B.Alts.distinct(B.Rec.alts(fs)), defs, o0, body, ps, {==}, h2, hm)

law parts_ok:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {RC(ps, B.Rec.fields(body)) == True{} : Bool}

def parts_ok(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      pa_if(CH.COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==},
        CR.cr_h(CH.COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))

# The records of a split line are no longer than the line's body.
law rec_len:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {RLE(ps, String.length(body)) == True{} : Bool}

def rec_len(defs, o, body, ps, h):
  +fs = B.Rec.fields(body)
  +K = List.length(&2, String, B.Rec.alts(fs))
  rlt_rle(ps, SL(body), AB.subst(Nat, z => {RLT(ps, z) == True{} : Bool}, Q.SN(fs), 1n+SL(body), Q.split_sn(body, '\t'),
    AB.and_true_l(RLT(ps, Q.SN(fs)), Nat.is_le(List.length(&2, String, ps), K), parts_ok(defs, o, body, ps, h))))

# There are no more records than ALTs.
law rec_cnt:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {Nat.is_le(List.length(&2, String, ps), List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool}

def rec_cnt(defs, o, body, ps, h):
  +fs = B.Rec.fields(body)
  +K = List.length(&2, String, B.Rec.alts(fs))
  AB.and_true_r(RLT(ps, Q.SN(fs)), Nat.is_le(List.length(&2, String, ps), K), parts_ok(defs, o, body, ps, h))

def cnd.k(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {CH.COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(CH.COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  {CH.COND(sp, B.Rec.fields(body)) == True{} : Bool}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({CH.COND(sp, fs) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, CH.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      e

# A split line is one -m may split: -m, not MALFORMED, two or more ALTs.
law parts_cand:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {CH.COND(R.Opts.split(o), B.Rec.fields(body)) == True{} : Bool}

def parts_cand(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      cnd.k(CH.COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==},
        CR.cr_h(CH.COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))
