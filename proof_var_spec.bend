import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP
import ./proof_var_steps.bend as ST

# The steps on whole variants: each keeps validity and the change; and the
# spec's tests (shift, drop_last, drop_first) read back as "all alleles end
# (start) with the same base".

def same_of_eq(+seq: Q.Bs(), +v: B.Var, +w: B.Var, +e: {L.haps(seq, v) == L.haps(seq, w) : Q.Als()}) ->
  {L.same(seq, v, w) == True{} : Bool}:
  %Equal.sym(Q.Als(), L.haps(seq, v), L.haps(seq, w), e) : {B.Alleles.eq(_, L.haps(seq, w)) == True{} : Bool}
  Q.alleles_refl(L.haps(seq, w))

def eq_of_same(+seq: Q.Bs(), +v: B.Var, +w: B.Var, +e: {L.same(seq, v, w) == True{} : Bool}) ->
  {L.haps(seq, v) == L.haps(seq, w) : Q.Als()}:
  Q.alleles_sound(L.haps(seq, v), L.haps(seq, w), e)

def trans3(+x: Q.Als(), +y: Q.Als(), +z: Q.Als(), +w: Q.Als(), +a: {x == y : Q.Als()}, +b: {y == z : Q.Als()}, +c: {w == z : Q.Als()}) ->
  {x == w : Q.Als()}:
  Equal.trans(Q.Als(), x, z, w, Equal.trans(Q.Als(), x, y, z, a, b), Equal.sym(Q.Als(), w, z, c))

def no_ref(+seq: Q.Bs(), +pos: Nat, +xs: Q.Als(), +hv: RP.Valid(seq, pos, Nil{}, xs), -T: Type) -> T:
  Empty.absurd(T, P.false_ne_true(RP.vk2(seq, pos, Nil{}, xs, hv)))

def ne_inits(+xs: Q.Als(), +h: {V.all_long(xs) == True{} : Bool}) -> {L.all_nonempty(V.inits(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({L.all_nonempty(V.inits(Nil{} <> t)) == True{} : Bool}, P.false_ne_true(h))
        case +g <> +u:
          Q.and_tt(Nat.is_le(1n, Q.len(Q.init(g <> u))), L.all_nonempty(V.inits(t)),
            %Q.len_init_r(g, u) : {Nat.is_le(1n, _) == True{} : Bool};
              P.and_true_l(Nat.is_le(2n, Q.len(g <> u)), V.all_long(t), h),
            ne_inits(t, P.and_true_r(Nat.is_le(2n, Q.len(g <> u)), V.all_long(t), h)))

def ne_tails(+xs: Q.Als(), +h: {V.all_long(xs) == True{} : Bool}) -> {L.all_nonempty(V.tails(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({L.all_nonempty(V.tails(Nil{} <> t)) == True{} : Bool}, P.false_ne_true(h))
        case +g <> +u:
          Q.and_tt(Nat.is_le(1n, Q.len(u)), L.all_nonempty(V.tails(t)),
            P.and_true_l(Nat.is_le(2n, Q.len(g <> u)), V.all_long(t), h),
            ne_tails(t, P.and_true_r(Nat.is_le(2n, Q.len(g <> u)), V.all_long(t), h)))

def ne_shifted(+c: B.Base, +xs: Q.Als()) -> {L.all_nonempty(V.shifted(c, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Q.and_tt(Nat.is_le(1n, Q.len(c <> V.init(x))), L.all_nonempty(V.shifted(c, t)),
        P.le_zero_l(Q.len(V.init(x))), ne_shifted(c, t))

# Trim the last base
# ==================

def trim_haps(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +he: {V.lasts_eq(r <> xs) == True{} : Bool}) ->
  {L.haps(seq, B.Var{pos, V.init(r), V.inits(xs)}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}:
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, {L.haps(seq, B.Var{pos, V.init(Nil{}), V.inits(xs)}) == L.haps(seq, B.Var{pos, Nil{}, xs}) : Q.Als()})
    case +g <> +u:
      +a = RP.vA(seq, pos)
      +b = RP.vB(seq, pos, g <> u)
      +es2 = ST.trim_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
      +hm = {%Equal.sym(Q.Als(), V.inits(xs), L.inits(xs), ST.inits_eq(xs)) :
          {RP.hmap(a, ST.lst(g, u) <> b, _) == RP.hmap(a, b, xs) : Q.Als()};
        ST.trim_hmap(a, b, ST.lst(g, u), xs, he) : {RP.hmap(a, ST.lst(g, u) <> b, V.inits(xs)) == RP.hmap(a, b, xs) : Q.Als()}}
      trans3(L.haps(seq, B.Var{pos, V.init(g <> u), V.inits(xs)}), RP.hmap(a, ST.lst(g, u) <> b, V.inits(xs)), RP.hmap(a, b, xs),
        L.haps(seq, B.Var{pos, g <> u, xs}),
        RP.haps_rep(seq, pos, V.init(g <> u), a, ST.lst(g, u) <> b, es2, RP.valid_el(seq, pos, g <> u, xs, hv), V.inits(xs)),
        hm, RP.valid_haps(seq, pos, g <> u, xs, hv))

def trim_valid(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +he: {V.lasts_eq(r <> xs) == True{} : Bool}, +hl: {V.all_long(r <> xs) == True{} : Bool}) ->
  RP.Valid(seq, pos, V.init(r), V.inits(xs)):
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, RP.Valid(seq, pos, V.init(Nil{}), V.inits(xs)))
    case +g <> +u:
      +a = RP.vA(seq, pos)
      +b = RP.vB(seq, pos, g <> u)
      +es2 = ST.trim_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
      +hm = {%Equal.sym(Q.Als(), V.inits(xs), L.inits(xs), ST.inits_eq(xs)) :
          {RP.hmap(a, ST.lst(g, u) <> b, _) == RP.hmap(a, b, xs) : Q.Als()};
        ST.trim_hmap(a, b, ST.lst(g, u), xs, he) : {RP.hmap(a, ST.lst(g, u) <> b, V.inits(xs)) == RP.hmap(a, b, xs) : Q.Als()}}
      +hl1 = P.and_true_l(Nat.is_le(2n, Q.len(g <> u)), V.all_long(xs), hl)
      +hl2 = P.and_true_r(Nat.is_le(2n, Q.len(g <> u)), V.all_long(xs), hl)
      RP.valid_of_rep(seq, pos, V.init(g <> u), V.inits(xs), a, ST.lst(g, u) <> b, es2, RP.valid_el(seq, pos, g <> u, xs, hv),
        RP.vk1(seq, pos, g <> u, xs, hv),
        %Q.len_init_r(g, u) : {Nat.is_le(1n, _) == True{} : Bool}; hl1,
        ne_inits(xs, hl2), pos, g <> u, xs, hv, hm)

# The spec's drop_last.
def trim_haps_l(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +he: {V.lasts_eq(r <> xs) == True{} : Bool}) ->
  {L.haps(seq, L.drop_last(B.Var{pos, r, xs})) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}:
  %ST.inits_eq(xs) : {L.haps(seq, B.Var{pos, L.init(r), _}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}
  trim_haps(seq, pos, r, xs, hv, he)

# Shift one base left (the code's step, read through a cut a, b)
# ==============================================================

def shift_gen(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +x: B.Base, +hv: RP.Valid(seq, pos, g <> u, xs),
  +he: {V.same_last(Some{ST.lst(g, u)}, xs) == True{} : Bool}, +hs: {Nat.is_le(2n, pos) == True{} : Bool},
  +hx: {V.Win.get(0n, seq, Nat.sub(pos, 2n)) == Some{x} : Maybe<&2, B.Base>},
  +a: Q.Bs(), +b: Q.Bs(), +es: {Q.app(a, Q.app(g <> u, b)) == seq : Q.Bs()}, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat},
  +hab: {RP.hmap(a, b, xs) == RP.hmap(RP.vA(seq, pos), RP.vB(seq, pos, g <> u), xs) : Q.Als()}) ->
  RP.Valid(seq, Nat.sub(pos, 1n), x <> V.init(g <> u), V.shifted(x, xs))
    & {L.haps(seq, B.Var{Nat.sub(pos, 1n), x <> V.init(g <> u), V.shifted(x, xs)}) == L.haps(seq, B.Var{pos, g <> u, xs}) : Q.Als()}:
  match a:
    case Nil{}:
      Empty.absurd(RP.Valid(seq, Nat.sub(pos, 1n), x <> V.init(g <> u), V.shifted(x, xs))
          & {L.haps(seq, B.Var{Nat.sub(pos, 1n), x <> V.init(g <> u), V.shifted(x, xs)}) == L.haps(seq, B.Var{pos, g <> u, xs}) : Q.Als()},
        P.false_ne_true(%Equal.sym(Nat, 0n, Nat.sub(pos, 1n), el) : {Nat.is_le(1n, _) == True{} : Bool}; Q.le2_sub1(pos, hs)))
    case +c0 <> +ct:
      +a0 = Q.init(c0 <> ct)
      +c = ST.lst(c0, ct)
      +lr = ST.lst(g, u)
      +es2 = ST.shift_es(seq, c0, ct, g, u, b, es)
      +el2 = ST.shift_el(pos, c0, ct, el)
      +ei = Equal.trans(Nat, Q.len(a0), Nat.sub(Nat.sub(pos, 1n), 1n), Nat.sub(pos, 2n), el2, Q.sub_sub_one(pos))
      +gt = ST.shift_get(seq, a0, c, Q.app(Q.init(g <> u), lr <> b), Nat.sub(pos, 2n), es2, ei)
      +ex = Q.some_inj(x, c, Equal.trans(Maybe<&2, B.Base>, Some{x}, V.Win.get(0n, seq, Nat.sub(pos, 2n)), Some{c},
        Equal.sym(Maybe<&2, B.Base>, V.Win.get(0n, seq, Nat.sub(pos, 2n)), Some{x}, hx), gt))
      %Equal.sym(B.Base, x, c, ex) :
        RP.Valid(seq, Nat.sub(pos, 1n), _ <> V.init(g <> u), V.shifted(_, xs))
          & {L.haps(seq, B.Var{Nat.sub(pos, 1n), _ <> V.init(g <> u), V.shifted(_, xs)}) == L.haps(seq, B.Var{pos, g <> u, xs}) : Q.Als()}
      +hm = {%Q.snoc(c0, ct) : {RP.hmap(a0, lr <> b, V.shifted(c, xs)) == RP.hmap(_, b, xs) : Q.Als()};
        ST.shift_hmap(a0, c, lr, b, xs, he) : {RP.hmap(a0, lr <> b, V.shifted(c, xs)) == RP.hmap(c0 <> ct, b, xs) : Q.Als()}}
      +hh = Equal.trans(Q.Als(), RP.hmap(a0, lr <> b, V.shifted(c, xs)), RP.hmap(c0 <> ct, b, xs),
        RP.hmap(RP.vA(seq, pos), RP.vB(seq, pos, g <> u), xs), hm, hab)
      +vv = RP.valid_of_rep(seq, Nat.sub(pos, 1n), c <> V.init(g <> u), V.shifted(c, xs), a0, lr <> b, es2, el2,
        Q.le2_sub1(pos, hs), P.le_zero_l(Q.len(V.init(g <> u))), ne_shifted(c, xs), pos, g <> u, xs, hv, hh)
      +hp = trans3(L.haps(seq, B.Var{Nat.sub(pos, 1n), c <> V.init(g <> u), V.shifted(c, xs)}),
        RP.hmap(a0, lr <> b, V.shifted(c, xs)), RP.hmap(RP.vA(seq, pos), RP.vB(seq, pos, g <> u), xs),
        L.haps(seq, B.Var{pos, g <> u, xs}),
        RP.haps_rep(seq, Nat.sub(pos, 1n), c <> V.init(g <> u), a0, lr <> b, es2, el2, V.shifted(c, xs)),
        hh, RP.valid_haps(seq, pos, g <> u, xs, hv))
      (vv, hp)

# Shifting needs the base before the variant: the whole contig has it.
def get_some(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +hs: {Nat.is_le(2n, pos) == True{} : Bool},
  +a: Q.Bs(), +b: Q.Bs(), +es: {Q.app(a, Q.app(g <> u, b)) == seq : Q.Bs()}, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}) ->
  {Maybe.is_some(&2, B.Base, V.Win.get(0n, seq, Nat.sub(pos, 2n))) == True{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&2, B.Base, V.Win.get(0n, seq, Nat.sub(pos, 2n))) == True{} : Bool},
        P.false_ne_true(%Equal.sym(Nat, 0n, Nat.sub(pos, 1n), el) : {Nat.is_le(1n, _) == True{} : Bool}; Q.le2_sub1(pos, hs)))
    case +c0 <> +ct:
      +a0 = Q.init(c0 <> ct)
      +es2 = ST.shift_es(seq, c0, ct, g, u, b, es)
      +ei = Equal.trans(Nat, Q.len(a0), Nat.sub(Nat.sub(pos, 1n), 1n), Nat.sub(pos, 2n), ST.shift_el(pos, c0, ct, el), Q.sub_sub_one(pos))
      %Equal.sym(Maybe<&2, B.Base>, V.Win.get(0n, seq, Nat.sub(pos, 2n)), Some{ST.lst(c0, ct)},
          ST.shift_get(seq, a0, ST.lst(c0, ct), Q.app(Q.init(g <> u), ST.lst(g, u) <> b), Nat.sub(pos, 2n), es2, ei)) :
        {Maybe.is_some(&2, B.Base, _) == True{} : Bool}
      {==}

# The spec's shift by one base, when every allele ends alike and pos >= 2.
def shift_one_gen(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +he: {V.same_last(Some{ST.lst(g, u)}, xs) == True{} : Bool}, +hs: {Nat.is_le(2n, pos) == True{} : Bool},
  +a: Q.Bs(), +b: Q.Bs(), +es: {Q.app(a, Q.app(g <> u, b)) == seq : Q.Bs()}, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat},
  +hab: {RP.hmap(a, b, xs) == RP.hmap(RP.vA(seq, pos), RP.vB(seq, pos, g <> u), xs) : Q.Als()}) ->
  {L.same(seq, L.shift(seq, B.Var{pos, g <> u, xs}, 1n), B.Var{pos, g <> u, xs}) == True{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({L.same(seq, L.shift(seq, B.Var{pos, g <> u, xs}, 1n), B.Var{pos, g <> u, xs}) == True{} : Bool},
        P.false_ne_true(%Equal.sym(Nat, 0n, Nat.sub(pos, 1n), el) : {Nat.is_le(1n, _) == True{} : Bool}; Q.le2_sub1(pos, hs)))
    case +c0 <> +ct:
      +a0 = Q.init(c0 <> ct)
      +c = ST.lst(c0, ct)
      +lr = ST.lst(g, u)
      +i = Nat.sub(Nat.sub(pos, 1n), 1n)
      +es2 = ST.shift_es(seq, c0, ct, g, u, b, es)
      +el2 = ST.shift_el(pos, c0, ct, el)
      +ei = Equal.trans(Nat, Q.len(a0), i, Nat.sub(pos, 2n), el2, Q.sub_sub_one(pos))
      +gt = ST.shift_get(seq, a0, c, Q.app(Q.init(g <> u), lr <> b), Nat.sub(pos, 2n), es2, ei)
      +es3 = {%Q.snoc_r(c0, ct) : {Q.app(_, Q.app(g <> u, b)) == seq : Q.Bs()}; es : {Q.app(Q.app(a0, [c]), Q.app(g <> u, b)) == seq : Q.Bs()}}
      +el3 = {%Q.snoc_r(c0, ct) : {Q.len(_) == Nat.sub(pos, 1n) : Nat}; el : {Q.len(Q.app(a0, [c])) == Nat.sub(pos, 1n) : Nat}}
      +hne = RP.vk4(seq, pos, g <> u, xs, hv)
      %Equal.sym(Q.Bs(), L.slice(seq, i, L.len(g <> u)), c <> Q.init(g <> u), ST.shift_ref(seq, a0, c, g, u, b, i, es2, el2)) :
        {L.same(seq, B.Var{Nat.sub(pos, 1n), _, L.shift.alts(seq, pos, g <> u, i, xs)}, B.Var{pos, g <> u, xs}) == True{} : Bool}
      %Equal.sym(Q.Als(), L.shift.alts(seq, pos, g <> u, i, xs), V.shifted(c, xs), ST.shift_alts(seq, pos, g <> u, a0, c, b, i, es3, el3, el2, xs, hne)) :
        {L.same(seq, B.Var{Nat.sub(pos, 1n), c <> Q.init(g <> u), _}, B.Var{pos, g <> u, xs}) == True{} : Bool}
      same_of_eq(seq, B.Var{Nat.sub(pos, 1n), c <> V.init(g <> u), V.shifted(c, xs)}, B.Var{pos, g <> u, xs},
        Q.snd(RP.Valid(seq, Nat.sub(pos, 1n), c <> V.init(g <> u), V.shifted(c, xs)),
          {L.haps(seq, B.Var{Nat.sub(pos, 1n), c <> V.init(g <> u), V.shifted(c, xs)}) == L.haps(seq, B.Var{pos, g <> u, xs}) : Q.Als()},
          shift_gen(seq, pos, g, u, xs, c, hv, he, hs, gt, c0 <> ct, b, es, el, hab)))

def shift_one(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +he: {V.same_last(Some{ST.lst(g, u)}, xs) == True{} : Bool}, +hs: {Nat.is_le(2n, pos) == True{} : Bool}) ->
  {L.same(seq, L.shift(seq, B.Var{pos, g <> u, xs}, 1n), B.Var{pos, g <> u, xs}) == True{} : Bool}:
  shift_one_gen(seq, pos, g, u, xs, hv, he, hs, RP.vA(seq, pos), RP.vB(seq, pos, g <> u),
    RP.valid_es(seq, pos, g <> u, xs, hv), RP.valid_el(seq, pos, g <> u, xs, hv), {==})

def movable_one(+k: Nat, +seq: Q.Bs(), +v: B.Var, +h: {L.same(seq, L.shift(seq, v, 1n), v) == True{} : Bool}) ->
  {L.movable(seq, v, 1n+k) == True{} : Bool}:
  match k:
    case 0n:
      %Equal.sym(Bool, L.same(seq, L.shift(seq, v, 1n), v), True{}, h) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case 1n+j:
      Q.or_tt_r(L.same(seq, L.shift(seq, v, 2n+j), v), L.movable(seq, v, 1n+j), movable_one(j, seq, v, h))

# Trim the first base
# ===================

def left_haps_l(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +hf: {V.same_first(Some{g}, xs) == True{} : Bool}) ->
  {L.haps(seq, B.Var{1n+pos, u, L.tails(xs)}) == L.haps(seq, B.Var{pos, g <> u, xs}) : Q.Als()}:
  +a = RP.vA(seq, pos)
  +b = RP.vB(seq, pos, g <> u)
  +es2 = ST.left_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
  +el2 = ST.left_el(pos, a, g, RP.valid_el(seq, pos, g <> u, xs, hv), RP.vk1(seq, pos, g <> u, xs, hv))
  trans3(L.haps(seq, B.Var{1n+pos, u, L.tails(xs)}), RP.hmap(Q.app(a, [g]), b, L.tails(xs)), RP.hmap(a, b, xs),
    L.haps(seq, B.Var{pos, g <> u, xs}),
    RP.haps_rep(seq, 1n+pos, u, Q.app(a, [g]), b, es2, el2, L.tails(xs)),
    ST.left_hmap(a, g, b, xs, hf), RP.valid_haps(seq, pos, g <> u, xs, hv))

def left_step(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +hfl: {Bool.and(V.firsts_eq(r <> xs), V.all_long(r <> xs)) == True{} : Bool}) ->
  RP.Valid(seq, 1n+pos, List.tail(&2, B.Base, r), V.tails(xs))
    & {L.haps(seq, B.Var{1n+pos, List.tail(&2, B.Base, r), V.tails(xs)}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}:
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, RP.Valid(seq, 1n+pos, List.tail(&2, B.Base, Nil{}), V.tails(xs))
        & {L.haps(seq, B.Var{1n+pos, List.tail(&2, B.Base, Nil{}), V.tails(xs)}) == L.haps(seq, B.Var{pos, Nil{}, xs}) : Q.Als()})
    case +g <> +u:
      +hf = P.and_true_l(V.firsts_eq((g <> u) <> xs), V.all_long((g <> u) <> xs), hfl)
      +hl = P.and_true_r(V.firsts_eq((g <> u) <> xs), V.all_long((g <> u) <> xs), hfl)
      +hl1 = P.and_true_l(Nat.is_le(2n, Q.len(g <> u)), V.all_long(xs), hl)
      +hl2 = P.and_true_r(Nat.is_le(2n, Q.len(g <> u)), V.all_long(xs), hl)
      +a = RP.vA(seq, pos)
      +b = RP.vB(seq, pos, g <> u)
      +es2 = ST.left_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
      +el2 = ST.left_el(pos, a, g, RP.valid_el(seq, pos, g <> u, xs, hv), RP.vk1(seq, pos, g <> u, xs, hv))
      +hm = {%Equal.sym(Q.Als(), V.tails(xs), L.tails(xs), ST.tails_eq(xs)) :
          {RP.hmap(Q.app(a, [g]), b, _) == RP.hmap(a, b, xs) : Q.Als()};
        ST.left_hmap(a, g, b, xs, hf) : {RP.hmap(Q.app(a, [g]), b, V.tails(xs)) == RP.hmap(a, b, xs) : Q.Als()}}
      +vv = RP.valid_of_rep(seq, 1n+pos, u, V.tails(xs), Q.app(a, [g]), b, es2, el2, P.le_zero_l(pos), hl1,
        ne_tails(xs, hl2), pos, g <> u, xs, hv, hm)
      +hp = trans3(L.haps(seq, B.Var{1n+pos, u, V.tails(xs)}), RP.hmap(Q.app(a, [g]), b, V.tails(xs)), RP.hmap(a, b, xs),
        L.haps(seq, B.Var{pos, g <> u, xs}),
        RP.haps_rep(seq, 1n+pos, u, Q.app(a, [g]), b, es2, el2, V.tails(xs)), hm, RP.valid_haps(seq, pos, g <> u, xs, hv))
      (vv, hp)

# The spec's tests read back
# ==========================

# drop_last keeps the change only if every allele ends like REF.
def lasts_of_drop_last(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +hs: {L.same(seq, L.drop_last(B.Var{pos, r, xs}), B.Var{pos, r, xs}) == True{} : Bool}) ->
  {V.lasts_eq(r <> xs) == True{} : Bool}:
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, {V.lasts_eq(Nil{} <> xs) == True{} : Bool})
    case +g <> +u:
      +a = RP.vA(seq, pos)
      +b = RP.vB(seq, pos, g <> u)
      +es2 = ST.trim_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
      +e = trans3(RP.hmap(a, ST.lst(g, u) <> b, L.inits(xs)), L.haps(seq, B.Var{pos, L.init(g <> u), L.inits(xs)}),
        L.haps(seq, B.Var{pos, g <> u, xs}), RP.hmap(a, b, xs),
        Equal.sym(Q.Als(), L.haps(seq, B.Var{pos, L.init(g <> u), L.inits(xs)}), RP.hmap(a, ST.lst(g, u) <> b, L.inits(xs)),
          RP.haps_rep(seq, pos, L.init(g <> u), a, ST.lst(g, u) <> b, es2, RP.valid_el(seq, pos, g <> u, xs, hv), L.inits(xs))),
        eq_of_same(seq, L.drop_last(B.Var{pos, g <> u, xs}), B.Var{pos, g <> u, xs}, hs),
        Equal.sym(Q.Als(), L.haps(seq, B.Var{pos, g <> u, xs}), RP.hmap(a, b, xs), RP.valid_haps(seq, pos, g <> u, xs, hv)))
      ST.trim_hmap_inv(a, b, ST.lst(g, u), xs, RP.vk4(seq, pos, g <> u, xs, hv), e)

# drop_first keeps the change only if every allele starts like REF.
def firsts_of_drop_first(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +hs: {L.same(seq, L.drop_first(B.Var{pos, r, xs}), B.Var{pos, r, xs}) == True{} : Bool}) ->
  {V.firsts_eq(r <> xs) == True{} : Bool}:
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, {V.firsts_eq(Nil{} <> xs) == True{} : Bool})
    case +g <> +u:
      +a = RP.vA(seq, pos)
      +b = RP.vB(seq, pos, g <> u)
      +es2 = ST.left_es(seq, a, g, u, b, RP.valid_es(seq, pos, g <> u, xs, hv))
      +el2 = ST.left_el(pos, a, g, RP.valid_el(seq, pos, g <> u, xs, hv), RP.vk1(seq, pos, g <> u, xs, hv))
      +e = trans3(RP.hmap(Q.app(a, [g]), b, L.tails(xs)), L.haps(seq, B.Var{1n+pos, u, L.tails(xs)}),
        L.haps(seq, B.Var{pos, g <> u, xs}), RP.hmap(a, b, xs),
        Equal.sym(Q.Als(), L.haps(seq, B.Var{1n+pos, u, L.tails(xs)}), RP.hmap(Q.app(a, [g]), b, L.tails(xs)),
          RP.haps_rep(seq, 1n+pos, u, Q.app(a, [g]), b, es2, el2, L.tails(xs))),
        eq_of_same(seq, L.drop_first(B.Var{pos, g <> u, xs}), B.Var{pos, g <> u, xs}, hs),
        Equal.sym(Q.Als(), L.haps(seq, B.Var{pos, g <> u, xs}), RP.hmap(a, b, xs), RP.valid_haps(seq, pos, g <> u, xs, hv)))
      ST.left_hmap_inv(a, g, b, xs, RP.vk4(seq, pos, g <> u, xs, hv), e)

def drop_last_same(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +he: {V.lasts_eq(r <> xs) == True{} : Bool}) ->
  {L.same(seq, L.drop_last(B.Var{pos, r, xs}), B.Var{pos, r, xs}) == True{} : Bool}:
  same_of_eq(seq, L.drop_last(B.Var{pos, r, xs}), B.Var{pos, r, xs}, trim_haps_l(seq, pos, r, xs, hv, he))

def drop_first_same(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +hf: {V.firsts_eq(r <> xs) == True{} : Bool}) ->
  {L.same(seq, L.drop_first(B.Var{pos, r, xs}), B.Var{pos, r, xs}) == True{} : Bool}:
  match r:
    case Nil{}:
      no_ref(seq, pos, xs, hv, {L.same(seq, L.drop_first(B.Var{pos, Nil{}, xs}), B.Var{pos, Nil{}, xs}) == True{} : Bool})
    case +g <> +u:
      same_of_eq(seq, L.drop_first(B.Var{pos, g <> u, xs}), B.Var{pos, g <> u, xs}, left_haps_l(seq, pos, g, u, xs, hv, hf))
