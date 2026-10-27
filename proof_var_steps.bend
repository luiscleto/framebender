import Base
import ./types.bend as B
import ./norm_var.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP

# One step of the normalizer (trim the last base, shift one base left, trim
# the first base) keeps the change, and the converses used for "no further
# step keeps the change". a, b: a cut of the contig around the variant.

def lst(+g: B.Base, +u: Q.Bs()) -> B.Base:
  List.last.go(&2, B.Base, u, g)

# Code and spec helpers agree
# ===========================

def inits_eq(+xs: Q.Als()) -> {V.inits(xs) == L.inits(xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %inits_eq(t) : {V.init(x) <> V.inits(t) == V.init(x) <> _ : Q.Als()}
      {==}

def tails_eq(+xs: Q.Als()) -> {V.tails(xs) == L.tails(xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %tails_eq(t) : {List.tail(&2, B.Base, x) <> V.tails(t) == List.tail(&2, B.Base, x) <> _ : Q.Als()}
      {==}

def long_eq(+xs: Q.Als()) -> {V.all_long(xs) == L.all_long.go(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %long_eq(t) : {Bool.and(Nat.is_le(2n, Q.len(x)), V.all_long(t)) == Bool.and(Nat.is_le(2n, Q.len(x)), _) : Bool}
      {==}

def total_eq(+xs: Q.Als()) -> {V.total(xs) == L.total(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %total_eq(t) : {Nat.add(Q.len(x), V.total(t)) == Nat.add(Q.len(x), _) : Nat}
      {==}

# Trim the last base
# ==================

def trim_es(+seq: Q.Bs(), +a: Q.Bs(), +g: B.Base, +u: Q.Bs(), +b: Q.Bs(), +es: {Q.app(a, Q.app(g <> u, b)) == seq : Q.Bs()}) ->
  {Q.app(a, Q.app(Q.init(g <> u), lst(g, u) <> b)) == seq : Q.Bs()}:
  %Q.snoc_app(g, u, b) : {Q.app(a, _) == seq : Q.Bs()}
  es

def trim_hmap(+a: Q.Bs(), +b: Q.Bs(), +c: B.Base, +xs: Q.Als(), +h: {V.same_last(Some{c}, xs) == True{} : Bool}) ->
  {RP.hmap(a, c <> b, L.inits(xs)) == RP.hmap(a, b, xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({RP.hmap(a, c <> b, L.inits(Nil{} <> t)) == RP.hmap(a, b, Nil{} <> t) : Q.Als()}, P.false_ne_true(h))
        case +g <> +u:
          +h1 = P.and_true_l(B.Base.is_eq(c, lst(g, u)), V.same_last(Some{c}, t), h)
          +h2 = P.and_true_r(B.Base.is_eq(c, lst(g, u)), V.same_last(Some{c}, t), h)
          +ec = Equal.sym(B.Base, c, lst(g, u), Q.base_sound(c, lst(g, u), h1))
          +eh = {
            %ec : {Q.app(a, Q.app(Q.init(g <> u), _ <> b)) == Q.app(a, Q.app(g <> u, b)) : Q.Bs()}
            %Q.snoc_app(g, u, b) : {Q.app(a, _) == Q.app(a, Q.app(g <> u, b)) : Q.Bs()}
            {==} : {Q.app(a, Q.app(Q.init(g <> u), c <> b)) == Q.app(a, Q.app(g <> u, b)) : Q.Bs()}}
          Q.acons_eq(Q.app(a, Q.app(Q.init(g <> u), c <> b)), RP.hmap(a, c <> b, L.inits(t)),
            Q.app(a, Q.app(g <> u, b)), RP.hmap(a, b, t), eh, trim_hmap(a, b, c, t, h2))

# Trimming the last base keeps the change only if every allele ends with it.
def trim_hmap_inv(+a: Q.Bs(), +b: Q.Bs(), +c: B.Base, +xs: Q.Als(), +hne: {L.all_nonempty(xs) == True{} : Bool},
  +e: {RP.hmap(a, c <> b, L.inits(xs)) == RP.hmap(a, b, xs) : Q.Als()}) ->
  {V.same_last(Some{c}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({V.same_last(Some{c}, Nil{} <> t) == True{} : Bool}, P.false_ne_true(hne))
        case +g <> +u:
          +eh = Q.acons_hd(Q.app(a, Q.app(Q.init(g <> u), c <> b)), RP.hmap(a, c <> b, L.inits(t)),
            Q.app(a, Q.app(g <> u, b)), RP.hmap(a, b, t), e)
          +et = Q.acons_tl(Q.app(a, Q.app(Q.init(g <> u), c <> b)), RP.hmap(a, c <> b, L.inits(t)),
            Q.app(a, Q.app(g <> u, b)), RP.hmap(a, b, t), e)
          +e1 = Q.cancel_l(a, Q.app(Q.init(g <> u), c <> b), Q.app(g <> u, b), eh)
          +e2 = Equal.trans(Q.Bs(), Q.app(Q.init(g <> u), c <> b), Q.app(g <> u, b), Q.app(Q.init(g <> u), lst(g, u) <> b),
            e1, Q.snoc_app(g, u, b))
          +e3 = Q.cons_hd(c, b, lst(g, u), b, Q.cancel_l(Q.init(g <> u), c <> b, lst(g, u) <> b, e2))
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(g <> u)), L.all_nonempty(t), hne)
          Q.and_tt(B.Base.is_eq(c, lst(g, u)), V.same_last(Some{c}, t),
            %e3 : {B.Base.is_eq(c, _) == True{} : Bool}; Q.base_refl(c),
            trim_hmap_inv(a, b, c, t, hne2, et))

# Shift one base left
# ===================

def shift_es(+seq: Q.Bs(), +c0: B.Base, +ct: Q.Bs(), +g: B.Base, +u: Q.Bs(), +b: Q.Bs(),
  +es: {Q.app(c0 <> ct, Q.app(g <> u, b)) == seq : Q.Bs()}) ->
  {Q.app(Q.init(c0 <> ct), Q.app(lst(c0, ct) <> Q.init(g <> u), lst(g, u) <> b)) == seq : Q.Bs()}:
  %Q.snoc_app(g, u, b) : {Q.app(Q.init(c0 <> ct), lst(c0, ct) <> _) == seq : Q.Bs()}
  %Q.snoc_app(c0, ct, Q.app(g <> u, b)) : {_ == seq : Q.Bs()}
  es

def shift_el(+pos: Nat, +c0: B.Base, +ct: Q.Bs(), +el: {Q.len(c0 <> ct) == Nat.sub(pos, 1n) : Nat}) ->
  {Q.len(Q.init(c0 <> ct)) == Nat.sub(Nat.sub(pos, 1n), 1n) : Nat}:
  %Q.len_init_r(c0, ct) : {_ == Nat.sub(Nat.sub(pos, 1n), 1n) : Nat}
  Equal.trans(Nat, Q.len(ct), Nat.sub(Q.len(c0 <> ct), 1n), Nat.sub(Nat.sub(pos, 1n), 1n),
    Equal.sym(Nat, Nat.sub(Q.len(ct), 0n), Q.len(ct), P.sub_zero(Q.len(ct))),
    Equal.cong(Nat, Nat, n => Nat.sub(n, 1n), Q.len(c0 <> ct), Nat.sub(pos, 1n), el))

# Reading index i (the base before the variant) through the whole contig.
def shift_get(+seq: Q.Bs(), +a0: Q.Bs(), +c: B.Base, +rest: Q.Bs(), +i: Nat,
  +es: {Q.app(a0, c <> rest) == seq : Q.Bs()}, +ei: {Q.len(a0) == i : Nat}) ->
  {V.Win.get(0n, seq, i) == Some{c} : Maybe<&2, B.Base>}:
  %Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)) : {V.Win.get.if(_, seq, 0n, i) == Some{c} : Maybe<&2, B.Base>}
  %Equal.sym(Nat, Nat.sub(i, 0n), i, P.sub_zero(i)) : {List.get(&2, B.Base, seq, _) == Some{c} : Maybe<&2, B.Base>}
  %ei : {List.get(&2, B.Base, seq, _) == Some{c} : Maybe<&2, B.Base>}
  %es : {List.get(&2, B.Base, _, Q.len(a0)) == Some{c} : Maybe<&2, B.Base>}
  P.get_append_len(B.Base, a0, c, rest)

def shift_hmap(+a0: Q.Bs(), +c: B.Base, +lr: B.Base, +b: Q.Bs(), +xs: Q.Als(), +h: {V.same_last(Some{lr}, xs) == True{} : Bool}) ->
  {RP.hmap(a0, lr <> b, V.shifted(c, xs)) == RP.hmap(Q.app(a0, [c]), b, xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({RP.hmap(a0, lr <> b, V.shifted(c, Nil{} <> t)) == RP.hmap(Q.app(a0, [c]), b, Nil{} <> t) : Q.Als()},
            P.false_ne_true(h))
        case +g <> +u:
          +h1 = P.and_true_l(B.Base.is_eq(lr, lst(g, u)), V.same_last(Some{lr}, t), h)
          +h2 = P.and_true_r(B.Base.is_eq(lr, lst(g, u)), V.same_last(Some{lr}, t), h)
          +ec = Equal.sym(B.Base, lr, lst(g, u), Q.base_sound(lr, lst(g, u), h1))
          +eh = {
            %ec : {Q.app(a0, c <> Q.app(Q.init(g <> u), _ <> b)) == Q.app(Q.app(a0, [c]), Q.app(g <> u, b)) : Q.Bs()}
            %Q.snoc_app(g, u, b) : {Q.app(a0, c <> _) == Q.app(Q.app(a0, [c]), Q.app(g <> u, b)) : Q.Bs()}
            Q.app_assoc_r(a0, [c], Q.app(g <> u, b))
              : {Q.app(a0, Q.app(c <> Q.init(g <> u), lr <> b)) == Q.app(Q.app(a0, [c]), Q.app(g <> u, b)) : Q.Bs()}}
          Q.acons_eq(Q.app(a0, Q.app(c <> Q.init(g <> u), lr <> b)), RP.hmap(a0, lr <> b, V.shifted(c, t)),
            Q.app(Q.app(a0, [c]), Q.app(g <> u, b)), RP.hmap(Q.app(a0, [c]), b, t), eh, shift_hmap(a0, c, lr, b, t, h2))

# The spec's shift by one base computes the same alleles as the code's.
def shift_ref(+seq: Q.Bs(), +a0: Q.Bs(), +c: B.Base, +g: B.Base, +u: Q.Bs(), +b: Q.Bs(), +i: Nat,
  +es: {Q.app(a0, Q.app(c <> Q.init(g <> u), lst(g, u) <> b)) == seq : Q.Bs()}, +ei: {Q.len(a0) == i : Nat}) ->
  {L.slice(seq, i, L.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}:
  %ei : {Q.take(Q.drop(seq, _), Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %es : {Q.take(Q.drop(_, Q.len(a0)), Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.drop_app0_r(a0, Q.app(c <> Q.init(g <> u), lst(g, u) <> b)) : {Q.take(_, Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.len_init(g, u) : {Q.take(Q.app(c <> Q.init(g <> u), lst(g, u) <> b), 1n+_) == c <> Q.init(g <> u) : Q.Bs()}
  Q.take_app0(c <> Q.init(g <> u), lst(g, u) <> b)

def shift_alt(+a0: Q.Bs(), +c: B.Base, +b: Q.Bs(), +i: Nat, +ei: {Q.len(a0) == i : Nat}, +g: B.Base, +u: Q.Bs()) ->
  {L.slice(Q.app(Q.app(a0, [c]), Q.app(g <> u, b)), i, L.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}:
  %ei : {Q.take(Q.drop(Q.app(Q.app(a0, [c]), Q.app(g <> u, b)), _), Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.app_assoc_r(a0, [c], Q.app(g <> u, b)) : {Q.take(Q.drop(_, Q.len(a0)), Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.drop_app0_r(a0, c <> Q.app(g <> u, b)) : {Q.take(_, Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.snoc_app_r(g, u, b) : {Q.take(c <> _, Q.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.len_init(g, u) : {Q.take(c <> Q.app(Q.init(g <> u), lst(g, u) <> b), 1n+_) == c <> Q.init(g <> u) : Q.Bs()}
  %Q.take_app0(Q.init(g <> u), lst(g, u) <> b) : {c <> Q.take(Q.app(Q.init(g <> u), lst(g, u) <> b), Q.len(Q.init(g <> u))) == c <> _ : Q.Bs()}
  {==}

def shift_alts(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +a0: Q.Bs(), +c: B.Base, +b: Q.Bs(), +i: Nat,
  +es: {Q.app(Q.app(a0, [c]), Q.app(r, b)) == seq : Q.Bs()}, +el: {Q.len(Q.app(a0, [c])) == Nat.sub(pos, 1n) : Nat},
  +ei: {Q.len(a0) == i : Nat}, +xs: Q.Als(), +hne: {L.all_nonempty(xs) == True{} : Bool}) ->
  {L.shift.alts(seq, pos, r, i, xs) == V.shifted(c, xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({L.shift.alts(seq, pos, r, i, Nil{} <> t) == V.shifted(c, Nil{} <> t) : Q.Als()}, P.false_ne_true(hne))
        case +g <> +u:
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(g <> u)), L.all_nonempty(t), hne)
          +eh = {
            %Equal.sym(Q.Bs(), L.apply(seq, pos, r, g <> u), Q.app(Q.app(a0, [c]), Q.app(g <> u, b)), RP.apply_rep(seq, pos, r, g <> u, Q.app(a0, [c]), b, es, el)) : {L.slice(_, i, L.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}
            shift_alt(a0, c, b, i, ei, g, u) : {L.slice(L.apply(seq, pos, r, g <> u), i, L.len(g <> u)) == c <> Q.init(g <> u) : Q.Bs()}}
          Q.acons_eq(L.slice(L.apply(seq, pos, r, g <> u), i, L.len(g <> u)), L.shift.alts(seq, pos, r, i, t),
            c <> Q.init(g <> u), V.shifted(c, t), eh, shift_alts(seq, pos, r, a0, c, b, i, es, el, ei, t, hne2))

# Trim the first base
# ===================

def left_es(+seq: Q.Bs(), +a: Q.Bs(), +g: B.Base, +u: Q.Bs(), +b: Q.Bs(), +es: {Q.app(a, Q.app(g <> u, b)) == seq : Q.Bs()}) ->
  {Q.app(Q.app(a, [g]), Q.app(u, b)) == seq : Q.Bs()}:
  %Q.app_assoc_r(a, [g], Q.app(u, b)) : {_ == seq : Q.Bs()}
  es

def left_el(+pos: Nat, +a: Q.Bs(), +g: B.Base, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}, h1: {Nat.is_le(1n, pos) == True{} : Bool}) ->
  {Q.len(Q.app(a, [g])) == Nat.sub(1n+pos, 1n) : Nat}:
  Equal.trans(Nat, Q.len(Q.app(a, [g])), Nat.add(Q.len(a), 1n), Nat.sub(1n+pos, 1n), Q.len_app(a, [g]),
    Equal.trans(Nat, Nat.add(Q.len(a), 1n), 1n+Q.len(a), Nat.sub(1n+pos, 1n), P.add_one(Q.len(a)),
      Equal.trans(Nat, 1n+Q.len(a), 1n+Nat.sub(pos, 1n), Nat.sub(1n+pos, 1n),
        Equal.cong(Nat, Nat, n => 1n+n, Q.len(a), Nat.sub(pos, 1n), el),
        Equal.trans(Nat, 1n+Nat.sub(pos, 1n), pos, Nat.sub(1n+pos, 1n), Q.succ_sub_one(pos, h1),
          Equal.sym(Nat, Nat.sub(pos, 0n), pos, P.sub_zero(pos))))))

def left_hmap(+a: Q.Bs(), +g: B.Base, +b: Q.Bs(), +xs: Q.Als(), +h: {V.same_first(Some{g}, xs) == True{} : Bool}) ->
  {RP.hmap(Q.app(a, [g]), b, L.tails(xs)) == RP.hmap(a, b, xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({RP.hmap(Q.app(a, [g]), b, L.tails(Nil{} <> t)) == RP.hmap(a, b, Nil{} <> t) : Q.Als()}, P.false_ne_true(h))
        case +g2 <> +u2:
          +h1 = P.and_true_l(B.Base.is_eq(g, g2), V.same_first(Some{g}, t), h)
          +h2 = P.and_true_r(B.Base.is_eq(g, g2), V.same_first(Some{g}, t), h)
          +eg = Q.base_sound(g, g2, h1)
          +eh = {
            %Q.app_assoc_r(a, [g], Q.app(u2, b)) : {_ == Q.app(a, Q.app(g2 <> u2, b)) : Q.Bs()}
            %eg : {Q.app(a, g <> Q.app(u2, b)) == Q.app(a, _ <> Q.app(u2, b)) : Q.Bs()}
            {==} : {Q.app(Q.app(a, [g]), Q.app(u2, b)) == Q.app(a, Q.app(g2 <> u2, b)) : Q.Bs()}}
          Q.acons_eq(Q.app(Q.app(a, [g]), Q.app(u2, b)), RP.hmap(Q.app(a, [g]), b, L.tails(t)),
            Q.app(a, Q.app(g2 <> u2, b)), RP.hmap(a, b, t), eh, left_hmap(a, g, b, t, h2))

# Trimming the first base keeps the change only if every allele starts with it.
def left_hmap_inv(+a: Q.Bs(), +g: B.Base, +b: Q.Bs(), +xs: Q.Als(), +hne: {L.all_nonempty(xs) == True{} : Bool},
  +e: {RP.hmap(Q.app(a, [g]), b, L.tails(xs)) == RP.hmap(a, b, xs) : Q.Als()}) ->
  {V.same_first(Some{g}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({V.same_first(Some{g}, Nil{} <> t) == True{} : Bool}, P.false_ne_true(hne))
        case +g2 <> +u2:
          +eh = Q.acons_hd(Q.app(Q.app(a, [g]), Q.app(u2, b)), RP.hmap(Q.app(a, [g]), b, L.tails(t)),
            Q.app(a, Q.app(g2 <> u2, b)), RP.hmap(a, b, t), e)
          +et = Q.acons_tl(Q.app(Q.app(a, [g]), Q.app(u2, b)), RP.hmap(Q.app(a, [g]), b, L.tails(t)),
            Q.app(a, Q.app(g2 <> u2, b)), RP.hmap(a, b, t), e)
          +e1 = Equal.trans(Q.Bs(), Q.app(a, g <> Q.app(u2, b)), Q.app(Q.app(a, [g]), Q.app(u2, b)), Q.app(a, Q.app(g2 <> u2, b)),
            Q.app_assoc_r(a, [g], Q.app(u2, b)), eh)
          +e2 = Q.cons_hd(g, Q.app(u2, b), g2, Q.app(u2, b), Q.cancel_l(a, g <> Q.app(u2, b), g2 <> Q.app(u2, b), e1))
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(g2 <> u2)), L.all_nonempty(t), hne)
          Q.and_tt(B.Base.is_eq(g, g2), V.same_first(Some{g}, t),
            %e2 : {B.Base.is_eq(g, _) == True{} : Bool}; Q.base_refl(g),
            left_hmap_inv(a, g, b, t, hne2, et))
