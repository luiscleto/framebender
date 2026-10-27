import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP
import ./proof_var_steps.bend as ST
import ./proof_var_spec.bend as SP

# A shift by any k that keeps the change makes every allele end like REF:
# after the shift the contig after the window is C ++ B with C non-empty and
# ending where REF ends, so every alternative ends with that base too.

def haps_go_hmap(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als()) ->
  {L.haps.go(seq, p, r, xs) == RP.hmap(Q.take(seq, Nat.sub(p, 1n)), Q.drop(seq, Nat.add(Nat.sub(p, 1n), Q.len(r))), xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %haps_go_hmap(seq, p, r, t) :
        {L.apply(seq, p, r, x) <> L.haps.go(seq, p, r, t) == L.apply(seq, p, r, x) <> _ : Q.Als()}
      {==}

# The contig after the shifted window.
def dlem(+seq: Q.Bs(), +i: Nat, +a2: Q.Bs(), +g: B.Base, +u: Q.Bs(), +b: Q.Bs(),
  +ds: {Q.drop(seq, i) == Q.app(a2, Q.app(g <> u, b)) : Q.Bs()}) ->
  {Q.drop(seq, Nat.add(i, Q.len(L.slice(seq, i, L.len(g <> u))))) == Q.app(Q.drop(Q.app(a2, g <> u), Q.len(g <> u)), b) : Q.Bs()}:
  +r = {g <> u : Q.Bs()}
  +ds_r = Equal.sym(Q.Bs(), Q.drop(seq, i), Q.app(a2, Q.app(r, b)), ds)
  +hle = Q.le_trans(Q.len(r), Q.len(Q.app(r, b)), Q.len(Q.app(a2, Q.app(r, b))), Q.le_len_app_l(r, b), Q.le_len_app_r(a2, Q.app(r, b)))
  %ds_r : {Q.drop(seq, Nat.add(i, Q.len(Q.take(_, Q.len(r))))) == Q.app(Q.drop(Q.app(a2, r), Q.len(r)), b) : Q.Bs()}
  %Equal.sym(Nat, Q.len(Q.take(Q.app(a2, Q.app(r, b)), Q.len(r))), Q.len(r), Q.len_take_le(Q.app(a2, Q.app(r, b)), Q.len(r), hle)) :
    {Q.drop(seq, Nat.add(i, _)) == Q.app(Q.drop(Q.app(a2, r), Q.len(r)), b) : Q.Bs()}
  %Q.drop_drop(seq, i, Q.len(r)) : {_ == Q.app(Q.drop(Q.app(a2, r), Q.len(r)), b) : Q.Bs()}
  %ds_r : {Q.drop(_, Q.len(r)) == Q.app(Q.drop(Q.app(a2, r), Q.len(r)), b) : Q.Bs()}
  %Q.app_assoc(a2, r, b) : {Q.drop(_, Q.len(r)) == Q.app(Q.drop(Q.app(a2, r), Q.len(r)), b) : Q.Bs()}
  Q.drop_app_le(Q.app(a2, r), b, Q.len(r), Q.le_len_app_r(a2, r))

# That non-empty piece C ends where REF ends.
def dlast(+a2: Q.Bs(), +g: B.Base, +u: Q.Bs(), +h: {Nat.is_le(1n, Q.len(a2)) == True{} : Bool}) ->
  {List.last(&2, B.Base, Q.drop(Q.app(a2, g <> u), Q.len(g <> u))) == Some{ST.lst(g, u)} : Maybe<&2, B.Base>}:
  +r = {g <> u : Q.Bs()}
  +x = Q.app(a2, r)
  +n = Q.len(r)
  +hx = {%Equal.sym(Nat, Q.len(x), Nat.add(Q.len(a2), n), Q.len_app(a2, r)) : {Nat.is_le(1n+n, _) == True{} : Bool};
    P.le_add(1n, Q.len(a2), n, n, h, P.le_refl(n)) : {Nat.is_le(1n+n, Q.len(x)) == True{} : Bool}}
  +hc = Q.drop_len1(x, n, hx)
  Equal.trans(Maybe<&2, B.Base>, List.last(&2, B.Base, Q.drop(x, n)), List.last(&2, B.Base, Q.app(Q.take(x, n), Q.drop(x, n))),
    Some{ST.lst(g, u)},
    Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, Q.app(Q.take(x, n), Q.drop(x, n))), List.last(&2, B.Base, Q.drop(x, n)),
      Q.last_app_len(Q.take(x, n), Q.drop(x, n), hc)),
    {%Q.take_drop_r(x, n) : {List.last(&2, B.Base, _) == Some{ST.lst(g, u)} : Maybe<&2, B.Base>};
      Q.last_app(a2, g, u) : {List.last(&2, B.Base, Q.app(Q.take(x, n), Q.drop(x, n))) == Some{ST.lst(g, u)} : Maybe<&2, B.Base>}})

# Each alternative of v, matched against one whose contig ends in C ++ b
# with C ending in l, ends in l.
def n1_hmap(+t: Q.Bs(), +c: Q.Bs(), +b: Q.Bs(), +a: Q.Bs(), +l: B.Base, +xs2: Q.Als(), +xs: Q.Als(),
  +hl: {List.last(&2, B.Base, c) == Some{l} : Maybe<&2, B.Base>}, +hne: {L.all_nonempty(xs) == True{} : Bool},
  +e: {RP.hmap(t, Q.app(c, b), xs2) == RP.hmap(a, b, xs) : Q.Als()}) ->
  {V.same_last(Some{l}, xs) == True{} : Bool}:
  match xs2 xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      Empty.absurd({V.same_last(Some{l}, y <> yt) == True{} : Bool}, Q.anil_ne_cons(Q.app(a, Q.app(y, b)), RP.hmap(a, b, yt), e))
    case +x <> +xt Nil{}:
      Empty.absurd({V.same_last(Some{l}, Nil{}) == True{} : Bool},
        Q.anil_ne_cons(Q.app(t, Q.app(x, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt),
          Equal.sym(Q.Als(), RP.hmap(t, Q.app(c, b), x <> xt), Nil{}, e)))
    case +x <> +xt +y <> +yt:
      match y:
        case Nil{}:
          Empty.absurd({V.same_last(Some{l}, Nil{} <> yt) == True{} : Bool}, P.false_ne_true(hne))
        case +g2 <> +u2:
          +y2 = {g2 <> u2 : Q.Bs()}
          +eh = Q.acons_hd(Q.app(t, Q.app(x, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt), Q.app(a, Q.app(y2, b)), RP.hmap(a, b, yt), e)
          +et = Q.acons_tl(Q.app(t, Q.app(x, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt), Q.app(a, Q.app(y2, b)), RP.hmap(a, b, yt), e)
          +lhs = Equal.trans(Q.Bs(), Q.app(Q.app(t, Q.app(x, c)), b), Q.app(t, Q.app(Q.app(x, c), b)), Q.app(t, Q.app(x, Q.app(c, b))),
            Q.app_assoc(t, Q.app(x, c), b),
            Equal.cong(Q.Bs(), Q.Bs(), z => Q.app(t, z), Q.app(Q.app(x, c), b), Q.app(x, Q.app(c, b)), Q.app_assoc(x, c, b)))
          +e1 = Equal.trans(Q.Bs(), Q.app(Q.app(t, Q.app(x, c)), b), Q.app(t, Q.app(x, Q.app(c, b))), Q.app(Q.app(a, y2), b), lhs,
            Equal.trans(Q.Bs(), Q.app(t, Q.app(x, Q.app(c, b))), Q.app(a, Q.app(y2, b)), Q.app(Q.app(a, y2), b), eh,
              Q.app_assoc_r(a, y2, b)))
          +e2 = Q.cancel_r(Q.app(t, Q.app(x, c)), Q.app(a, y2), b, e1)
          +e3 = Equal.trans(Q.Bs(), Q.app(Q.app(t, x), c), Q.app(t, Q.app(x, c)), Q.app(a, y2), Q.app_assoc(t, x, c), e2)
          +el = Q.some_inj(l, ST.lst(g2, u2), Q.last_eq_gen(Q.app(t, x), c, a, g2, u2, l, hl, e3))
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(y2)), L.all_nonempty(yt), hne)
          Q.and_tt(B.Base.is_eq(l, ST.lst(g2, u2)), V.same_last(Some{l}, yt),
            %el : {B.Base.is_eq(l, _) == True{} : Bool}; Q.base_refl(l),
            n1_hmap(t, c, b, a, l, xt, yt, hl, hne2, et))

# Shifting v by k (1 <= k <= pos - 1) keeps the change only if every allele
# ends like REF.
def n1(+seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +k: Nat, +hv: RP.Valid(seq, pos, g <> u, xs),
  +hk1: {Nat.is_le(1n, k) == True{} : Bool}, +hk2: {Nat.is_le(k, Nat.sub(pos, 1n)) == True{} : Bool},
  +hs: {L.same(seq, L.shift(seq, B.Var{pos, g <> u, xs}, k), B.Var{pos, g <> u, xs}) == True{} : Bool}) ->
  {V.same_last(Some{ST.lst(g, u)}, xs) == True{} : Bool}:
  +r = {g <> u : Q.Bs()}
  +i = Nat.sub(Nat.sub(pos, k), 1n)
  +a = RP.vA(seq, pos)
  +b = RP.vB(seq, pos, r)
  +hi = {%Equal.sym(Nat, Q.len(a), Nat.sub(pos, 1n), RP.valid_el(seq, pos, r, xs, hv)) : {Nat.is_le(1n+i, _) == True{} : Bool};
    Q.lt_sub(pos, k, hk1, hk2) : {Nat.is_le(1n+i, Q.len(a)) == True{} : Bool}}
  +hi0 = Q.le_trans(i, 1n+i, Q.len(a), Q.le_succ(i), hi)
  +a2 = Q.drop(a, i)
  +ds = {%RP.valid_es(seq, pos, r, xs, hv) : {Q.drop(_, i) == Q.app(a2, Q.app(r, b)) : Q.Bs()};
    Q.drop_app_le(a, Q.app(r, b), i, hi0) : {Q.drop(seq, i) == Q.app(a2, Q.app(r, b)) : Q.Bs()}}
  +c = Q.drop(Q.app(a2, r), Q.len(r))
  +t = Q.take(seq, i)
  +d = Q.drop(seq, Nat.add(i, Q.len(L.slice(seq, i, L.len(r)))))
  +xs2 = L.shift.alts(seq, pos, r, i, xs)
  +eh = SP.trans3(RP.hmap(t, d, xs2), L.haps(seq, L.shift(seq, B.Var{pos, r, xs}, k)), L.haps(seq, B.Var{pos, r, xs}), RP.hmap(a, b, xs),
    Equal.sym(Q.Als(), L.haps.go(seq, Nat.sub(pos, k), L.slice(seq, i, L.len(r)), xs2), RP.hmap(t, d, xs2),
      haps_go_hmap(seq, Nat.sub(pos, k), L.slice(seq, i, L.len(r)), xs2)),
    SP.eq_of_same(seq, L.shift(seq, B.Var{pos, r, xs}, k), B.Var{pos, r, xs}, hs),
    Equal.sym(Q.Als(), L.haps(seq, B.Var{pos, r, xs}), RP.hmap(a, b, xs), RP.valid_haps(seq, pos, r, xs, hv)))
  +eh2 = {%dlem(seq, i, a2, g, u, b, ds) : {RP.hmap(t, _, xs2) == RP.hmap(a, b, xs) : Q.Als()};
    eh : {RP.hmap(t, Q.app(c, b), xs2) == RP.hmap(a, b, xs) : Q.Als()}}
  n1_hmap(t, c, b, a, ST.lst(g, u), xs2, xs, dlast(a2, g, u, Q.drop_len1(a, i, hi)), RP.vk4(seq, pos, r, xs, hv), eh2)

# When the alleles do not all end alike, no shift keeps the change.
def not_movable(+k: Nat, +seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +hl: {V.same_last(Some{ST.lst(g, u)}, xs) == False{} : Bool}, +hk: {Nat.is_le(k, Nat.sub(pos, 1n)) == True{} : Bool}) ->
  {L.movable(seq, B.Var{pos, g <> u, xs}, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +v = {B.Var{pos, g <> u, xs} : B.Var}
      +hs = Q.false_of(L.same(seq, L.shift(seq, v, 1n+j), v),
        h => P.true_ne_false(Equal.trans(Bool, True{}, V.same_last(Some{ST.lst(g, u)}, xs), False{},
          Equal.sym(Bool, V.same_last(Some{ST.lst(g, u)}, xs), True{}, n1(seq, pos, g, u, xs, 1n+j, hv, P.le_zero_l(j), hk, h)), hl)))
      %Equal.sym(Bool, L.same(seq, L.shift(seq, v, 1n+j), v), False{}, hs) : {Bool.or(_, L.movable(seq, v, j)) == False{} : Bool}
      not_movable(j, seq, pos, g, u, xs, hv, hl, Q.le_trans(j, 1n+j, Nat.sub(pos, 1n), Q.le_succ(j), hk))
