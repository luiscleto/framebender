import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP
import ./proof_var_steps.bend as ST
import ./proof_var_spec.bend as SP
import ./proof_var_n1.bend as N

# Uniqueness: two valid normalized variants making the same change are equal.
# Cut both: seq = (A ++ REF) ++ B = (A2 ++ REF2) ++ B2.
# - One window ends later (u1): its alleles all end alike, so it starts at
#   position 1 (left-aligned) and, being parsimonious, has a one-base allele;
#   but it holds the other window plus at least one base: contradiction.
# - Same end, one starts earlier (u2): its alleles all start alike and are
#   long, so it is not parsimonious.
# - Same window (u3): equal.

def hmap_inj(+a: Q.Bs(), +b: Q.Bs(), +xs: Q.Als(), +ys: Q.Als(), +e: {RP.hmap(a, b, xs) == RP.hmap(a, b, ys) : Q.Als()}) -> {xs == ys : Q.Als()}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      Empty.absurd({Nil{} == y <> yt : Q.Als()}, Q.anil_ne_cons(Q.app(a, Q.app(y, b)), RP.hmap(a, b, yt), e))
    case +x <> +xt Nil{}:
      Empty.absurd({x <> xt == Nil{} : Q.Als()},
        Q.anil_ne_cons(Q.app(a, Q.app(x, b)), RP.hmap(a, b, xt), Equal.sym(Q.Als(), RP.hmap(a, b, x <> xt), Nil{}, e)))
    case +x <> +xt +y <> +yt:
      +eh = Q.acons_hd(Q.app(a, Q.app(x, b)), RP.hmap(a, b, xt), Q.app(a, Q.app(y, b)), RP.hmap(a, b, yt), e)
      +et = Q.acons_tl(Q.app(a, Q.app(x, b)), RP.hmap(a, b, xt), Q.app(a, Q.app(y, b)), RP.hmap(a, b, yt), e)
      Q.acons_eq(x, xt, y, yt, Q.cancel_r(x, y, b, Q.cancel_l(a, Q.app(x, b), Q.app(y, b), eh)), hmap_inj(a, b, xt, yt, et))

def reassoc(+t: Q.Bs(), +x: Q.Bs(), +c: Q.Bs(), +b: Q.Bs()) -> {Q.app(Q.app(t, Q.app(x, c)), b) == Q.app(t, Q.app(x, Q.app(c, b))) : Q.Bs()}:
  Equal.trans(Q.Bs(), Q.app(Q.app(t, Q.app(x, c)), b), Q.app(t, Q.app(Q.app(x, c), b)), Q.app(t, Q.app(x, Q.app(c, b))),
    Q.app_assoc(t, Q.app(x, c), b),
    Equal.cong(Q.Bs(), Q.Bs(), z => Q.app(t, z), Q.app(Q.app(x, c), b), Q.app(x, Q.app(c, b)), Q.app_assoc(x, c, b)))

# Matched against alternatives cut with nothing before them, each is t ++ x ++ c.
def u1_long(+t: Q.Bs(), +c: Q.Bs(), +b: Q.Bs(), +hc: {Nat.is_le(1n, Q.len(c)) == True{} : Bool}, +xs2: Q.Als(), +xs: Q.Als(),
  +hne: {L.all_nonempty(xs) == True{} : Bool}, +e: {RP.hmap(t, Q.app(c, b), xs) == RP.hmap(Nil{}, b, xs2) : Q.Als()}) ->
  {L.all_long.go(xs2) == True{} : Bool}:
  match xs2 xs:
    case Nil{} Nil{}:
      {==}
    case +y <> +yt Nil{}:
      Empty.absurd({L.all_long.go(y <> yt) == True{} : Bool}, Q.anil_ne_cons(Q.app(y, b), RP.hmap(Nil{}, b, yt), e))
    case Nil{} +x <> +xt:
      Empty.absurd({L.all_long.go(Nil{}) == True{} : Bool},
        Q.anil_ne_cons(Q.app(t, Q.app(x, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt),
          Equal.sym(Q.Als(), RP.hmap(t, Q.app(c, b), x <> xt), Nil{}, e)))
    case +y <> +yt +x <> +xt:
      match x:
        case Nil{}:
          Empty.absurd({L.all_long.go(y <> yt) == True{} : Bool}, P.false_ne_true(hne))
        case +g <> +u:
          +x2 = {g <> u : Q.Bs()}
          +eh = Q.acons_hd(Q.app(t, Q.app(x2, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt), Q.app(y, b), RP.hmap(Nil{}, b, yt), e)
          +et = Q.acons_tl(Q.app(t, Q.app(x2, Q.app(c, b))), RP.hmap(t, Q.app(c, b), xt), Q.app(y, b), RP.hmap(Nil{}, b, yt), e)
          +e2 = Q.cancel_r(Q.app(t, Q.app(x2, c)), y, b,
            Equal.trans(Q.Bs(), Q.app(Q.app(t, Q.app(x2, c)), b), Q.app(t, Q.app(x2, Q.app(c, b))), Q.app(y, b), reassoc(t, x2, c, b), eh))
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(x2)), L.all_nonempty(xt), hne)
          Q.and_tt(Nat.is_le(2n, Q.len(y)), L.all_long.go(yt),
            %e2 : {Nat.is_le(2n, Q.len(_)) == True{} : Bool}; Q.len2(t, g, u, c, hc),
            u1_long(t, c, b, hc, yt, xt, hne2, et))

def u2_elem(+t: Q.Bs(), +m: Q.Bs(), +b: Q.Bs(), +x: Q.Bs(), +y: Q.Bs(),
  +eh: {Q.app(t, Q.app(x, b)) == Q.app(Q.app(t, m), Q.app(y, b)) : Q.Bs()}) -> {x == Q.app(m, y) : Q.Bs()}:
  +e1 = Equal.trans(Q.Bs(), Q.app(t, Q.app(x, b)), Q.app(Q.app(t, m), Q.app(y, b)), Q.app(t, Q.app(m, Q.app(y, b))), eh,
    Q.app_assoc(t, m, Q.app(y, b)))
  +e2 = Q.cancel_l(t, Q.app(x, b), Q.app(m, Q.app(y, b)), e1)
  Q.cancel_r(x, Q.app(m, y), b, Equal.trans(Q.Bs(), Q.app(x, b), Q.app(m, Q.app(y, b)), Q.app(Q.app(m, y), b), e2, Q.app_assoc_r(m, y, b)))

# Alternatives of the window starting earlier all start with its extra base e0.
def u2_first(+t: Q.Bs(), +e0: B.Base, +et: Q.Bs(), +b: Q.Bs(), +xs: Q.Als(), +xs2: Q.Als(),
  +e: {RP.hmap(t, b, xs) == RP.hmap(Q.app(t, e0 <> et), b, xs2) : Q.Als()}) -> {V.same_first(Some{e0}, xs) == True{} : Bool}:
  match xs xs2:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      Empty.absurd({V.same_first(Some{e0}, Nil{}) == True{} : Bool},
        Q.anil_ne_cons(Q.app(Q.app(t, e0 <> et), Q.app(y, b)), RP.hmap(Q.app(t, e0 <> et), b, yt), e))
    case +x <> +xt Nil{}:
      Empty.absurd({V.same_first(Some{e0}, x <> xt) == True{} : Bool},
        Q.anil_ne_cons(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Equal.sym(Q.Als(), RP.hmap(t, b, x <> xt), Nil{}, e)))
    case +x <> +xt +y <> +yt:
      +m = {e0 <> et : Q.Bs()}
      +eh = Q.acons_hd(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Q.app(Q.app(t, m), Q.app(y, b)), RP.hmap(Q.app(t, m), b, yt), e)
      +et2 = Q.acons_tl(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Q.app(Q.app(t, m), Q.app(y, b)), RP.hmap(Q.app(t, m), b, yt), e)
      +ex = u2_elem(t, m, b, x, y, eh)
      %Equal.sym(Q.Bs(), x, Q.app(m, y), ex) : {Bool.and(V.opt_eq(Some{e0}, List.head(&2, B.Base, _)), V.same_first(Some{e0}, xt)) == True{} : Bool}
      Q.and_tt(B.Base.is_eq(e0, e0), V.same_first(Some{e0}, xt), Q.base_refl(e0), u2_first(t, e0, et, b, xt, yt, et2))

def u2_long(+t: Q.Bs(), +e0: B.Base, +et: Q.Bs(), +b: Q.Bs(), +xs: Q.Als(), +xs2: Q.Als(), +hne2: {L.all_nonempty(xs2) == True{} : Bool},
  +e: {RP.hmap(t, b, xs) == RP.hmap(Q.app(t, e0 <> et), b, xs2) : Q.Als()}) -> {L.all_long.go(xs) == True{} : Bool}:
  match xs xs2:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      Empty.absurd({L.all_long.go(Nil{}) == True{} : Bool},
        Q.anil_ne_cons(Q.app(Q.app(t, e0 <> et), Q.app(y, b)), RP.hmap(Q.app(t, e0 <> et), b, yt), e))
    case +x <> +xt Nil{}:
      Empty.absurd({L.all_long.go(x <> xt) == True{} : Bool},
        Q.anil_ne_cons(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Equal.sym(Q.Als(), RP.hmap(t, b, x <> xt), Nil{}, e)))
    case +x <> +xt +y <> +yt:
      match y:
        case Nil{}:
          Empty.absurd({L.all_long.go(x <> xt) == True{} : Bool}, P.false_ne_true(hne2))
        case +g <> +u:
          +m = {e0 <> et : Q.Bs()}
          +y2 = {g <> u : Q.Bs()}
          +eh = Q.acons_hd(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Q.app(Q.app(t, m), Q.app(y2, b)), RP.hmap(Q.app(t, m), b, yt), e)
          +et2 = Q.acons_tl(Q.app(t, Q.app(x, b)), RP.hmap(t, b, xt), Q.app(Q.app(t, m), Q.app(y2, b)), RP.hmap(Q.app(t, m), b, yt), e)
          +ex = u2_elem(t, m, b, x, y2, eh)
          +hne3 = P.and_true_r(Nat.is_le(1n, Q.len(y2)), L.all_nonempty(yt), hne2)
          Q.and_tt(Nat.is_le(2n, Q.len(x)), L.all_long.go(xt),
            %Equal.sym(Q.Bs(), x, Q.app(m, y2), ex) : {Nat.is_le(2n, Q.len(_)) == True{} : Bool};
              Q.le_trans(1n, Q.len(y2), Q.len(Q.app(et, y2)), P.le_zero_l(Q.len(u)), Q.le_len_app_r(et, y2)),
            u2_long(t, e0, et, b, xt, yt, hne3, et2))

def Norm(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Data:
  {L.normalized(seq, B.Var{p, r, xs}) == True{} : Bool}

def par_of(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hn: Norm(seq, p, r, xs)) -> {L.parsimonious(seq, B.Var{p, r, xs}) == True{} : Bool}:
  P.and_true_r(L.left_aligned(seq, B.Var{p, r, xs}), L.parsimonious(seq, B.Var{p, r, xs}), hn)

def la_of(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hn: Norm(seq, p, r, xs)) -> {L.left_aligned(seq, B.Var{p, r, xs}) == True{} : Bool}:
  P.and_true_l(L.left_aligned(seq, B.Var{p, r, xs}), L.parsimonious(seq, B.Var{p, r, xs}), hn)

# A long variant that a drop keeps the change of is not parsimonious.
def not_par(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hn: Norm(seq, p, r, xs),
  +hl: {L.all_long(B.Var{p, r, xs}) == True{} : Bool},
  +hd: {Bool.or(L.same(seq, L.drop_first(B.Var{p, r, xs}), B.Var{p, r, xs}), L.same(seq, L.drop_last(B.Var{p, r, xs}), B.Var{p, r, xs})) == True{} : Bool}) ->
  Empty:
  +v = {B.Var{p, r, xs} : B.Var}
  +d = Bool.or(L.same(seq, L.drop_first(v), v), L.same(seq, L.drop_last(v), v))
  Q.not_tt(Bool.and(L.all_long(v), d), par_of(seq, p, r, xs, hn), Q.and_tt(L.all_long(v), d, hl, hd))

# The window of w ends later than v's (by c <> ct).
def u1(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(),
  +hv: RP.Valid(seq, pos, r, xs), +hw: RP.Valid(seq, pos2, r2, xs2), +hnw: Norm(seq, pos2, r2, xs2),
  +a: Q.Bs(), +bt: Q.Bs(), +a2: Q.Bs(), +b2: Q.Bs(), +el2: {Q.len(a2) == Nat.sub(pos2, 1n) : Nat},
  +hh: {RP.hmap(a, bt, xs) == RP.hmap(a2, b2, xs2) : Q.Als()}, +c: B.Base, +ct: Q.Bs(),
  +eq: {Q.app(a2, r2) == Q.app(Q.app(a, r), c <> ct) : Q.Bs()}, +eb: {bt == Q.app(c <> ct, b2) : Q.Bs()}) -> Empty:
  match r r2 a2:
    case Nil{} _ _:
      SP.no_ref(seq, pos, xs, hv, Empty)
    case +g <> +u Nil{} _:
      SP.no_ref(seq, pos2, xs2, hw, Empty)
    case +g <> +u +g2 <> +u2 +d <> +dt:
      +w = {B.Var{pos2, g2 <> u2, xs2} : B.Var}
      +hl = Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, g2 <> u2), List.last(&2, B.Base, c <> ct),
        Q.last_eq(d <> dt, g2, u2, Q.app(a, g <> u), c, ct, eq))
      +hh2 = {%eb : {RP.hmap(a, _, xs) == RP.hmap(d <> dt, b2, xs2) : Q.Als()};
        hh : {RP.hmap(a, Q.app(c <> ct, b2), xs) == RP.hmap(d <> dt, b2, xs2) : Q.Als()}}
      +lw = N.n1_hmap(a, c <> ct, b2, d <> dt, ST.lst(g2, u2), xs, xs2, hl, RP.vk4(seq, pos2, g2 <> u2, xs2, hw), hh2)
      +hs2 = Q.one_le_sub(pos2, %el2 : {Nat.is_le(1n, _) == True{} : Bool}; P.le_zero_l(Q.len(dt)))
      +mv = SP.movable_one(Q.len(dt), seq, w, SP.shift_one(seq, pos2, g2, u2, xs2, hw, lw, hs2))
      +la = {%Equal.sym(Nat, Q.len(d <> dt), Nat.sub(pos2, 1n), el2) : {Bool.not(L.movable(seq, w, _)) == True{} : Bool};
        la_of(seq, pos2, g2 <> u2, xs2, hnw) : {Bool.not(L.movable(seq, w, 1n+Q.len(dt))) == True{} : Bool}}
      Q.not_tt(L.movable(seq, w, 1n+Q.len(dt)), la, mv)
    case +g <> +u +g2 <> +u2 Nil{}:
      +w = {B.Var{pos2, g2 <> u2, xs2} : B.Var}
      +hl = Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, g2 <> u2), List.last(&2, B.Base, c <> ct),
        Q.last_eq(Nil{}, g2, u2, Q.app(a, g <> u), c, ct, eq))
      +hh2 = {%eb : {RP.hmap(a, _, xs) == RP.hmap(Nil{}, b2, xs2) : Q.Als()};
        hh : {RP.hmap(a, Q.app(c <> ct, b2), xs) == RP.hmap(Nil{}, b2, xs2) : Q.Als()}}
      +lw = N.n1_hmap(a, c <> ct, b2, Nil{}, ST.lst(g2, u2), xs, xs2, hl, RP.vk4(seq, pos2, g2 <> u2, xs2, hw), hh2)
      +hr2 = {%Equal.sym(Q.Bs(), g2 <> u2, Q.app(Q.app(a, g <> u), c <> ct), eq) : {Nat.is_le(2n, Q.len(_)) == True{} : Bool};
        %Q.app_assoc_r(a, g <> u, c <> ct) : {Nat.is_le(2n, Q.len(_)) == True{} : Bool};
          Q.len2(a, g, u, c <> ct, P.le_zero_l(Q.len(ct)))
        : {Nat.is_le(2n, Q.len(g2 <> u2)) == True{} : Bool}}
      +hx2 = u1_long(a, c <> ct, b2, P.le_zero_l(Q.len(ct)), xs2, xs, RP.vk4(seq, pos, g <> u, xs, hv), hh2)
      +hal = Q.and_tt(Nat.is_le(2n, Q.len(g2 <> u2)), L.all_long.go(xs2), hr2, hx2)
      not_par(seq, pos2, g2 <> u2, xs2, hnw, hal,
        Q.or_tt_r(L.same(seq, L.drop_first(w), w), L.same(seq, L.drop_last(w), w),
          SP.drop_last_same(seq, pos2, g2 <> u2, xs2, hw, lw)))

# Same end; the window of v starts earlier (by e0 <> et).
def u2(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(),
  +hv: RP.Valid(seq, pos, r, xs), +hw: RP.Valid(seq, pos2, r2, xs2), +hnv: Norm(seq, pos, r, xs),
  +a: Q.Bs(), +b: Q.Bs(), +e0: B.Base, +et: Q.Bs(),
  +hh: {RP.hmap(a, b, xs) == RP.hmap(Q.app(a, e0 <> et), b, xs2) : Q.Als()}, +er: {r == Q.app(e0 <> et, r2) : Q.Bs()}) -> Empty:
  match r r2:
    case Nil{} _:
      SP.no_ref(seq, pos, xs, hv, Empty)
    case +g <> +u Nil{}:
      SP.no_ref(seq, pos2, xs2, hw, Empty)
    case +g <> +u +g2 <> +u2:
      +v = {B.Var{pos, g <> u, xs} : B.Var}
      +eg = Q.cons_hd(g, u, e0, Q.app(et, g2 <> u2), er)
      +hf = {%Equal.sym(B.Base, g, e0, eg) : {V.same_first(Some{_}, xs) == True{} : Bool};
        u2_first(a, e0, et, b, xs, xs2, hh) : {V.same_first(Some{g}, xs) == True{} : Bool}}
      +hr = {%Equal.sym(Q.Bs(), g <> u, Q.app(e0 <> et, g2 <> u2), er) : {Nat.is_le(2n, Q.len(_)) == True{} : Bool};
        Q.le_trans(1n, Q.len(g2 <> u2), Q.len(Q.app(et, g2 <> u2)), P.le_zero_l(Q.len(u2)), Q.le_len_app_r(et, g2 <> u2))
        : {Nat.is_le(2n, Q.len(g <> u)) == True{} : Bool}}
      +hal = Q.and_tt(Nat.is_le(2n, Q.len(g <> u)), L.all_long.go(xs), hr, u2_long(a, e0, et, b, xs, xs2, RP.vk4(seq, pos2, g2 <> u2, xs2, hw), hh))
      not_par(seq, pos, g <> u, xs, hnv, hal,
        Q.or_tt_l(L.same(seq, L.drop_first(v), v), L.same(seq, L.drop_last(v), v), SP.drop_first_same(seq, pos, g <> u, xs, hv, hf)))

# Same window.
def u3(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(),
  +hv: RP.Valid(seq, pos, r, xs), +hw: RP.Valid(seq, pos2, r2, xs2), +a: Q.Bs(), +b: Q.Bs(),
  +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}, +el2: {Q.len(a) == Nat.sub(pos2, 1n) : Nat}, +er: {r == r2 : Q.Bs()},
  +hh: {RP.hmap(a, b, xs) == RP.hmap(a, b, xs2) : Q.Als()}) -> {B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var}:
  +es = Equal.trans(Nat, Nat.sub(pos, 1n), Q.len(a), Nat.sub(pos2, 1n), Equal.sym(Nat, Q.len(a), Nat.sub(pos, 1n), el), el2)
  +ep = Equal.trans(Nat, pos, 1n+Nat.sub(pos, 1n), pos2, Equal.sym(Nat, 1n+Nat.sub(pos, 1n), pos, Q.succ_sub_one(pos, RP.vk1(seq, pos, r, xs, hv))),
    Equal.trans(Nat, 1n+Nat.sub(pos, 1n), 1n+Nat.sub(pos2, 1n), pos2, Equal.cong(Nat, Nat, n => 1n+n, Nat.sub(pos, 1n), Nat.sub(pos2, 1n), es),
      Q.succ_sub_one(pos2, RP.vk1(seq, pos2, r2, xs2, hw))))
  %ep : {B.Var{pos, r, xs} == B.Var{_, r2, xs2} : B.Var}
  %er : {B.Var{pos, r, xs} == B.Var{pos, _, xs2} : B.Var}
  %hmap_inj(a, b, xs, xs2, hh) : {B.Var{pos, r, xs} == B.Var{pos, r, _} : B.Var}
  {==}

def u_same(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(),
  +hv: RP.Valid(seq, pos, r, xs), +hw: RP.Valid(seq, pos2, r2, xs2), +hnv: Norm(seq, pos, r, xs), +hnw: Norm(seq, pos2, r2, xs2),
  +a: Q.Bs(), +a2: Q.Bs(), +b: Q.Bs(), +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}, +el2: {Q.len(a2) == Nat.sub(pos2, 1n) : Nat},
  +hh: {RP.hmap(a, b, xs) == RP.hmap(a2, b, xs2) : Q.Als()}, cu: Or(Q.Cut(a, r, a2, r2), Q.Cut(a2, r2, a, r))) ->
  {B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var}:
  match cu:
    case Inl{wt}:
      match wt:
        case (+m, pr):
          match m:
            case Nil{}:
              match pr:
                case (+ea, +er):
                  +ea2 = Equal.trans(Q.Bs(), a2, Q.app(a, Nil{}), a, ea, Q.app_nil(a))
                  u3(seq, pos, r, xs, pos2, r2, xs2, hv, hw, a, b, el,
                    {%ea2 : {Q.len(_) == Nat.sub(pos2, 1n) : Nat}; el2 : {Q.len(a) == Nat.sub(pos2, 1n) : Nat}}, er,
                    {%ea2 : {RP.hmap(a, b, xs) == RP.hmap(_, b, xs2) : Q.Als()}; hh : {RP.hmap(a, b, xs) == RP.hmap(a, b, xs2) : Q.Als()}})
            case +e0 <> +et:
              match pr:
                case (+ea, +er):
                  Empty.absurd({B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var},
                    u2(seq, pos, r, xs, pos2, r2, xs2, hv, hw, hnv, a, b, e0, et,
                      {%ea : {RP.hmap(a, b, xs) == RP.hmap(_, b, xs2) : Q.Als()};
                        hh : {RP.hmap(a, b, xs) == RP.hmap(Q.app(a, e0 <> et), b, xs2) : Q.Als()}}, er))
    case Inr{wt}:
      match wt:
        case (+m, pr):
          match m:
            case Nil{}:
              match pr:
                case (+ea, +er):
                  +ea2 = Equal.sym(Q.Bs(), a, a2, Equal.trans(Q.Bs(), a, Q.app(a2, Nil{}), a2, ea, Q.app_nil(a2)))
                  u3(seq, pos, r, xs, pos2, r2, xs2, hv, hw, a, b, el,
                    {%ea2 : {Q.len(_) == Nat.sub(pos2, 1n) : Nat}; el2 : {Q.len(a) == Nat.sub(pos2, 1n) : Nat}},
                    Equal.sym(Q.Bs(), r2, r, er),
                    {%ea2 : {RP.hmap(a, b, xs) == RP.hmap(_, b, xs2) : Q.Als()}; hh : {RP.hmap(a, b, xs) == RP.hmap(a, b, xs2) : Q.Als()}})
            case +e0 <> +et:
              match pr:
                case (+ea, +er):
                  Empty.absurd({B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var},
                    u2(seq, pos2, r2, xs2, pos, r, xs, hw, hv, hnw, a2, b, e0, et,
                      {%ea : {RP.hmap(a2, b, xs2) == RP.hmap(_, b, xs) : Q.Als()};
                        Equal.sym(Q.Als(), RP.hmap(a, b, xs), RP.hmap(a2, b, xs2), hh)
                        : {RP.hmap(a2, b, xs2) == RP.hmap(Q.app(a2, e0 <> et), b, xs) : Q.Als()}}, er))

def u_top(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(),
  +hv: RP.Valid(seq, pos, r, xs), +hw: RP.Valid(seq, pos2, r2, xs2), +hnv: Norm(seq, pos, r, xs), +hnw: Norm(seq, pos2, r2, xs2),
  +a: Q.Bs(), +bt: Q.Bs(), +a2: Q.Bs(), +b2: Q.Bs(), +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}, +el2: {Q.len(a2) == Nat.sub(pos2, 1n) : Nat},
  +hh: {RP.hmap(a, bt, xs) == RP.hmap(a2, b2, xs2) : Q.Als()},
  cu: Or(Q.Cut(Q.app(a, r), bt, Q.app(a2, r2), b2), Q.Cut(Q.app(a2, r2), b2, Q.app(a, r), bt))) ->
  {B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var}:
  match cu:
    case Inl{wt}:
      match wt:
        case (+m, pr):
          match m:
            case Nil{}:
              match pr:
                case (+eq, +eb):
                  +e1 = Equal.sym(Q.Bs(), Q.app(a2, r2), Q.app(a, r), Equal.trans(Q.Bs(), Q.app(a2, r2), Q.app(Q.app(a, r), Nil{}), Q.app(a, r), eq, Q.app_nil(Q.app(a, r))))
                  u_same(seq, pos, r, xs, pos2, r2, xs2, hv, hw, hnv, hnw, a, a2, b2, el, el2,
                    {%eb : {RP.hmap(a, _, xs) == RP.hmap(a2, b2, xs2) : Q.Als()}; hh : {RP.hmap(a, b2, xs) == RP.hmap(a2, b2, xs2) : Q.Als()}},
                    Q.cuts(a, r, a2, r2, e1))
            case +c <> +ct:
              match pr:
                case (+eq, +eb):
                  Empty.absurd({B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var},
                    u1(seq, pos, r, xs, pos2, r2, xs2, hv, hw, hnw, a, bt, a2, b2, el2, hh, c, ct, eq, eb))
    case Inr{wt}:
      match wt:
        case (+m, pr):
          match m:
            case Nil{}:
              match pr:
                case (+ep, +ec):
                  +e1 = Equal.trans(Q.Bs(), Q.app(a, r), Q.app(Q.app(a2, r2), Nil{}), Q.app(a2, r2), ep, Q.app_nil(Q.app(a2, r2)))
                  u_same(seq, pos, r, xs, pos2, r2, xs2, hv, hw, hnv, hnw, a, a2, bt, el, el2,
                    {%ec : {RP.hmap(a, bt, xs) == RP.hmap(a2, _, xs2) : Q.Als()}; hh : {RP.hmap(a, bt, xs) == RP.hmap(a2, bt, xs2) : Q.Als()}},
                    Q.cuts(a, r, a2, r2, e1))
            case +c <> +ct:
              match pr:
                case (+ep, +ec):
                  Empty.absurd({B.Var{pos, r, xs} == B.Var{pos2, r2, xs2} : B.Var},
                    u1(seq, pos2, r2, xs2, pos, r, xs, hw, hv, hnv, a2, b2, a, bt, el,
                      Equal.sym(Q.Als(), RP.hmap(a, bt, xs), RP.hmap(a2, b2, xs2), hh), c, ct, ep, ec))

# Two valid normalized variants making the same change are equal.
def uniq(+seq: Q.Bs(), +v: B.Var, +w: B.Var, +hv: {L.valid(seq, v) == True{} : Bool}, +hw: {L.valid(seq, w) == True{} : Bool},
  +hnv: {L.normalized(seq, v) == True{} : Bool}, +hnw: {L.normalized(seq, w) == True{} : Bool},
  +hs: {L.haps(seq, v) == L.haps(seq, w) : Q.Als()}) -> {v == w : B.Var}:
  match v w:
    case B.Var{+pos, +r, +xs} B.Var{+pos2, +r2, +xs2}:
      +a = RP.vA(seq, pos)
      +bt = RP.vB(seq, pos, r)
      +a2 = RP.vA(seq, pos2)
      +b2 = RP.vB(seq, pos2, r2)
      +es = RP.valid_es(seq, pos, r, xs, hv)
      +es2 = RP.valid_es(seq, pos2, r2, xs2, hw)
      +hh = SP.trans3(RP.hmap(a, bt, xs), L.haps(seq, B.Var{pos, r, xs}), L.haps(seq, B.Var{pos2, r2, xs2}), RP.hmap(a2, b2, xs2),
        Equal.sym(Q.Als(), L.haps(seq, B.Var{pos, r, xs}), RP.hmap(a, bt, xs), RP.valid_haps(seq, pos, r, xs, hv)), hs,
        Equal.sym(Q.Als(), L.haps(seq, B.Var{pos2, r2, xs2}), RP.hmap(a2, b2, xs2), RP.valid_haps(seq, pos2, r2, xs2, hw)))
      +ec = Equal.trans(Q.Bs(), Q.app(Q.app(a, r), bt), Q.app(a, Q.app(r, bt)), Q.app(Q.app(a2, r2), b2), Q.app_assoc(a, r, bt),
        Equal.trans(Q.Bs(), Q.app(a, Q.app(r, bt)), seq, Q.app(Q.app(a2, r2), b2), es,
          Equal.trans(Q.Bs(), seq, Q.app(a2, Q.app(r2, b2)), Q.app(Q.app(a2, r2), b2), Equal.sym(Q.Bs(), Q.app(a2, Q.app(r2, b2)), seq, es2),
            Q.app_assoc_r(a2, r2, b2))))
      u_top(seq, pos, r, xs, pos2, r2, xs2, hv, hw, hnv, hnw, a, bt, a2, b2,
        RP.valid_el(seq, pos, r, xs, hv), RP.valid_el(seq, pos2, r2, xs2, hw), hh, Q.cuts(Q.app(a, r), bt, Q.app(a2, r2), b2, ec))
