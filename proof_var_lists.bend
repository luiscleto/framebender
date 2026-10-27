import Base
import ./types.bend as B
import ./proof_base.bend as P

# Lemmas about lists of bases, used by proof_var.bend.
# Rewrites: `%e : G` with e : {new == old}; G is the goal with `_` where old
# is; what follows proves G with new there.

def Bs() -> Data:
  List<&2, B.Base>

def Als() -> Data:
  List<&2, List<&2, B.Base>>

def app(xs: Bs(), ys: Bs()) -> Bs():
  List.append(&2, B.Base, xs, ys)

def len(xs: Bs()) -> Nat:
  List.length(&2, B.Base, xs)

def take(xs: Bs(), n: Nat) -> Bs():
  List.take(&2, B.Base, xs, n)

def drop(xs: Bs(), n: Nat) -> Bs():
  List.drop(&2, B.Base, xs, n)

# Nat
# ===

def n_ne_succ_add(+n: Nat, +k: Nat, e: {n == 1n+Nat.add(k, n) : Nat}) -> Empty:
  match n:
    case 0n:
      P.succ_ne_zero(Nat.add(k, 0n), Equal.sym(Nat, 0n, 1n+Nat.add(k, 0n), e))
    case 1n+m:
      +e2 = {%P.add_succ(k, m) : {1n+m == 1n+_ : Nat}; e : {1n+m == 2n+Nat.add(k, m) : Nat}}
      +e3 = P.succ_inj(m, 1n+Nat.add(k, m), e2)
      n_ne_succ_add(m, k, e3)

# Cons
# ====

def hd(+d: B.Base, xs: Bs()) -> B.Base:
  match xs:
    case Nil{}:
      d
    case h <> t:
      h

def cons_tl(+h: B.Base, +t: Bs(), +g: B.Base, +u: Bs(), e: {h <> t == g <> u : Bs()}) -> {t == u : Bs()}:
  Equal.cong(Bs(), Bs(), l => List.tail(&2, B.Base, l), h <> t, g <> u, e)

def cons_hd(+h: B.Base, +t: Bs(), +g: B.Base, +u: Bs(), e: {h <> t == g <> u : Bs()}) -> {h == g : B.Base}:
  Equal.cong(Bs(), B.Base, l => hd(h, l), h <> t, g <> u, e)

def cons_eq(+h: B.Base, +t: Bs(), +g: B.Base, +u: Bs(), eh: {h == g : B.Base}, et: {t == u : Bs()}) -> {h <> t == g <> u : Bs()}:
  %eh : {h <> t == _ <> u : Bs()}
  %et : {h <> t == h <> _ : Bs()}
  {==}

def disc_nil(xs: Bs()) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      Empty

def nil_ne_cons(-g: B.Base, -u: Bs(), e: {Nil{} == g <> u : Bs()}) -> Empty:
  %e : disc_nil(_)
  Unit{}

# Append
# ======

def app_nil(+xs: Bs()) -> {app(xs, Nil{}) == xs : Bs()}:
  P.append_nil(B.Base, xs)

def app_assoc(+xs: Bs(), +ys: Bs(), +zs: Bs()) -> {app(app(xs, ys), zs) == app(xs, app(ys, zs)) : Bs()}:
  P.append_assoc(B.Base, xs, ys, zs)

def len_app(+xs: Bs(), +ys: Bs()) -> {len(app(xs, ys)) == Nat.add(len(xs), len(ys)) : Nat}:
  P.length_append(B.Base, xs, ys)

def cancel_l(+xs: Bs(), +ys: Bs(), +zs: Bs(), e: {app(xs, ys) == app(xs, zs) : Bs()}) -> {ys == zs : Bs()}:
  match xs:
    case Nil{}:
      e
    case +h <> +t:
      cancel_l(t, ys, zs, cons_tl(h, app(t, ys), h, app(t, zs), e))

def no_self_suffix(+zs: Bs(), +h: B.Base, +t: Bs(), e: {zs == h <> app(t, zs) : Bs()}) -> Empty:
  +el = Equal.cong(Bs(), Nat, l => len(l), zs, h <> app(t, zs), e)
  n_ne_succ_add(len(zs), len(t), %len_app(t, zs) : {len(zs) == 1n+_ : Nat}; el)

def cancel_r(+xs: Bs(), +ys: Bs(), +zs: Bs(), +e: {app(xs, zs) == app(ys, zs) : Bs()}) -> {xs == ys : Bs()}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +g <> +u:
      Empty.absurd({Nil{} == g <> u : Bs()}, no_self_suffix(zs, g, u, e))
    case +h <> +t Nil{}:
      Empty.absurd({h <> t == Nil{} : Bs()}, no_self_suffix(zs, h, t, Equal.sym(Bs(), h <> app(t, zs), zs, e)))
    case +h <> +t +g <> +u:
      cons_eq(h, t, g, u, cons_hd(h, app(t, zs), g, app(u, zs), e),
        cancel_r(t, u, zs, cons_tl(h, app(t, zs), g, app(u, zs), e)))

# Take and drop
# =============

def take_zero(+ys: Bs()) -> {take(ys, 0n) == Nil{} : Bs()}:
  match ys:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def drop_zero(+ys: Bs()) -> {drop(ys, 0n) == ys : Bs()}:
  match ys:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def take_drop(+xs: Bs(), +n: Nat) -> {app(take(xs, n), drop(xs, n)) == xs : Bs()}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case +h <> +t 1n+k:
      %take_drop(t, k) : {h <> app(take(t, k), drop(t, k)) == h <> _ : Bs()}
      {==}

def drop_drop(+xs: Bs(), +a: Nat, +b: Nat) -> {drop(drop(xs, a), b) == drop(xs, Nat.add(a, b)) : Bs()}:
  match xs a:
    case Nil{} _:
      match b:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      drop_drop(t, k, b)

def take_app(+xs: Bs(), +ys: Bs(), +n: Nat) -> {take(app(xs, ys), Nat.add(len(xs), n)) == app(xs, take(ys, n)) : Bs()}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %take_app(t, ys, n) : {h <> take(app(t, ys), Nat.add(len(t), n)) == h <> _ : Bs()}
      {==}

def drop_app(+xs: Bs(), +ys: Bs(), +n: Nat) -> {drop(app(xs, ys), Nat.add(len(xs), n)) == drop(ys, n) : Bs()}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      drop_app(t, ys, n)

def take_app0(+xs: Bs(), +ys: Bs()) -> {take(app(xs, ys), len(xs)) == xs : Bs()}:
  match xs:
    case Nil{}:
      take_zero(ys)
    case +h <> +t:
      %take_app0(t, ys) : {h <> take(app(t, ys), len(t)) == h <> _ : Bs()}
      {==}

def drop_app0(+xs: Bs(), +ys: Bs()) -> {drop(app(xs, ys), len(xs)) == ys : Bs()}:
  match xs:
    case Nil{}:
      drop_zero(ys)
    case h <> t:
      drop_app0(t, ys)

# take(xs, n) has n bases when xs goes past n.
def len_take_of(+xs: Bs(), +n: Nat, +g: B.Base, +u: Bs(), e: {drop(xs, n) == g <> u : Bs()}) -> {len(take(xs, n)) == n : Nat}:
  match xs n:
    case Nil{} _:
      Empty.absurd({len(take(Nil{}, n)) == n : Nat}, nil_ne_cons(g, u, e))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      %len_take_of(t, k, g, u, e) : {1n+len(take(t, k)) == 1n+_ : Nat}
      {==}

# Last
# ====

def last_go_app(+xs: Bs(), +h: B.Base, +t: Bs(), +d: B.Base) ->
  {List.last.go(&2, B.Base, app(xs, h <> t), d) == List.last.go(&2, B.Base, t, h) : B.Base}:
  match xs:
    case Nil{}:
      {==}
    case x <> xt:
      last_go_app(xt, h, t, x)

def last_app(+xs: Bs(), +h: B.Base, +t: Bs()) ->
  {List.last(&2, B.Base, app(xs, h <> t)) == List.last(&2, B.Base, h <> t) : Maybe<&2, B.Base>}:
  match xs:
    case Nil{}:
      {==}
    case x <> xt:
      %last_go_app(xt, h, t, x) : {Some{List.last.go(&2, B.Base, app(xt, h <> t), x)} == Some{_} : Maybe<&2, B.Base>}
      {==}

# X ++ C == Y ++ a with C and a non-empty: C and a end with the same base.
def last_eq(+xs: Bs(), +c: B.Base, +ct: Bs(), +ys: Bs(), +a: B.Base, +at: Bs(),
  e: {app(xs, c <> ct) == app(ys, a <> at) : Bs()}) ->
  {List.last(&2, B.Base, c <> ct) == List.last(&2, B.Base, a <> at) : Maybe<&2, B.Base>}:
  +el = Equal.cong(Bs(), Maybe<&2, B.Base>, l => List.last(&2, B.Base, l), app(xs, c <> ct), app(ys, a <> at), e)
  %last_app(xs, c, ct) : {_ == List.last(&2, B.Base, a <> at) : Maybe<&2, B.Base>}
  %last_app(ys, a, at) : {List.last(&2, B.Base, app(xs, c <> ct)) == _ : Maybe<&2, B.Base>}
  el

# Init
# ====

def init(+xs: Bs()) -> Bs():
  List.take(&2, B.Base, xs, Nat.sub(len(xs), 1n))

def init_cons(+h: B.Base, +t: Bs()) -> {init(h <> t) == take(h <> t, len(t)) : Bs()}:
  %Equal.sym(Nat, Nat.sub(len(t), 0n), len(t), P.sub_zero(len(t))) : {take(h <> t, _) == take(h <> t, len(t)) : Bs()}
  {==}

def snoc_go(+t: Bs(), +h: B.Base) -> {app(take(h <> t, len(t)), [List.last.go(&2, B.Base, t, h)]) == h <> t : Bs()}:
  match t:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      %snoc_go(t2, h2) : {h <> app(take(h2 <> t2, len(t2)), [List.last.go(&2, B.Base, t2, h2)]) == h <> _ : Bs()}
      {==}

# A non-empty list is its init followed by its last base.
def snoc(+h: B.Base, +t: Bs()) -> {app(init(h <> t), [List.last.go(&2, B.Base, t, h)]) == h <> t : Bs()}:
  %Equal.sym(Bs(), init(h <> t), take(h <> t, len(t)), init_cons(h, t)) : {app(_, [List.last.go(&2, B.Base, t, h)]) == h <> t : Bs()}
  snoc_go(t, h)

def len_take_go(+t: Bs(), +h: B.Base) -> {len(take(h <> t, len(t))) == len(t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      %len_take_go(t2, h2) : {1n+len(take(h2 <> t2, len(t2))) == 1n+_ : Nat}
      {==}

def len_init(+h: B.Base, +t: Bs()) -> {len(init(h <> t)) == len(t) : Nat}:
  %Equal.sym(Bs(), init(h <> t), take(h <> t, len(t)), init_cons(h, t)) : {len(_) == len(t) : Nat}
  len_take_go(t, h)

# Equality tests
# ==============

def base_refl(+b: B.Base) -> {B.Base.is_eq(b, b) == True{} : Bool}:
  match b:
    case B.A{}:
      {==}
    case B.C{}:
      {==}
    case B.G{}:
      {==}
    case B.T{}:
      {==}
    case B.N{}:
      {==}

def base_sound(+a: B.Base, +b: B.Base, e: {B.Base.is_eq(a, b) == True{} : Bool}) -> {a == b : B.Base}:
  match a b:
    case B.A{} B.A{}:
      {==}
    case B.A{} B.C{}:
      Empty.absurd({B.A{} == B.C{} : B.Base}, P.false_ne_true(e))
    case B.A{} B.G{}:
      Empty.absurd({B.A{} == B.G{} : B.Base}, P.false_ne_true(e))
    case B.A{} B.T{}:
      Empty.absurd({B.A{} == B.T{} : B.Base}, P.false_ne_true(e))
    case B.A{} B.N{}:
      Empty.absurd({B.A{} == B.N{} : B.Base}, P.false_ne_true(e))
    case B.C{} B.A{}:
      Empty.absurd({B.C{} == B.A{} : B.Base}, P.false_ne_true(e))
    case B.C{} B.C{}:
      {==}
    case B.C{} B.G{}:
      Empty.absurd({B.C{} == B.G{} : B.Base}, P.false_ne_true(e))
    case B.C{} B.T{}:
      Empty.absurd({B.C{} == B.T{} : B.Base}, P.false_ne_true(e))
    case B.C{} B.N{}:
      Empty.absurd({B.C{} == B.N{} : B.Base}, P.false_ne_true(e))
    case B.G{} B.A{}:
      Empty.absurd({B.G{} == B.A{} : B.Base}, P.false_ne_true(e))
    case B.G{} B.C{}:
      Empty.absurd({B.G{} == B.C{} : B.Base}, P.false_ne_true(e))
    case B.G{} B.G{}:
      {==}
    case B.G{} B.T{}:
      Empty.absurd({B.G{} == B.T{} : B.Base}, P.false_ne_true(e))
    case B.G{} B.N{}:
      Empty.absurd({B.G{} == B.N{} : B.Base}, P.false_ne_true(e))
    case B.T{} B.A{}:
      Empty.absurd({B.T{} == B.A{} : B.Base}, P.false_ne_true(e))
    case B.T{} B.C{}:
      Empty.absurd({B.T{} == B.C{} : B.Base}, P.false_ne_true(e))
    case B.T{} B.G{}:
      Empty.absurd({B.T{} == B.G{} : B.Base}, P.false_ne_true(e))
    case B.T{} B.T{}:
      {==}
    case B.T{} B.N{}:
      Empty.absurd({B.T{} == B.N{} : B.Base}, P.false_ne_true(e))
    case B.N{} B.A{}:
      Empty.absurd({B.N{} == B.A{} : B.Base}, P.false_ne_true(e))
    case B.N{} B.C{}:
      Empty.absurd({B.N{} == B.C{} : B.Base}, P.false_ne_true(e))
    case B.N{} B.G{}:
      Empty.absurd({B.N{} == B.G{} : B.Base}, P.false_ne_true(e))
    case B.N{} B.T{}:
      Empty.absurd({B.N{} == B.T{} : B.Base}, P.false_ne_true(e))
    case B.N{} B.N{}:
      {==}

def bases_refl(+xs: Bs()) -> {B.Bases.eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, B.Base.is_eq(h, h), True{}, base_refl(h)) : {Bool.and(_, B.Bases.eq(t, t)) == True{} : Bool}
      bases_refl(t)

def bases_sound(+xs: Bs(), +ys: Bs(), +e: {B.Bases.eq(xs, ys) == True{} : Bool}) -> {xs == ys : Bs()}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +g <> +u:
      Empty.absurd({Nil{} == g <> u : Bs()}, P.false_ne_true(e))
    case +h <> +t Nil{}:
      Empty.absurd({h <> t == Nil{} : Bs()}, P.false_ne_true(e))
    case +h <> +t +g <> +u:
      cons_eq(h, t, g, u,
        base_sound(h, g, P.and_true_l(B.Base.is_eq(h, g), B.Bases.eq(t, u), e)),
        bases_sound(t, u, P.and_true_r(B.Base.is_eq(h, g), B.Bases.eq(t, u), e)))

def acons_tl(+h: Bs(), +t: Als(), +g: Bs(), +u: Als(), e: {h <> t == g <> u : Als()}) -> {t == u : Als()}:
  Equal.cong(Als(), Als(), l => List.tail(&2, List<&2, B.Base>, l), h <> t, g <> u, e)

def ahd(+d: Bs(), xs: Als()) -> Bs():
  match xs:
    case Nil{}:
      d
    case h <> t:
      h

def acons_hd(+h: Bs(), +t: Als(), +g: Bs(), +u: Als(), e: {h <> t == g <> u : Als()}) -> {h == g : Bs()}:
  Equal.cong(Als(), Bs(), l => ahd(h, l), h <> t, g <> u, e)

def acons_eq(+h: Bs(), +t: Als(), +g: Bs(), +u: Als(), eh: {h == g : Bs()}, et: {t == u : Als()}) -> {h <> t == g <> u : Als()}:
  %eh : {h <> t == _ <> u : Als()}
  %et : {h <> t == h <> _ : Als()}
  {==}

def alleles_refl(+xs: Als()) -> {B.Alleles.eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, B.Bases.eq(h, h), True{}, bases_refl(h)) : {Bool.and(_, B.Alleles.eq(t, t)) == True{} : Bool}
      alleles_refl(t)

def alleles_sound(+xs: Als(), +ys: Als(), +e: {B.Alleles.eq(xs, ys) == True{} : Bool}) -> {xs == ys : Als()}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +g <> +u:
      Empty.absurd({Nil{} == g <> u : Als()}, P.false_ne_true(e))
    case +h <> +t Nil{}:
      Empty.absurd({h <> t == Nil{} : Als()}, P.false_ne_true(e))
    case +h <> +t +g <> +u:
      acons_eq(h, t, g, u,
        bases_sound(h, g, P.and_true_l(B.Bases.eq(h, g), B.Alleles.eq(t, u), e)),
        alleles_sound(t, u, P.and_true_r(B.Bases.eq(h, g), B.Alleles.eq(t, u), e)))

# Reversed forms, for rewriting the long side into the short one
# ==============================================================

def take_app0_r(+xs: Bs(), +ys: Bs()) -> {xs == take(app(xs, ys), len(xs)) : Bs()}:
  Equal.sym(Bs(), take(app(xs, ys), len(xs)), xs, take_app0(xs, ys))

def drop_app0_r(+xs: Bs(), +ys: Bs()) -> {ys == drop(app(xs, ys), len(xs)) : Bs()}:
  Equal.sym(Bs(), drop(app(xs, ys), len(xs)), ys, drop_app0(xs, ys))

def drop_app_r(+xs: Bs(), +ys: Bs(), +n: Nat) -> {drop(ys, n) == drop(app(xs, ys), Nat.add(len(xs), n)) : Bs()}:
  Equal.sym(Bs(), drop(app(xs, ys), Nat.add(len(xs), n)), drop(ys, n), drop_app(xs, ys, n))

def app_assoc_r(+xs: Bs(), +ys: Bs(), +zs: Bs()) -> {app(xs, app(ys, zs)) == app(app(xs, ys), zs) : Bs()}:
  Equal.sym(Bs(), app(app(xs, ys), zs), app(xs, app(ys, zs)), app_assoc(xs, ys, zs))

def take_drop_r(+xs: Bs(), +n: Nat) -> {xs == app(take(xs, n), drop(xs, n)) : Bs()}:
  Equal.sym(Bs(), app(take(xs, n), drop(xs, n)), xs, take_drop(xs, n))

def snoc_r(+h: B.Base, +t: Bs()) -> {h <> t == app(init(h <> t), [List.last.go(&2, B.Base, t, h)]) : Bs()}:
  Equal.sym(Bs(), app(init(h <> t), [List.last.go(&2, B.Base, t, h)]), h <> t, snoc(h, t))

# Booleans
# ========

def and_tt(+a: Bool, +b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def bool_ext(+a: Bool, +b: Bool, f: {a == True{} : Bool} -> {b == True{} : Bool}, g: {b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(f({==})))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(g({==})))

# Two ways of cutting one list: one cut is a prefix of the other
# ==============================================================

def Cut(+p: Bs(), +b: Bs(), +q: Bs(), +c: Bs()) -> Type:
  Exists(Bs(), m => {q == app(p, m) : Bs()} & {b == app(m, c) : Bs()})

def cuts.lift(+h: B.Base, +p: Bs(), +b: Bs(), +q: Bs(), +c: Bs(),
  r: Or(Cut(p, b, q, c), Cut(q, c, p, b))) -> Or(Cut(h <> p, b, h <> q, c), Cut(h <> q, c, h <> p, b)):
  match r:
    case Inl{w}:
      match w:
        case (+m, pr):
          match pr:
            case (eq, eb):
              Inl{(m, (%eq : {h <> q == h <> _ : Bs()}; {==}, eb))}
    case Inr{w}:
      match w:
        case (+m, pr):
          match pr:
            case (ep, ec):
              Inr{(m, (%ep : {h <> p == h <> _ : Bs()}; {==}, ec))}

# p ++ b == q ++ c: q = p ++ m and b = m ++ c, or the other way round.
def cuts(+p: Bs(), +b: Bs(), +q: Bs(), +c: Bs(), +e: {app(p, b) == app(q, c) : Bs()}) -> Or(Cut(p, b, q, c), Cut(q, c, p, b)):
  match p q:
    case Nil{} _:
      Inl{(q, ({==}, e))}
    case +h <> +t Nil{}:
      Inr{(h <> t, ({==}, Equal.sym(Bs(), h <> app(t, b), c, e)))}
    case +h <> +t +g <> +u:
      +eh = cons_hd(h, app(t, b), g, app(u, c), e)
      +et = cons_tl(h, app(t, b), g, app(u, c), e)
      %eh : Or(Cut(h <> t, b, _ <> u, c), Cut(_ <> u, c, h <> t, b))
      cuts.lift(h, t, b, u, c, cuts(t, b, u, c, et))

# More about init
# ===============

# xs ++ b, with xs split before its last base.
def snoc_app(+g: B.Base, +u: Bs(), +b: Bs()) ->
  {app(g <> u, b) == app(init(g <> u), List.last.go(&2, B.Base, u, g) <> b) : Bs()}:
  %snoc(g, u) : {app(_, b) == app(init(g <> u), List.last.go(&2, B.Base, u, g) <> b) : Bs()}
  app_assoc(init(g <> u), [List.last.go(&2, B.Base, u, g)], b)

def snoc_app_r(+g: B.Base, +u: Bs(), +b: Bs()) ->
  {app(init(g <> u), List.last.go(&2, B.Base, u, g) <> b) == app(g <> u, b) : Bs()}:
  Equal.sym(Bs(), app(g <> u, b), app(init(g <> u), List.last.go(&2, B.Base, u, g) <> b), snoc_app(g, u, b))

def len_init_r(+h: B.Base, +t: Bs()) -> {len(t) == len(init(h <> t)) : Nat}:
  Equal.sym(Nat, len(init(h <> t)), len(t), len_init(h, t))

def succ_sub_one(+n: Nat, e: {Nat.is_le(1n, n) == True{} : Bool}) -> {1n+Nat.sub(n, 1n) == n : Nat}:
  match n:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, P.false_ne_true(e))
    case 1n+p:
      %P.sub_zero(p) : {1n+Nat.sub(p, 0n) == 1n+_ : Nat}
      {==}

def sub_sub_one(+n: Nat) -> {Nat.sub(Nat.sub(n, 1n), 1n) == Nat.sub(n, 2n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %P.sub_zero(p) : {Nat.sub(Nat.sub(p, 0n), 1n) == Nat.sub(_, 1n) : Nat}
      {==}

def sub_one_succ(+n: Nat) -> {Nat.sub(1n+n, 1n) == n : Nat}:
  P.sub_zero(n)

# Order
# =====

def le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

def le_trans(+a: Nat, +b: Nat, +c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      P.le_zero_l(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, P.false_ne_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.false_ne_true(e2))
    case 1n+p 1n+q 1n+k:
      le_trans(p, q, k, e1, e2)

def or_tt_r(+a: Bool, +b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def le_of_eq(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_le(a, b) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  P.le_refl(a)

def some_inj(+a: B.Base, +b: B.Base, e: {Some{a} == Some{b} : Maybe<&2, B.Base>}) -> {a == b : B.Base}:
  Equal.cong(Maybe<&2, B.Base>, B.Base, m => Maybe.default(&2, B.Base, m, a), Some{a}, Some{b}, e)

def le2_sub1(+n: Nat, e: {Nat.is_le(2n, n) == True{} : Bool}) -> {Nat.is_le(1n, Nat.sub(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, P.sub_zero(p)) : {Nat.is_le(1n, _) == True{} : Bool}
      e

def false_of(+b: Bool, f: {b == True{} : Bool} -> Empty) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}))

def fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (x, y):
      x

def snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (x, y):
      y

# Lengths, drop and last
# ======================

def le_len_app_l(+xs: Bs(), +ys: Bs()) -> {Nat.is_le(len(xs), len(app(xs, ys))) == True{} : Bool}:
  match xs:
    case Nil{}:
      P.le_zero_l(len(ys))
    case h <> t:
      le_len_app_l(t, ys)

def le_len_app_r(+xs: Bs(), +ys: Bs()) -> {Nat.is_le(len(ys), len(app(xs, ys))) == True{} : Bool}:
  match xs:
    case Nil{}:
      P.le_refl(len(ys))
    case h <> t:
      le_trans(len(ys), len(app(t, ys)), 1n+len(app(t, ys)), le_len_app_r(t, ys), le_succ(len(app(t, ys))))

def drop_app_le(+xs: Bs(), +ys: Bs(), +n: Nat, e: {Nat.is_le(n, len(xs)) == True{} : Bool}) ->
  {drop(app(xs, ys), n) == app(drop(xs, n), ys) : Bs()}:
  match xs n:
    case Nil{} 0n:
      drop_zero(ys)
    case Nil{} 1n+m:
      Empty.absurd({drop(ys, 1n+m) == app(drop(Nil{}, 1n+m), ys) : Bs()}, P.false_ne_true(e))
    case h <> t 0n:
      {==}
    case h <> t 1n+m:
      drop_app_le(t, ys, m, e)

def len_take_le(+xs: Bs(), +n: Nat, e: {Nat.is_le(n, len(xs)) == True{} : Bool}) -> {len(take(xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({len(take(Nil{}, 1n+m)) == 1n+m : Nat}, P.false_ne_true(e))
    case h <> t 0n:
      {==}
    case h <> t 1n+m:
      %len_take_le(t, m, e) : {1n+len(take(t, m)) == 1n+_ : Nat}
      {==}

def drop_len1(+xs: Bs(), +n: Nat, e: {Nat.is_le(1n+n, len(xs)) == True{} : Bool}) -> {Nat.is_le(1n, len(drop(xs, n))) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Nat.is_le(1n, len(drop(Nil{}, n))) == True{} : Bool}, P.false_ne_true(e))
    case h <> t 0n:
      P.le_zero_l(len(t))
    case h <> t 1n+m:
      drop_len1(t, m, e)

def last_app_len(+xs: Bs(), +c: Bs(), e: {Nat.is_le(1n, len(c)) == True{} : Bool}) ->
  {List.last(&2, B.Base, app(xs, c)) == List.last(&2, B.Base, c) : Maybe<&2, B.Base>}:
  match c:
    case Nil{}:
      Empty.absurd({List.last(&2, B.Base, app(xs, Nil{})) == List.last(&2, B.Base, Nil{}) : Maybe<&2, B.Base>}, P.false_ne_true(e))
    case +g <> +u:
      last_app(xs, g, u)

def mdisc(m: Maybe<&2, B.Base>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_ne_some2(-x: B.Base, e: {None{} == Some{x} : Maybe<&2, B.Base>}) -> Empty:
  %e : mdisc(_)
  Unit{}

# X ++ C == Y ++ a with C ending in l and a non-empty: a ends in l.
def last_eq_gen(+xs: Bs(), +c: Bs(), +ys: Bs(), +a: B.Base, +at: Bs(), +l: B.Base,
  +hl: {List.last(&2, B.Base, c) == Some{l} : Maybe<&2, B.Base>}, +e: {app(xs, c) == app(ys, a <> at) : Bs()}) ->
  {Some{l} == List.last(&2, B.Base, a <> at) : Maybe<&2, B.Base>}:
  match c:
    case Nil{}:
      Empty.absurd({Some{l} == List.last(&2, B.Base, a <> at) : Maybe<&2, B.Base>}, none_ne_some2(l, hl))
    case +g <> +u:
      Equal.trans(Maybe<&2, B.Base>, Some{l}, List.last(&2, B.Base, g <> u), List.last(&2, B.Base, a <> at),
        Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, g <> u), Some{l}, hl), last_eq(xs, g, u, ys, a, at, e))

def adisc(xs: Als()) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      Empty

def anil_ne_cons(-g: Bs(), -u: Als(), e: {Nil{} == g <> u : Als()}) -> Empty:
  %e : adisc(_)
  Unit{}

# i = pos - k - 1 is below pos - 1 when 1 <= k <= pos - 1.
def lt_sub_go(+x: Nat, +j: Nat, e: {Nat.is_le(1n+j, x) == True{} : Bool}) ->
  {Nat.is_le(1n+Nat.sub(Nat.sub(x, j), 1n), x) == True{} : Bool}:
  match x j:
    case 0n _:
      Empty.absurd({Nat.is_le(1n+Nat.sub(Nat.sub(0n, j), 1n), 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+y 0n:
      %Equal.sym(Nat, Nat.sub(y, 0n), y, P.sub_zero(y)) : {Nat.is_le(_, y) == True{} : Bool}
      P.le_refl(y)
    case 1n+y 1n+m:
      le_trans(Nat.sub(Nat.sub(y, m), 1n), 1n+Nat.sub(Nat.sub(y, m), 1n), y, le_succ(Nat.sub(Nat.sub(y, m), 1n)), lt_sub_go(y, m, e))

def lt_sub(+pos: Nat, +k: Nat, e1: {Nat.is_le(1n, k) == True{} : Bool}, e2: {Nat.is_le(k, Nat.sub(pos, 1n)) == True{} : Bool}) ->
  {Nat.is_le(1n+Nat.sub(Nat.sub(pos, k), 1n), Nat.sub(pos, 1n)) == True{} : Bool}:
  match pos k:
    case 0n _:
      Empty.absurd({Nat.is_le(1n+Nat.sub(Nat.sub(0n, k), 1n), 0n) == True{} : Bool}, P.false_ne_true(le_trans(1n, k, 0n, e1, e2)))
    case 1n+x 0n:
      Empty.absurd({Nat.is_le(1n+Nat.sub(Nat.sub(1n+x, 0n), 1n), Nat.sub(1n+x, 1n)) == True{} : Bool}, P.false_ne_true(e1))
    case 1n+x 1n+j:
      %Equal.sym(Nat, Nat.sub(x, 0n), x, P.sub_zero(x)) : {Nat.is_le(1n+Nat.sub(Nat.sub(x, j), 1n), _) == True{} : Bool}
      lt_sub_go(x, j, %P.sub_zero(x) : {Nat.is_le(1n+j, _) == True{} : Bool}; e2)

def and_l_false(+a: Bool, +b: Bool, e: {Bool.and(a, b) == False{} : Bool}, eb: {b == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, eb), e)))

def not_tt(+b: Bool, e1: {Bool.not(b) == True{} : Bool}, e2: {b == True{} : Bool}) -> Empty:
  P.false_ne_true(%e2 : {Bool.not(_) == True{} : Bool}; e1)

def or_tt_l(+a: Bool, +b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def one_le_sub(+n: Nat, e: {Nat.is_le(1n, Nat.sub(n, 1n)) == True{} : Bool}) -> {Nat.is_le(2n, n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(2n, 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p:
      %P.sub_zero(p) : {Nat.is_le(1n, _) == True{} : Bool}
      e

# x ++ (a ++ c) has at least two bases when a and c are non-empty.
def len2(+x: Bs(), +a0: B.Base, +at: Bs(), +c: Bs(), e: {Nat.is_le(1n, len(c)) == True{} : Bool}) ->
  {Nat.is_le(2n, len(app(x, app(a0 <> at, c)))) == True{} : Bool}:
  le_trans(2n, len(a0 <> app(at, c)), len(app(x, a0 <> app(at, c))),
    le_trans(1n, len(c), len(app(at, c)), e, le_len_app_r(at, c)),
    le_len_app_r(x, a0 <> app(at, c)))
