import Base
import ./proof_base.bend as P

# General lemmas for the run proofs (proof_run.bend): Nat order, String
# append, String.eq.

# Nat order
# =========

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      P.le_zero_l(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, P.false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

# Not a <= b gives b <= a.
law le_flip:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == False{} : Bool}
  {Nat.is_le(b, a) == True{} : Bool}

def le_flip(a, b, e):
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_le(b, 0n) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, P.le_zero_l(b)), e)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_flip(p, q, e)

# Not a <= b gives b + 1 <= a.
law le_flip_s:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == False{} : Bool}
  {Nat.is_le(1n+b, a) == True{} : Bool}

def le_flip_s(a, b, e):
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_le(1n+b, 0n) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, P.le_zero_l(b)), e)))
    case 1n+p 0n:
      P.le_zero_l(p)
    case 1n+p 1n+q:
      le_flip_s(p, q, e)

# a + 1 <= b gives a <= b.
law le_of_s:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(1n+a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_s(a, b, e):
  match a b:
    case 0n _:
      P.le_zero_l(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p 1n+q:
      le_of_s(p, q, e)

# a + 1 <= b and b <= a cannot both hold.
law le_s_not:
  for +a: Nat
  for +b: Nat
  for e1: {Nat.is_le(1n+a, b) == True{} : Bool}
  for e2: {Nat.is_le(b, a) == True{} : Bool}
  Empty

def le_s_not(a, b, e1, e2):
  match a b:
    case 0n 0n:
      P.false_ne_true(e1)
    case 0n 1n+q:
      P.false_ne_true(e2)
    case 1n+p 0n:
      P.false_ne_true(e1)
    case 1n+p 1n+q:
      le_s_not(p, q, e1, e2)

# String append
# =============

law s_append_nil:
  for +s: String
  {s ++ "" == s : String}

def s_append_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %s_append_nil(t) : {SCon{h, t ++ ""} == SCon{h, _} : String}
      {==}

law s_append_assoc:
  for +a: String
  for +b: String
  for +c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}

def s_append_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %s_append_assoc(t, b, c) : {SCon{h, (t ++ b) ++ c} == SCon{h, _} : String}
      {==}

# String.eq
# =========

def Cmp.disc_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case o:
      Empty

law lt_ne_eq:
  for e: {LT{} == EQ{} : Cmp}
  Empty

def lt_ne_eq(e):
  %Equal.sym(Cmp, LT{}, EQ{}, e) : Cmp.disc_eq(_)
  Unit{}

law gt_ne_eq:
  for e: {GT{} == EQ{} : Cmp}
  Empty

def gt_ne_eq(e):
  %Equal.sym(Cmp, GT{}, EQ{}, e) : Cmp.disc_eq(_)
  Unit{}

law bool_cmp_eq:
  for +a: Bool
  for +b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

def bool_cmp_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_ne_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_ne_eq(e))
    case True{} True{}:
      {==}

law cmp_fin_eq:
  for +ab: Bool
  for +bb: Bool
  for +t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp} & {ab == bb : Bool}

def cmp_fin_eq(ab, bb, t, e):
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {ab == bb : Bool}, lt_ne_eq(e))
    case EQ{}:
      ({==}, bool_cmp_eq(ab, bb, e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {ab == bb : Bool}, gt_ne_eq(e))

def word_eq.go(+p: Nat, +ab: Bool, +at: Word(p), +bb: Bool, +bt: Word(p),
  ih: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  r: {Word.cmp(p, at, bt) == EQ{} : Cmp} & {ab == bb : Bool}) -> {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  match r:
    case (te, he):
      %he : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
      %ih(te) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
      {==}

law word_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word_eq.go(p, ab, at, bb, bt, te => word_eq(p, at, bt, te), cmp_fin_eq(ab, bb, Word.cmp(p, at, bt), e))

law word_refl:
  for +n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def word_refl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

def order_go_eq.go(+x: Word(32n), +t1: String, +y: Word(32n), +t2: String,
  r: {Word.cmp(32n, x, y) == EQ{} : Cmp} & {t1 == t2 : String}) ->
  {EQ{} == EQ{} : Cmp} & {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String}:
  match r:
    case (ce, te):
      %te : {EQ{} == EQ{} : Cmp} & {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, _} : String}
      %word_eq(32n, x, y, ce) : {EQ{} == EQ{} : Cmp} & {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{_}}, t1} : String}
      ({==}, {==})

law order_go_eq:
  for +a: String
  for +b: String
  for +c: Cmp
  for e: {String.order.go(a, b, c) == EQ{} : Cmp}
  {c == EQ{} : Cmp} & {a == b : String}

def order_go_eq(a, b, c, e):
  match a b c:
    case SNil{} SNil{} _:
      (e, {==})
    case SNil{} SCon{h, t} LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {SNil{} == SCon{h, t} : String}, lt_ne_eq(e))
    case SNil{} SCon{h, t} EQ{}:
      Empty.absurd({EQ{} == EQ{} : Cmp} & {SNil{} == SCon{h, t} : String}, lt_ne_eq(e))
    case SNil{} SCon{h, t} GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {SNil{} == SCon{h, t} : String}, gt_ne_eq(e))
    case SCon{h, t} SNil{} LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {SCon{h, t} == SNil{} : String}, lt_ne_eq(e))
    case SCon{h, t} SNil{} EQ{}:
      Empty.absurd({EQ{} == EQ{} : Cmp} & {SCon{h, t} == SNil{} : String}, gt_ne_eq(e))
    case SCon{h, t} SNil{} GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {SCon{h, t} == SNil{} : String}, gt_ne_eq(e))
    case SCon{h1, t1} SCon{h2, t2} LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {SCon{h1, t1} == SCon{h2, t2} : String}, lt_ne_eq(e))
    case SCon{h1, t1} SCon{h2, t2} GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {SCon{h1, t1} == SCon{h2, t2} : String}, gt_ne_eq(e))
    case SCon{Chr{U32{+x}}, +t1} SCon{Chr{U32{+y}}, +t2} EQ{}:
      order_go_eq.go(x, t1, y, t2, order_go_eq(t1, t2, Word.cmp(32n, x, y), e))

law is_eq_true:
  for +c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def is_eq_true(c, e):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, P.false_ne_true(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, P.false_ne_true(e))

def str_eq.go(+a: String, +b: String, r: {EQ{} == EQ{} : Cmp} & {a == b : String}) -> {a == b : String}:
  match r:
    case (ce, ab):
      ab

# String.eq is equality.
law str_eq_sound:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def str_eq_sound(a, b, e):
  str_eq.go(a, b, order_go_eq(a, b, EQ{}, is_eq_true(String.order(a, b), e)))

law order_go_refl:
  for +a: String
  {String.order.go(a, a, EQ{}) == EQ{} : Cmp}

def order_go_refl(a):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+x}}, +t}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word_refl(32n, x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      order_go_refl(t)

law str_eq_refl:
  for +a: String
  {String.eq(a, a) == True{} : Bool}

def str_eq_refl(a):
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, order_go_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# String.eq(a, b) is False when a and b differ.
law str_eq_false:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  for ab: {a == b : String}
  Empty

def str_eq_false(a, b, e, ab):
  P.true_ne_false(Equal.trans(Bool, True{}, String.eq(a, b), False{},
    %ab : {True{} == String.eq(a, _) : Bool}; Equal.sym(Bool, String.eq(a, a), True{}, str_eq_refl(a)), e))

def str_eq_sym.go2(+a: String, +b: String, +y: Bool, ey: {String.eq(b, a) == y : Bool}, e: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  match y:
    case False{}:
      ey
    case True{}:
      Empty.absurd({String.eq(b, a) == False{} : Bool}, str_eq_false(a, b, e, Equal.sym(String, b, a, str_eq_sound(b, a, ey))))

law str_eq_sym:
  for +a: String
  for +b: String
  {String.eq(b, a) == String.eq(a, b) : Bool}

def str_eq_sym.go(+a: String, +b: String, +x: Bool, e: {String.eq(a, b) == x : Bool}) -> {String.eq(b, a) == x : Bool}:
  match x:
    case True{}:
      +ab = str_eq_sound(a, b, e)
      %Equal.sym(String, a, b, ab) : {String.eq(b, _) == True{} : Bool}
      str_eq_refl(b)
    case False{}:
      str_eq_sym.go2(a, b, String.eq(b, a), {==}, e)

def str_eq_sym(a, b):
  str_eq_sym.go(a, b, String.eq(a, b), {==})
