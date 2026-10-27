import Base
import ./types.bend as B
import ./proof_base.bend as P
import ./LAWS.bend as L

# Generic lemmas for proof_window.bend: equality of strings, slices of lists,
# reading FASTA letters as bases, small Nat facts.

# Maybe
# =====

def some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, x), Some{x}, Some{y}, e)

def none_ne_some(-A: Data, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %e : P.Bool.disc_ft(Maybe.is_some(&2, A, _))
  Unit{}

# Bool
# ====

def not_false_inv(+b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, P.true_ne_false(e))

def or_false_r(+a: Bool, +b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.true_ne_false(e))

# Strings: String.eq is equality
# ==============================

def Cmp.disc_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case o:
      Unit

def lt_ne_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.disc_eq(_)
  Unit{}

def gt_ne_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : Cmp.disc_eq(_)
  Unit{}

def bool_cmp_eq(+a: Bool, +b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_ne_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_ne_eq(e))
    case True{} True{}:
      {==}

def word_fin_t(+ab: Bool, +bb: Bool, +t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_ne_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_ne_eq(e))

def word_fin_b(+ab: Bool, +bb: Bool, +t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {Bool.cmp(ab, bb) == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, lt_ne_eq(e))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, gt_ne_eq(e))

def word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n), +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %bool_cmp_eq(ab, bb, word_fin_b(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %word_cmp_eq(p, at, bt, word_fin_t(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

def u32_cmp_eq(+a: U32, +b: U32, e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %word_cmp_eq(32n, x, y, e) : {U32{x} == U32{_} : U32}
      {==}

def order_lt(+a: String, +b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def order_gt(+a: String, +b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

# Once the comparison is not EQ, it stays so.
def order_c(+a: String, +b: String, +c: Cmp, e: {String.order.go(a, b, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_ne_eq(Equal.trans(Cmp, LT{}, String.order.go(a, b, LT{}), EQ{}, Equal.sym(Cmp, String.order.go(a, b, LT{}), LT{}, order_lt(a, b)), e)))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_ne_eq(Equal.trans(Cmp, GT{}, String.order.go(a, b, GT{}), EQ{}, Equal.sym(Cmp, String.order.go(a, b, GT{}), GT{}, order_gt(a, b)), e)))

def order_go_eq(+a: String, +b: String, +e: {String.order.go(a, b, EQ{}) == EQ{} : Cmp}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, lt_ne_eq(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, gt_ne_eq(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      +hc = order_c(t1, t2, U32.cmp(x, y), e)
      +e2 = Equal.trans(Cmp, String.order.go(t1, t2, EQ{}), String.order.go(t1, t2, U32.cmp(x, y)), EQ{},
        Equal.cong(Cmp, Cmp, c => String.order.go(t1, t2, c), EQ{}, U32.cmp(x, y), Equal.sym(Cmp, U32.cmp(x, y), EQ{}, hc)), e)
      %u32_cmp_eq(x, y, hc) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %order_go_eq(t1, t2, e2) : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

def cmp_is_eq(+c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, P.false_ne_true(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, P.false_ne_true(e))

def string_eq_sound(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  order_go_eq(a, b, cmp_is_eq(String.order.go(a, b, EQ{}), e))

# Reading FASTA letters commutes with length, take and drop
# =========================================================

def of_fasta_len(+s: String) -> {List.length(&2, B.Base, B.Bases.of_fasta(s)) == String.length(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %of_fasta_len(t) : {1n+List.length(&2, B.Base, B.Bases.of_fasta(t)) == 1n+_ : Nat}
      {==}

def of_fasta_take(+s: String, +n: Nat) -> {B.Bases.of_fasta(String.take(s, n)) == List.take(&2, B.Base, B.Bases.of_fasta(s), n) : List<&2, B.Base>}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      %of_fasta_take(t, p) : {B.Base.of_fasta(h) <> B.Bases.of_fasta(String.take(t, p)) == B.Base.of_fasta(h) <> _ : List<&2, B.Base>}
      {==}

def of_fasta_drop(+s: String, +n: Nat) -> {B.Bases.of_fasta(String.drop(s, n)) == List.drop(&2, B.Base, B.Bases.of_fasta(s), n) : List<&2, B.Base>}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      of_fasta_drop(t, p)

# Slices of lists
# ===============

def take_take(+xs: List<&2, B.Base>, +m: Nat, +n: Nat, e: {Nat.is_le(n, m) == True{} : Bool}) ->
  {List.take(&2, B.Base, List.take(&2, B.Base, xs, m), n) == List.take(&2, B.Base, xs, n) : List<&2, B.Base>}:
  match xs m n:
    case Nil{} _ _:
      {==}
    case x <> t 0n 0n:
      {==}
    case x <> t 0n 1n+q:
      Empty.absurd({Nil{} == x <> List.take(&2, B.Base, t, q) : List<&2, B.Base>}, P.false_ne_true(e))
    case x <> t 1n+k 0n:
      {==}
    case +x <> +t 1n+k 1n+q:
      %take_take(t, k, q, e) : {x <> List.take(&2, B.Base, List.take(&2, B.Base, t, k), q) == x <> _ : List<&2, B.Base>}
      {==}

# Taking n after skipping s inside the first L bases reads the list itself
# when s + n <= L.
def slice_take(+xs: List<&2, B.Base>, +l: Nat, +s: Nat, +n: Nat, e: {Nat.is_le(Nat.add(s, n), l) == True{} : Bool}) ->
  {List.take(&2, B.Base, List.drop(&2, B.Base, List.take(&2, B.Base, xs, l), s), n)
    == List.take(&2, B.Base, List.drop(&2, B.Base, xs, s), n) : List<&2, B.Base>}:
  match xs l s n:
    case Nil{} _ _ _:
      {==}
    case x <> t 0n 0n 0n:
      {==}
    case x <> t 0n 0n 1n+q:
      Empty.absurd({Nil{} == x <> List.take(&2, B.Base, t, q) : List<&2, B.Base>}, P.false_ne_true(e))
    case x <> t 0n 1n+r _:
      Empty.absurd({List.take(&2, B.Base, Nil{}, n) == List.take(&2, B.Base, List.drop(&2, B.Base, t, r), n) : List<&2, B.Base>}, P.false_ne_true(e))
    case x <> t 1n+k 0n 0n:
      {==}
    case +x <> +t 1n+k 0n 1n+q:
      %take_take(t, k, q, e) : {x <> List.take(&2, B.Base, List.take(&2, B.Base, t, k), q) == x <> _ : List<&2, B.Base>}
      {==}
    case +x <> +t 1n+k 1n+r _:
      slice_take(t, k, r, n, e)

# A window of L bases from o, read from s - o, is the list read from s, when
# o <= s and s + n <= o + L.
def slice_win(+xs: List<&2, B.Base>, +o: Nat, +s: Nat, +l: Nat, +n: Nat,
  e1: {Nat.is_le(o, s) == True{} : Bool}, e2: {Nat.is_le(Nat.add(s, n), Nat.add(o, l)) == True{} : Bool}) ->
  {List.take(&2, B.Base, List.drop(&2, B.Base, List.take(&2, B.Base, List.drop(&2, B.Base, xs, o), l), Nat.sub(s, o)), n)
    == List.take(&2, B.Base, List.drop(&2, B.Base, xs, s), n) : List<&2, B.Base>}:
  match xs o s:
    case Nil{} _ _:
      {==}
    case +x <> +t 0n 0n:
      slice_take(x <> t, l, 0n, n, e2)
    case +x <> +t 0n 1n+r:
      slice_take(x <> t, l, 1n+r, n, e2)
    case x <> t 1n+k 0n:
      Empty.absurd({List.take(&2, B.Base, List.drop(&2, B.Base, List.take(&2, B.Base, List.drop(&2, B.Base, t, k), l), 0n), n)
        == List.take(&2, B.Base, x <> t, n) : List<&2, B.Base>}, P.false_ne_true(e1))
    case +x <> +t 1n+k 1n+r:
      slice_win(t, k, r, l, n, e1, e2)

# Lengths
# =======

def bases_eq_len(+xs: List<&2, B.Base>, +ys: List<&2, B.Base>, e: {B.Bases.eq(xs, ys) == True{} : Bool}) ->
  {List.length(&2, B.Base, xs) == List.length(&2, B.Base, ys) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      Empty.absurd({0n == 1n+List.length(&2, B.Base, yt) : Nat}, P.false_ne_true(e))
    case x <> xt Nil{}:
      Empty.absurd({1n+List.length(&2, B.Base, xt) == 0n : Nat}, P.false_ne_true(e))
    case +x <> +xt +y <> +yt:
      %bases_eq_len(xt, yt, P.and_true_r(B.Base.is_eq(x, y), B.Bases.eq(xt, yt), e)) :
        {1n+List.length(&2, B.Base, xt) == 1n+_ : Nat}
      {==}

def take_len_le(+xs: List<&2, B.Base>, +n: Nat, e: {List.length(&2, B.Base, List.take(&2, B.Base, xs, n)) == n : Nat}) ->
  {Nat.is_le(n, List.length(&2, B.Base, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, P.succ_ne_zero(q, Equal.sym(Nat, 0n, 1n+q, e)))
    case +x <> +t 0n:
      P.le_zero_l(1n+List.length(&2, B.Base, t))
    case +x <> +t 1n+q:
      take_len_le(t, q, P.succ_inj(List.length(&2, B.Base, List.take(&2, B.Base, t, q)), q, e))

def slice_len_fits.nil(+s: Nat, +n: Nat, h: {Nat.is_le(1n, n) == True{} : Bool}, e: {0n == n : Nat}) ->
  {Nat.is_le(Nat.add(s, n), 0n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(s, 0n), 0n) == True{} : Bool}, P.false_ne_true(h))
    case 1n+q:
      Empty.absurd({Nat.is_le(Nat.add(s, 1n+q), 0n) == True{} : Bool}, P.succ_ne_zero(q, Equal.sym(Nat, 0n, 1n+q, e)))

# A slice of n >= 1 bases from s that has n bases fits: s + n <= length.
def slice_len_fits(+xs: List<&2, B.Base>, +s: Nat, +n: Nat, h: {Nat.is_le(1n, n) == True{} : Bool},
  e: {List.length(&2, B.Base, List.take(&2, B.Base, List.drop(&2, B.Base, xs, s), n)) == n : Nat}) ->
  {Nat.is_le(Nat.add(s, n), List.length(&2, B.Base, xs)) == True{} : Bool}:
  match xs s:
    case Nil{} _:
      slice_len_fits.nil(s, n, h, e)
    case +x <> +t 0n:
      take_len_le(x <> t, n, e)
    case +x <> +t 1n+r:
      slice_len_fits(t, r, n, h, e)

# Nat
# ===

def min_le_id(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == 1n+p : Nat}, P.false_ne_true(e))
    case 1n+p 1n+q:
      %min_le_id(p, q, e) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

def le_min_l(+x: Nat, +a: Nat, +b: Nat, e: {Nat.is_le(x, Nat.min(a, b)) == True{} : Bool}) -> {Nat.is_le(x, a) == True{} : Bool}:
  match x a b:
    case 0n _ _:
      P.le_zero_l(a)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n+q) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p 1n+q 1n+r:
      le_min_l(p, q, r, e)

def pos_of_ne_zero(+p: Nat, e: {Nat.is_eq(p, 0n) == False{} : Bool}) -> {Nat.is_le(1n, p) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.true_ne_false(e))
    case 1n+q:
      P.le_zero_l(q)

# Reading alleles
# ===============

def read_len.cons(b: Maybe<&2, B.Base>, rest: Maybe<&2, List<&2, B.Base>>, +n: Nat,
  ih: @+xs: List<&2, B.Base> -> @+hr: {rest == Some{xs} : Maybe<&2, List<&2, B.Base>>} -> {List.length(&2, B.Base, xs) == n : Nat},
  +ys: List<&2, B.Base>, e: {B.Allele.read.cons(b, rest) == Some{ys} : Maybe<&2, List<&2, B.Base>>}) ->
  {List.length(&2, B.Base, ys) == 1n+n : Nat}:
  match b rest:
    case Some{+x} Some{+xs}:
      %some_inj(List<&2, B.Base>, x <> xs, ys, e) : {List.length(&2, B.Base, _) == 1n+n : Nat}
      %ih(xs, {==}) : {1n+List.length(&2, B.Base, xs) == 1n+_ : Nat}
      {==}
    case None{} _:
      Empty.absurd({List.length(&2, B.Base, ys) == 1n+n : Nat}, none_ne_some(List<&2, B.Base>, ys, e))
    case Some{x} None{}:
      Empty.absurd({List.length(&2, B.Base, ys) == 1n+n : Nat}, none_ne_some(List<&2, B.Base>, ys, e))

# An allele read from s has as many bases as s has letters.
def read_len(+s: String, +ys: List<&2, B.Base>, e: {B.Allele.read.go(s) == Some{ys} : Maybe<&2, List<&2, B.Base>>}) ->
  {List.length(&2, B.Base, ys) == String.length(s) : Nat}:
  match s:
    case SNil{}:
      %some_inj(List<&2, B.Base>, Nil{}, ys, e) : {List.length(&2, B.Base, _) == 0n : Nat}
      {==}
    case SCon{+h, +t}:
      read_len.cons(B.Base.of_letter(h), B.Allele.read.go(t), String.length(t), xs => hr => read_len(t, xs, hr), ys, e)

def letters_len(+s: String, e: {B.Text.is_letters(s) == True{} : Bool}) -> {Nat.is_le(1n, String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.false_ne_true(e))
    case SCon{h, +t}:
      P.le_zero_l(String.length(t))

def nonempty_len(+s: String, e: {String.is_empty(s) == False{} : Bool}) -> {Nat.is_le(1n, String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.true_ne_false(e))
    case SCon{h, +t}:
      P.le_zero_l(String.length(t))

# An allele read from a non-empty string is non-empty.
def allele_ne(+s: String, +y: List<&2, B.Base>, h: {Nat.is_le(1n, String.length(s)) == True{} : Bool},
  e: {B.Allele.read.go(s) == Some{y} : Maybe<&2, List<&2, B.Base>>}) -> {Nat.is_le(1n, L.len(y)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, B.Base, y), String.length(s), read_len(s, y, e)) : {Nat.is_le(1n, _) == True{} : Bool}
  h

def alts_ok.cons(a: Maybe<&2, List<&2, B.Base>>, rest: Maybe<&2, List<&2, List<&2, B.Base>>>, +x: String,
  ha: {B.Allele.read(x) == a : Maybe<&2, List<&2, B.Base>>}, hx: {String.is_empty(x) == False{} : Bool},
  ih: @+ys: List<&2, List<&2, B.Base>> -> @+hr: {rest == Some{ys} : Maybe<&2, List<&2, List<&2, B.Base>>>} -> {L.all_nonempty(ys) == True{} : Bool},
  +zs: List<&2, List<&2, B.Base>>, e: {B.Alleles.read.cons(a, rest) == Some{zs} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {L.all_nonempty(zs) == True{} : Bool}:
  match a rest:
    case Some{+y} Some{+ys}:
      %some_inj(List<&2, List<&2, B.Base>>, y <> ys, zs, e) : {L.all_nonempty(_) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(1n, L.len(y)), True{}, allele_ne(x, y, nonempty_len(x, hx), ha)) :
        {Bool.and(_, L.all_nonempty(ys)) == True{} : Bool}
      ih(ys, {==})
    case None{} _:
      Empty.absurd({L.all_nonempty(zs) == True{} : Bool}, none_ne_some(List<&2, List<&2, B.Base>>, zs, e))
    case Some{y} None{}:
      Empty.absurd({L.all_nonempty(zs) == True{} : Bool}, none_ne_some(List<&2, List<&2, B.Base>>, zs, e))

# ALT strings none of them empty read as alleles none of them empty.
def alts_ok(+xs: List<&2, String>, +ys: List<&2, List<&2, B.Base>>, +hx: {B.Text.any_empty(xs) == False{} : Bool},
  e: {B.Alleles.read(xs) == Some{ys} : Maybe<&2, List<&2, List<&2, B.Base>>>}) -> {L.all_nonempty(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      %some_inj(List<&2, List<&2, B.Base>>, Nil{}, ys, e) : {L.all_nonempty(_) == True{} : Bool}
      {==}
    case +x <> +t:
      alts_ok.cons(B.Allele.read(x), B.Alleles.read(t), x, {==},
        P.or_false_inv(String.is_empty(x), B.Text.any_empty(t), hx),
        zs => hr => alts_ok(t, zs, or_false_r(String.is_empty(x), B.Text.any_empty(t), hx), hr), ys, e)

def alts_len.cons(a: Maybe<&2, List<&2, B.Base>>, rest: Maybe<&2, List<&2, List<&2, B.Base>>>, +n: Nat,
  ih: @+ys: List<&2, List<&2, B.Base>> -> @+hr: {rest == Some{ys} : Maybe<&2, List<&2, List<&2, B.Base>>>} -> {List.length(&2, List<&2, B.Base>, ys) == n : Nat},
  +zs: List<&2, List<&2, B.Base>>, e: {B.Alleles.read.cons(a, rest) == Some{zs} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {List.length(&2, List<&2, B.Base>, zs) == 1n+n : Nat}:
  match a rest:
    case Some{+y} Some{+ys}:
      %some_inj(List<&2, List<&2, B.Base>>, y <> ys, zs, e) : {List.length(&2, List<&2, B.Base>, _) == 1n+n : Nat}
      %ih(ys, {==}) : {1n+List.length(&2, List<&2, B.Base>, ys) == 1n+_ : Nat}
      {==}
    case None{} _:
      Empty.absurd({List.length(&2, List<&2, B.Base>, zs) == 1n+n : Nat}, none_ne_some(List<&2, List<&2, B.Base>>, zs, e))
    case Some{y} None{}:
      Empty.absurd({List.length(&2, List<&2, B.Base>, zs) == 1n+n : Nat}, none_ne_some(List<&2, List<&2, B.Base>>, zs, e))

def alts_len(+xs: List<&2, String>, +ys: List<&2, List<&2, B.Base>>,
  e: {B.Alleles.read(xs) == Some{ys} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {List.length(&2, List<&2, B.Base>, ys) == List.length(&2, String, xs) : Nat}:
  match xs:
    case Nil{}:
      %some_inj(List<&2, List<&2, B.Base>>, Nil{}, ys, e) : {List.length(&2, List<&2, B.Base>, _) == 0n : Nat}
      {==}
    case +x <> +t:
      alts_len.cons(B.Allele.read(x), B.Alleles.read(t), List.length(&2, String, t), zs => hr => alts_len(t, zs, hr), ys, e)

def split_fin_ne(+cut: Bool, c: Char, r: List<&2, String>) -> {Nat.is_le(1n, List.length(&2, String, String.split.fin(c, r, cut))) == True{} : Bool}:
  match cut r:
    case True{} _:
      P.le_zero_l(List.length(&2, String, r))
    case False{} Nil{}:
      {==}
    case False{} h <> +t:
      P.le_zero_l(List.length(&2, String, t))

# Splitting gives at least one piece.
def split_ne(+s: String, +sep: Char) -> {Nat.is_le(1n, List.length(&2, String, String.split(s, sep))) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      split_fin_ne(Char.is_eq(h, sep), h, String.split(t, sep))
