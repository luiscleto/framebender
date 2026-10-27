import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_text.bend as X
import ./proof_run_dec.bend as D

# Record text facts for twice_run: split and join undo each other, Rec.put
# changes one field, alleles and numbers read back as written.

# Split and join
# ==============

law split_one:
  for +h: String
  for +c: Char
  for +hn: {X.no_c(h, c) == True{} : Bool}
  {String.split(h, c) == [h] : List<&2, String>}

def split_one(h, c, hn):
  match h:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +nx = P.not_true(Char.is_eq(x, c), P.and_true_l(Bool.not(Char.is_eq(x, c)), X.no_c(t, c), hn))
      %Equal.sym(Bool, Char.is_eq(x, c), False{}, nx) : {String.split.fin(x, String.split(t, c), _) == [SCon{x, t}] : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(t, c), [t], split_one(t, c, P.and_true_r(Bool.not(Char.is_eq(x, c)), X.no_c(t, c), hn))) :
        {String.split.push(x, _) == [SCon{x, t}] : List<&2, String>}
      {==}

# Joining pieces without the separator, then splitting, gives the pieces.
law split_join:
  for +t: List<&2, String>
  for +h: String
  for +c: Char
  for +hh: {X.no_c(h, c) == True{} : Bool}
  for +ht: {X.all_noc(t, c) == True{} : Bool}
  {String.split(String.join.go(t, h, SCon{c, SNil{}}), c) == h <> t : List<&2, String>}

def split_join(t, h, c, hh, ht):
  match t:
    case Nil{}:
      split_one(h, c, hh)
    case +h2 <> +t2:
      +j = String.join.go(t2, h2, SCon{c, SNil{}})
      %Equal.sym(List<&2, String>, String.split(h ++ SCon{c, j}, c), h <> String.split(j, c), X.split_app(h, j, c, hh)) :
        {_ == h <> h2 <> t2 : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(j, c), h2 <> t2,
        split_join(t2, h2, c, P.and_true_l(X.no_c(h2, c), X.all_noc(t2, c), ht), P.and_true_r(X.no_c(h2, c), X.all_noc(t2, c), ht))) :
        {h <> _ == h <> h2 <> t2 : List<&2, String>}
      {==}

law join_go_cons:
  for +r: List<&2, String>
  for +h: Char
  for +p: String
  for +sep: String
  {String.join.go(r, SCon{h, p}, sep) == SCon{h, String.join.go(r, p, sep)} : String}

def join_go_cons(r, h, p, sep):
  match r:
    case Nil{}:
      {==}
    case +q <> +t:
      {==}

def join_split.go(+h: Char, +t: String, +c: Char, ps: List<&2, String>, +x: Bool, +ex: {Char.is_eq(h, c) == x : Bool},
  ne: {ps == Nil{} : List<&2, String>} -> Empty,
  +ih: {String.join(ps, SCon{c, SNil{}}) == t : String}) ->
  {String.join(String.split.fin(h, ps, x), SCon{c, SNil{}}) == SCon{h, t} : String}:
  match ps:
    case Nil{}:
      Empty.absurd({String.join(String.split.fin(h, Nil{}, x), SCon{c, SNil{}}) == SCon{h, t} : String}, ne({==}))
    case +p <> +r:
      match x:
        case True{}:
          +j = String.join.go(r, p, SCon{c, SNil{}})
          %ih : {SCon{c, j} == SCon{h, _} : String}
          %X.char_eq_sound(h, c, ex) : {SCon{_, j} == SCon{h, j} : String}
          {==}
        case False{}:
          %Equal.sym(String, String.join.go(r, SCon{h, p}, SCon{c, SNil{}}), SCon{h, String.join.go(r, p, SCon{c, SNil{}})}, join_go_cons(r, h, p, SCon{c, SNil{}})) :
            {_ == SCon{h, t} : String}
          %ih : {SCon{h, String.join.go(r, p, SCon{c, SNil{}})} == SCon{h, _} : String}
          {==}

def join_split.nn(+s: String, +c: Char) -> ({String.split(s, c) == Nil{} : List<&2, String>} -> Empty):
  e => X.split_nn(s, c, e)

# Splitting, then joining with the separator, gives the text back.
law join_split:
  for +s: String
  for +c: Char
  {String.join(String.split(s, c), SCon{c, SNil{}}) == s : String}

def join_split(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      join_split.go(h, t, c, String.split(t, c), Char.is_eq(h, c), {==}, join_split.nn(t, c), join_split(t, c))

# Rec.put
# =======

def slen(xs: List<&2, String>) -> Nat:
  List.length(&2, String, xs)

law field_put_eq:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  for +hl: {Nat.is_lt(i, slen(xs)) == True{} : Bool}
  {B.Rec.field(B.Rec.put(xs, i, s), i) == s : String}

def field_put_eq(xs, i, s, hl):
  match xs i:
    case Nil{} _:
      Empty.absurd({B.Rec.field(B.Rec.put(Nil{}, i, s), i) == s : String},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(i, 0n), False{}, Equal.sym(Bool, Nat.is_lt(i, 0n), True{}, hl), P.lt_zero(i))))
    case +h <> +t 0n:
      {==}
    case +h <> +t 1n+j:
      field_put_eq(t, j, s, hl)

law field_put_ne:
  for +xs: List<&2, String>
  for +i: Nat
  for +j: Nat
  for +s: String
  for +hne: {Nat.is_eq(i, j) == False{} : Bool}
  {B.Rec.field(B.Rec.put(xs, i, s), j) == B.Rec.field(xs, j) : String}

def field_put_ne(xs, i, j, s, hne):
  match xs i j:
    case Nil{} _ _:
      {==}
    case +h <> +t 0n 0n:
      Empty.absurd({B.Rec.field(B.Rec.put(h <> t, 0n, s), 0n) == B.Rec.field(h <> t, 0n) : String}, P.true_ne_false(hne))
    case +h <> +t 0n 1n+k:
      {==}
    case +h <> +t 1n+i2 0n:
      {==}
    case +h <> +t 1n+i2 1n+k:
      field_put_ne(t, i2, k, s, hne)

law len_put:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  {slen(B.Rec.put(xs, i, s)) == slen(xs) : Nat}

def len_put(xs, i, s):
  match xs i:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      {==}
    case +h <> +t 1n+j:
      %len_put(t, j, s) : {1n+slen(B.Rec.put(t, j, s)) == 1n+_ : Nat}
      {==}

law noc_put:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  for +c: Char
  for +hx: {X.all_noc(xs, c) == True{} : Bool}
  for +hs: {X.no_c(s, c) == True{} : Bool}
  {X.all_noc(B.Rec.put(xs, i, s), c) == True{} : Bool}

def noc_put(xs, i, s, c, hx, hs):
  match xs i:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      S.and_intro(X.no_c(s, c), X.all_noc(t, c), hs, P.and_true_r(X.no_c(h, c), X.all_noc(t, c), hx))
    case +h <> +t 1n+j:
      S.and_intro(X.no_c(h, c), X.all_noc(B.Rec.put(t, j, s), c), P.and_true_l(X.no_c(h, c), X.all_noc(t, c), hx),
        noc_put(t, j, s, c, P.and_true_r(X.no_c(h, c), X.all_noc(t, c), hx), hs))

# Putting back the value a field has changes nothing.
law put_same:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  for +h: {B.Rec.field(xs, i) == s : String}
  {B.Rec.put(xs, i, s) == xs : List<&2, String>}

def put_same(xs, i, s, h):
  match xs i:
    case Nil{} _:
      {==}
    case +x <> +t 0n:
      %h : {_ <> t == x <> t : List<&2, String>}
      {==}
    case +x <> +t 1n+j:
      %Equal.sym(List<&2, String>, B.Rec.put(t, j, s), t, put_same(t, j, s, h)) : {x <> _ == x <> t : List<&2, String>}
      {==}

# The last field
# ==============

def lastp(t: List<&2, String>, h: String) -> String:
  match t:
    case Nil{}:
      h
    case h2 <> t2:
      lastp(t2, h2)

def last(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      lastp(t, h)

law last_put_ne:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  for +h: {Nat.is_eq(1n+i, slen(xs)) == False{} : Bool}
  {last(B.Rec.put(xs, i, s)) == last(xs) : String}

def last_put_ne(xs, i, s, h):
  match xs i:
    case Nil{} _:
      {==}
    case +x <> Nil{} 0n:
      Empty.absurd({last(B.Rec.put([x], 0n, s)) == last([x]) : String}, P.true_ne_false(h))
    case +x <> (+y <> +t) 0n:
      {==}
    case +x <> Nil{} 1n+j:
      {==}
    case +x <> (+y <> +t) 1n+0n:
      last_put_ne(y <> t, 0n, s, h)
    case +x <> (+y <> +t) 1n+1n+k:
      last_put_ne(y <> t, 1n+k, s, h)

law last_put_eq:
  for +xs: List<&2, String>
  for +i: Nat
  for +s: String
  for +h: {Nat.is_eq(1n+i, slen(xs)) == True{} : Bool}
  {last(B.Rec.put(xs, i, s)) == s : String}

def last_put_eq(xs, i, s, h):
  match xs i:
    case Nil{} _:
      Empty.absurd({last(B.Rec.put(Nil{}, i, s)) == s : String}, P.false_ne_true(h))
    case +x <> Nil{} 0n:
      {==}
    case +x <> (+y <> +t) 0n:
      Empty.absurd({last(B.Rec.put(x <> y <> t, 0n, s)) == s : String}, P.false_ne_true(h))
    case +x <> Nil{} 1n+j:
      Empty.absurd({last(B.Rec.put([x], 1n+j, s)) == s : String}, P.false_ne_true(h))
    case +x <> (+y <> +t) 1n+0n:
      last_put_eq(y <> t, 0n, s, h)
    case +x <> (+y <> +t) 1n+1n+k:
      last_put_eq(y <> t, 1n+k, s, h)

law last_field:
  for +xs: List<&2, String>
  for +i: Nat
  for +h: {Nat.is_eq(1n+i, slen(xs)) == True{} : Bool}
  {last(xs) == B.Rec.field(xs, i) : String}

def last_field(xs, i, h):
  match xs i:
    case Nil{} _:
      Empty.absurd({last(Nil{}) == B.Rec.field(Nil{}, i) : String}, P.false_ne_true(h))
    case +x <> Nil{} 0n:
      {==}
    case +x <> (+y <> +t) 0n:
      Empty.absurd({last(x <> y <> t) == B.Rec.field(x <> y <> t, 0n) : String}, P.false_ne_true(h))
    case +x <> Nil{} 1n+j:
      Empty.absurd({last([x]) == B.Rec.field([x], 1n+j) : String}, P.false_ne_true(h))
    case +x <> (+y <> +t) 1n+0n:
      last_field(y <> t, 0n, h)
    case +x <> (+y <> +t) 1n+1n+k:
      last_field(y <> t, 1n+k, h)

# Ending with CR
# ==============

def ecr(s: String) -> Bool:
  String.ends_with(s, "\r")

def hd_cr.go(+h: Char, acc1: String, acc2: String, +x: Bool, +ex: {Char.is_eq(h, '\r') == x : Bool}) ->
  {String.starts_with.go.if(SNil{}, acc1, x) == String.starts_with.go.if(SNil{}, acc2, x) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law hd_cr_rev:
  for +t: String
  for +h: Char
  for +acc1: String
  for +acc2: String
  {String.starts_with(String.reverse.go(SCon{h, t}, acc1), "\r") == String.starts_with(String.reverse.go(SCon{h, t}, acc2), "\r") : Bool}

def hd_cr_rev(t, h, acc1, acc2):
  match t:
    case SNil{}:
      hd_cr.go(h, acc1, acc2, Char.is_eq(h, '\r'), {==})
    case SCon{+h2, +t2}:
      hd_cr_rev(t2, h2, SCon{h, acc1}, SCon{h, acc2})

# Only the last char counts.
law ecr_app:
  for +a: String
  for +h: Char
  for +t: String
  {ecr(a ++ SCon{h, t}) == ecr(SCon{h, t}) : Bool}

def ecr_app(a, h, t):
  %Equal.sym(String, String.reverse.go(a ++ SCon{h, t}, SNil{}), String.reverse.go(SCon{h, t}, String.reverse.go(a, SNil{})), X.rev_app(a, SCon{h, t}, SNil{})) :
    {String.starts_with(_, "\r") == ecr(SCon{h, t}) : Bool}
  hd_cr_rev(t, h, String.reverse.go(a, SNil{}), SNil{})

law ecr_one:
  for +c: Char
  for +hc: {Char.is_eq(c, '\r') == False{} : Bool}
  {ecr(SCon{c, SNil{}}) == False{} : Bool}

def ecr_one(c, hc):
  %Equal.sym(Bool, Char.is_eq(c, '\r'), False{}, hc) : {String.starts_with.go.if(SNil{}, SNil{}, _) == False{} : Bool}
  {==}

def ecr_join.go(+c: Char, +hc: {Char.is_eq(c, '\r') == False{} : Bool}, j: String, +l: String,
  ih: {ecr(j) == ecr(l) : Bool}) -> {ecr(SCon{c, j}) == ecr(l) : Bool}:
  match j:
    case SNil{}:
      Equal.trans(Bool, ecr(SCon{c, SNil{}}), False{}, ecr(l), ecr_one(c, hc), ih)
    case SCon{+x, +t}:
      Equal.trans(Bool, ecr(SCon{c, SCon{x, t}}), ecr(SCon{x, t}), ecr(l), ecr_app(SCon{c, SNil{}}, x, t), ih)

# A joined text ends with CR when its last piece does.
law ecr_join:
  for +t: List<&2, String>
  for +h: String
  for +c: Char
  for +hc: {Char.is_eq(c, '\r') == False{} : Bool}
  {ecr(String.join.go(t, h, SCon{c, SNil{}})) == ecr(lastp(t, h)) : Bool}

def ecr_join(t, h, c, hc):
  match t:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      +j = String.join.go(t2, h2, SCon{c, SNil{}})
      Equal.trans(Bool, ecr(h ++ SCon{c, j}), ecr(SCon{c, j}), ecr(lastp(t2, h2)), ecr_app(h, c, j),
        ecr_join.go(c, hc, j, lastp(t2, h2), ecr_join(t2, h2, c, hc)))

law noc_ecr:
  for +s: String
  for +h: {X.no_c(s, '\r') == True{} : Bool}
  {ecr(s) == False{} : Bool}

def noc_ecr(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+x, SNil{}}:
      ecr_one(x, P.not_true(Char.is_eq(x, '\r'), P.and_true_l(Bool.not(Char.is_eq(x, '\r')), True{}, h)))
    case SCon{+x, SCon{+y, +t}}:
      Equal.trans(Bool, ecr(SCon{x, SCon{y, t}}), ecr(SCon{y, t}), False{}, ecr_app(SCon{x, SNil{}}, y, t),
        noc_ecr(SCon{y, t}, P.and_true_r(Bool.not(Char.is_eq(x, '\r')), X.no_c(SCon{y, t}, '\r'), h)))

# Alleles as text
# ===============

def letter_ok(b: B.Base) -> {B.Base.of_letter(B.Base.letter(b)) == Some{b} : Maybe<&2, B.Base>}:
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

law allele_rt:
  for +s: List<&2, B.Base>
  {B.Allele.read(B.Allele.show(s)) == Some{s} : Maybe<&2, List<&2, B.Base>>}

def allele_rt(s):
  match s:
    case Nil{}:
      {==}
    case +b <> +t:
      %Equal.sym(Maybe<&2, B.Base>, B.Base.of_letter(B.Base.letter(b)), Some{b}, letter_ok(b)) :
        {B.Allele.read.cons(_, B.Allele.read.go(B.Allele.show(t))) == Some{b <> t} : Maybe<&2, List<&2, B.Base>>}
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read.go(B.Allele.show(t)), Some{t}, allele_rt(t)) :
        {B.Allele.read.cons(Some{b}, _) == Some{b <> t} : Maybe<&2, List<&2, B.Base>>}
      {==}

law alleles_rt:
  for +y: List<&2, List<&2, B.Base>>
  {B.Alleles.read(B.Alleles.show(y)) == Some{y} : Maybe<&2, List<&2, List<&2, B.Base>>>}

def alleles_rt(y):
  match y:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(B.Allele.show(x)), Some{x}, allele_rt(x)) :
        {B.Alleles.read.cons(_, B.Alleles.read(B.Alleles.show(t))) == Some{x <> t} : Maybe<&2, List<&2, List<&2, B.Base>>>}
      %Equal.sym(Maybe<&2, List<&2, List<&2, B.Base>>>, B.Alleles.read(B.Alleles.show(t)), Some{t}, alleles_rt(t)) :
        {B.Alleles.read.cons(Some{x}, _) == Some{x <> t} : Maybe<&2, List<&2, List<&2, B.Base>>>}
      {==}

law show_len:
  for +s: List<&2, B.Base>
  {String.length(B.Allele.show(s)) == L.len(s) : Nat}

def show_len(s):
  match s:
    case Nil{}:
      {==}
    case +b <> +t:
      %show_len(t) : {1n+String.length(B.Allele.show(t)) == 1n+_ : Nat}
      {==}

def letter_alpha(b: B.Base) -> {Char.is_alpha(B.Base.letter(b)) == True{} : Bool}:
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

law show_all_letters:
  for +s: List<&2, B.Base>
  {B.Text.all_letters(B.Allele.show(s)) == True{} : Bool}

def show_all_letters(s):
  match s:
    case Nil{}:
      {==}
    case +b <> +t:
      S.and_intro(Char.is_alpha(B.Base.letter(b)), B.Text.all_letters(B.Allele.show(t)), letter_alpha(b), show_all_letters(t))

law show_letters:
  for +s: List<&2, B.Base>
  for +hne: {Nat.is_le(1n, L.len(s)) == True{} : Bool}
  {B.Text.is_letters(B.Allele.show(s)) == True{} : Bool}

def show_letters(s, hne):
  match s:
    case Nil{}:
      Empty.absurd({B.Text.is_letters(B.Allele.show(Nil{})) == True{} : Bool}, P.false_ne_true(hne))
    case +b <> +t:
      show_all_letters(b <> t)

# A char that is no base letter.
def not_letter(+c: Char) -> Bool:
  Bool.or(Char.is_eq('A', c), Bool.or(Char.is_eq('C', c), Bool.or(Char.is_eq('G', c), Bool.or(Char.is_eq('T', c), Char.is_eq('N', c)))))

law or_inv_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_inv_r(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.true_ne_false(e))

def letter_ne.go(b: B.Base, +c: Char,
  r0: {Char.is_eq('A', c) == False{} : Bool}, r1: {Char.is_eq('C', c) == False{} : Bool}, r2: {Char.is_eq('G', c) == False{} : Bool},
  r3: {Char.is_eq('T', c) == False{} : Bool}, r4: {Char.is_eq('N', c) == False{} : Bool}) -> {Char.is_eq(B.Base.letter(b), c) == False{} : Bool}:
  match b:
    case B.A{}:
      r0
    case B.C{}:
      r1
    case B.G{}:
      r2
    case B.T{}:
      r3
    case B.N{}:
      r4

def letter_ne(b: B.Base, +c: Char, +hc: {not_letter(c) == False{} : Bool}) -> {Char.is_eq(B.Base.letter(b), c) == False{} : Bool}:
  +eA = Char.is_eq('A', c)
  +eC = Char.is_eq('C', c)
  +eG = Char.is_eq('G', c)
  +eT = Char.is_eq('T', c)
  +eN = Char.is_eq('N', c)
  +r1 = or_inv_r(eA, Bool.or(eC, Bool.or(eG, Bool.or(eT, eN))), hc)
  +r2 = or_inv_r(eC, Bool.or(eG, Bool.or(eT, eN)), r1)
  +r3 = or_inv_r(eG, Bool.or(eT, eN), r2)
  letter_ne.go(b, c, P.or_false_inv(eA, Bool.or(eC, Bool.or(eG, Bool.or(eT, eN))), hc), P.or_false_inv(eC, Bool.or(eG, Bool.or(eT, eN)), r1),
    P.or_false_inv(eG, Bool.or(eT, eN), r2), P.or_false_inv(eT, eN, r3), or_inv_r(eT, eN, r3))

law show_noc:
  for +s: List<&2, B.Base>
  for +c: Char
  for +hc: {not_letter(c) == False{} : Bool}
  {X.no_c(B.Allele.show(s), c) == True{} : Bool}

def show_noc(s, c, hc):
  match s:
    case Nil{}:
      {==}
    case +b <> +t:
      S.and_intro(Bool.not(Char.is_eq(B.Base.letter(b), c)), X.no_c(B.Allele.show(t), c),
        (%Equal.sym(Bool, Char.is_eq(B.Base.letter(b), c), False{}, letter_ne(b, c, hc)) : {Bool.not(_) == True{} : Bool}; {==}),
        show_noc(t, c, hc))

def mlen(m: Maybe<&2, List<&2, B.Base>>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{xs}:
      Nat.is_eq(L.len(xs), n)

def read_mlen.go(a: Maybe<&2, B.Base>, m: Maybe<&2, List<&2, B.Base>>, +n: Nat, ih: {mlen(m, n) == True{} : Bool}) ->
  {mlen(B.Allele.read.cons(a, m), 1n+n) == True{} : Bool}:
  match a m:
    case Some{x} Some{xs}:
      ih
    case None{} _:
      {==}
    case Some{x} None{}:
      {==}

law read_mlen:
  for +str: String
  {mlen(B.Allele.read.go(str), String.length(str)) == True{} : Bool}

def read_mlen(str):
  match str:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      read_mlen.go(B.Base.of_letter(h), B.Allele.read.go(t), String.length(t), read_mlen(t))

# An allele read from text has its length.
law read_len:
  for +str: String
  for +bs: List<&2, B.Base>
  for e: {B.Allele.read(str) == Some{bs} : Maybe<&2, List<&2, B.Base>>}
  {String.length(str) == L.len(bs) : Nat}

def read_len(str, bs, e):
  +h = {(%e : {mlen(_, String.length(str)) == True{} : Bool}; read_mlen(str)) : {Nat.is_eq(L.len(bs), String.length(str)) == True{} : Bool}}
  Equal.sym(Nat, L.len(bs), String.length(str), P.eq_sound(L.len(bs), String.length(str), h))

def ane(m: Maybe<&2, List<&2, List<&2, B.Base>>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ys}:
      L.all_nonempty(ys)

law nonempty_len:
  for +x: String
  for +h: {String.is_empty(x) == False{} : Bool}
  {Nat.is_le(1n, String.length(x)) == True{} : Bool}

def nonempty_len(x, h):
  match x:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.true_ne_false(h))
    case SCon{+c, +t}:
      P.le_zero_l(String.length(t))

def alleles_ne.go(+x: String, a: Maybe<&2, List<&2, B.Base>>, ea: {B.Allele.read(x) == a : Maybe<&2, List<&2, B.Base>>},
  m: Maybe<&2, List<&2, List<&2, B.Base>>>, hx: {String.is_empty(x) == False{} : Bool}, ih: {ane(m) == True{} : Bool}) ->
  {ane(B.Alleles.read.cons(a, m)) == True{} : Bool}:
  match a m:
    case Some{+bx} Some{ys}:
      +hl = {(%read_len(x, bx, ea) : {Nat.is_le(1n, _) == True{} : Bool}; nonempty_len(x, hx)) :
        {Nat.is_le(1n, L.len(bx)) == True{} : Bool}}
      S.and_intro(Nat.is_le(1n, L.len(bx)), L.all_nonempty(ys), hl, ih)
    case None{} _:
      {==}
    case Some{bx} None{}:
      {==}

law alleles_ne:
  for +xs: List<&2, String>
  for +h: {B.Text.any_empty(xs) == False{} : Bool}
  {ane(B.Alleles.read(xs)) == True{} : Bool}

def alleles_ne(xs, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      alleles_ne.go(x, B.Allele.read(x), {==}, B.Alleles.read(t), P.or_false_inv(String.is_empty(x), B.Text.any_empty(t), h),
        alleles_ne(t, or_inv_r(String.is_empty(x), B.Text.any_empty(t), h)))

def alm(m: Maybe<&2, List<&2, List<&2, B.Base>>>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ys}:
      Nat.is_eq(List.length(&2, List<&2, B.Base>, ys), n)

def alleles_len.go(a: Maybe<&2, List<&2, B.Base>>, m: Maybe<&2, List<&2, List<&2, B.Base>>>, +n: Nat, ih: {alm(m, n) == True{} : Bool}) ->
  {alm(B.Alleles.read.cons(a, m), 1n+n) == True{} : Bool}:
  match a m:
    case Some{x} Some{xs}:
      ih
    case None{} _:
      {==}
    case Some{x} None{}:
      {==}

law alleles_len:
  for +xs: List<&2, String>
  {alm(B.Alleles.read(xs), slen(xs)) == True{} : Bool}

def alleles_len(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      alleles_len.go(B.Allele.read(x), B.Alleles.read(t), slen(t), alleles_len(t))

# INFO/END
# ========

def repl(l: List<&2, Maybe<&2, Nat>>, +e: Nat) -> List<&2, Maybe<&2, Nat>>:
  match l:
    case Nil{}:
      Nil{}
    case x <> t:
      Some{e} <> repl(t, e)

def drop0(+s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      {==}

def ends_set.go(+p: String, +t: List<&2, String>, +e: Nat, +b: Bool, +eb: {String.eq(B.Info.key(p), "END") == b : Bool},
  +ih: {B.Info.ends.go(B.Info.set_end.go(t, e)) == repl(B.Info.ends.go(t), e) : List<&2, Maybe<&2, Nat>>}) ->
  {B.Info.ends.go(B.Info.set_end.put(b, p, e) <> B.Info.set_end.go(t, e)) == repl(B.Info.ends.put(b, p, B.Info.ends.go(t)), e) : List<&2, Maybe<&2, Nat>>}:
  match b:
    case True{}:
      %Equal.sym(String, String.drop(Nat.show(e), 0n), Nat.show(e), drop0(Nat.show(e))) :
        {B.Pos.read(_) <> B.Info.ends.go(B.Info.set_end.go(t, e)) == Some{e} <> repl(B.Info.ends.go(t), e) : List<&2, Maybe<&2, Nat>>}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.read(Nat.show(e)), Some{e}, D.show_read(e)) :
        {_ <> B.Info.ends.go(B.Info.set_end.go(t, e)) == Some{e} <> repl(B.Info.ends.go(t), e) : List<&2, Maybe<&2, Nat>>}
      %ih : {Some{e} <> B.Info.ends.go(B.Info.set_end.go(t, e)) == Some{e} <> _ : List<&2, Maybe<&2, Nat>>}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(B.Info.key(p), "END"), False{}, eb) :
        {B.Info.ends.put(_, p, B.Info.ends.go(B.Info.set_end.go(t, e))) == repl(B.Info.ends.go(t), e) : List<&2, Maybe<&2, Nat>>}
      ih

# Setting END makes every END entry read as e.
law ends_set:
  for +ps: List<&2, String>
  for +e: Nat
  {B.Info.ends.go(B.Info.set_end.go(ps, e)) == repl(B.Info.ends.go(ps), e) : List<&2, Maybe<&2, Nat>>}

def ends_set(ps, e):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      ends_set.go(p, t, e, String.eq(B.Info.key(p), "END"), {==}, ends_set(t, e))

law end_ok_repl:
  for +l: List<&2, Maybe<&2, Nat>>
  for +e: Nat
  for +e1: Nat
  for h: {B.Info.end_ok.go(l, e1) == True{} : Bool}
  {B.Info.end_ok.go(repl(l, e), e) == True{} : Bool}

def end_ok_repl(l, e, e1, h):
  match l:
    case Nil{}:
      {==}
    case None{} <> t:
      Empty.absurd({B.Info.end_ok.go(repl(None{} <> t, e), e) == True{} : Bool}, P.false_ne_true(h))
    case Some{v} <> Nil{}:
      P.eq_refl(e)
    case Some{v} <> (y <> t):
      Empty.absurd({B.Info.end_ok.go(repl(Some{v} <> y <> t, e), e) == True{} : Bool}, P.false_ne_true(h))

law digits_noc:
  for +s: String
  for +c: Char
  for +hs: {D.all_dig(s) == True{} : Bool}
  for +hc: {Maybe.is_some(&2, Nat, B.Pos.digit(c)) == False{} : Bool}
  {X.no_c(s, c) == True{} : Bool}

def digits_noc.go(+h: Char, +c: Char, +x: Bool, +ex: {Char.is_eq(h, c) == x : Bool},
  +hh: {Maybe.is_some(&2, Nat, B.Pos.digit(h)) == True{} : Bool},
  +hc: {Maybe.is_some(&2, Nat, B.Pos.digit(c)) == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, Maybe.is_some(&2, Nat, B.Pos.digit(c)), False{},
          (%X.char_eq_sound(h, c, ex) : {True{} == Maybe.is_some(&2, Nat, B.Pos.digit(_)) : Bool}; Equal.sym(Bool, Maybe.is_some(&2, Nat, B.Pos.digit(h)), True{}, hh)), hc)))

def digits_noc(s, c, hs, hc):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      S.and_intro(Bool.not(Char.is_eq(h, c)), X.no_c(t, c),
        digits_noc.go(h, c, Char.is_eq(h, c), {==}, P.and_true_l(Maybe.is_some(&2, Nat, B.Pos.digit(h)), D.all_dig(t), hs), hc),
        digits_noc(t, c, P.and_true_r(Maybe.is_some(&2, Nat, B.Pos.digit(h)), D.all_dig(t), hs), hc))

def endp(+e: Nat) -> String:
  "END=" ++ Nat.show(e)

def put_noc(b: Bool, +p: String, +e: Nat, +c: Char, +hp: {X.no_c(p, c) == True{} : Bool}, +hend: {X.no_c(endp(e), c) == True{} : Bool}) ->
  {X.no_c(B.Info.set_end.put(b, p, e), c) == True{} : Bool}:
  match b:
    case True{}:
      hend
    case False{}:
      hp

law set_noc:
  for +ps: List<&2, String>
  for +e: Nat
  for +c: Char
  for +hps: {X.all_noc(ps, c) == True{} : Bool}
  for +hend: {X.no_c(endp(e), c) == True{} : Bool}
  {X.all_noc(B.Info.set_end.go(ps, e), c) == True{} : Bool}

def set_noc(ps, e, c, hps, hend):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      S.and_intro(X.no_c(B.Info.set_end.put(String.eq(B.Info.key(p), "END"), p, e), c), X.all_noc(B.Info.set_end.go(t, e), c),
        put_noc(String.eq(B.Info.key(p), "END"), p, e, c, P.and_true_l(X.no_c(p, c), X.all_noc(t, c), hps), hend),
        set_noc(t, e, c, P.and_true_r(X.no_c(p, c), X.all_noc(t, c), hps), hend))

def end_set_ok.go(ps: List<&2, String>, +e: Nat, +e1: Nat, +hps: {X.all_noc(ps, ';') == True{} : Bool},
  ne: {ps == Nil{} : List<&2, String>} -> Empty,
  h: {B.Info.end_ok.go(B.Info.ends.go(ps), e1) == True{} : Bool}) ->
  {B.Info.end_ok.go(B.Info.ends.go(String.split(String.join(B.Info.set_end.go(ps, e), ";"), ';')), e) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({B.Info.end_ok.go(B.Info.ends.go(String.split(String.join(B.Info.set_end.go(Nil{}, e), ";"), ';')), e) == True{} : Bool}, ne({==}))
    case +p <> +r:
      +hend = digits_noc(Nat.show(e), ';', D.show_digits(e), {==})
      +b = String.eq(B.Info.key(p), "END")
      +q0 = B.Info.set_end.put(b, p, e)
      +qr = B.Info.set_end.go(r, e)
      %Equal.sym(List<&2, String>, String.split(String.join.go(qr, q0, ";"), ';'), q0 <> qr,
        split_join(qr, q0, ';', put_noc(b, p, e, ';', P.and_true_l(X.no_c(p, ';'), X.all_noc(r, ';'), hps), hend),
          set_noc(r, e, ';', P.and_true_r(X.no_c(p, ';'), X.all_noc(r, ';'), hps), hend))) :
        {B.Info.end_ok.go(B.Info.ends.go(_), e) == True{} : Bool}
      %Equal.sym(List<&2, Maybe<&2, Nat>>, B.Info.ends.go(B.Info.set_end.go(p <> r, e)), repl(B.Info.ends.go(p <> r), e), ends_set(p <> r, e)) :
        {B.Info.end_ok.go(_, e) == True{} : Bool}
      end_ok_repl(B.Info.ends.go(p <> r), e, e1, h)

# Setting END to e on a record whose END was fine gives a fine END for e.
law end_set_ok:
  for +info: String
  for +e: Nat
  for +e1: Nat
  for h: {B.Info.end_ok(info, e1) == True{} : Bool}
  {B.Info.end_ok(B.Info.set_end(info, e), e) == True{} : Bool}

def end_set_ok(info, e, e1, h):
  end_set_ok.go(String.split(info, ';'), e, e1, X.pieces_noc(info, ';'), ne => X.split_nn(info, ';', ne), h)

law last_set:
  for +r: List<&2, String>
  for +p: String
  for +e: Nat
  {lastp(B.Info.set_end.go(r, e), B.Info.set_end.put(String.eq(B.Info.key(p), "END"), p, e)) ==
    B.Info.set_end.put(String.eq(B.Info.key(lastp(r, p)), "END"), lastp(r, p), e) : String}

def last_set(r, p, e):
  match r:
    case Nil{}:
      {==}
    case +q <> +t:
      last_set(t, q, e)

def ecr_put(b: Bool, +l: String, +e: Nat, h: {ecr(B.Info.set_end.put(b, l, e)) == True{} : Bool}) -> {ecr(l) == True{} : Bool}:
  match b:
    case False{}:
      h
    case True{}:
      +hn = {digits_noc(Nat.show(e), '\r', D.show_digits(e), {==}) : {X.no_c(endp(e), '\r') == True{} : Bool}}
      Empty.absurd({ecr(l) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, ecr(endp(e)), False{}, Equal.sym(Bool, ecr(endp(e)), True{}, h), noc_ecr(endp(e), hn))))

def ecr_set.go(ps: List<&2, String>, +e: Nat, ne: {ps == Nil{} : List<&2, String>} -> Empty,
  h: {ecr(String.join(B.Info.set_end.go(ps, e), ";")) == True{} : Bool}) -> {ecr(String.join(ps, ";")) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({ecr(String.join(Nil{}, ";")) == True{} : Bool}, ne({==}))
    case +p <> +r:
      +b = String.eq(B.Info.key(p), "END")
      +q0 = B.Info.set_end.put(b, p, e)
      +qr = B.Info.set_end.go(r, e)
      +L = lastp(r, p)
      +h1 = {(%ecr_join(qr, q0, ';', {==}) : {_ == True{} : Bool}; h) : {ecr(lastp(qr, q0)) == True{} : Bool}}
      +h2 = {(%last_set(r, p, e) : {ecr(_) == True{} : Bool}; h1) : {ecr(B.Info.set_end.put(String.eq(B.Info.key(L), "END"), L, e)) == True{} : Bool}}
      %Equal.sym(Bool, ecr(String.join.go(r, p, ";")), ecr(L), ecr_join(r, p, ';', {==})) : {_ == True{} : Bool}
      ecr_put(String.eq(B.Info.key(L), "END"), L, e, h2)

# Setting END never makes INFO end with CR.
law ecr_set:
  for +info: String
  for +e: Nat
  for h: {ecr(B.Info.set_end(info, e)) == True{} : Bool}
  {ecr(info) == True{} : Bool}

def ecr_set(info, e, h):
  %join_split(info, ';') : {ecr(_) == True{} : Bool}
  ecr_set.go(String.split(info, ';'), e, ne => X.split_nn(info, ';', ne), h)

# No char c
# =========

law join_noc:
  for +t: List<&2, String>
  for +h: String
  for +sep: String
  for +c: Char
  for +hh: {X.no_c(h, c) == True{} : Bool}
  for +ht: {X.all_noc(t, c) == True{} : Bool}
  for +hs: {X.no_c(sep, c) == True{} : Bool}
  {X.no_c(String.join.go(t, h, sep), c) == True{} : Bool}

def join_noc(t, h, sep, c, hh, ht, hs):
  match t:
    case Nil{}:
      hh
    case +h2 <> +t2:
      X.no_c_app(h, sep ++ String.join.go(t2, h2, sep), c, hh,
        X.no_c_app(sep, String.join.go(t2, h2, sep), c, hs,
          join_noc(t2, h2, sep, c, P.and_true_l(X.no_c(h2, c), X.all_noc(t2, c), ht), P.and_true_r(X.no_c(h2, c), X.all_noc(t2, c), ht), hs)))

law join_noc2:
  for +xs: List<&2, String>
  for +sep: String
  for +c: Char
  for +hx: {X.all_noc(xs, c) == True{} : Bool}
  for +hs: {X.no_c(sep, c) == True{} : Bool}
  {X.no_c(String.join(xs, sep), c) == True{} : Bool}

def join_noc2(xs, sep, c, hx, hs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      join_noc(t, h, sep, c, P.and_true_l(X.no_c(h, c), X.all_noc(t, c), hx), P.and_true_r(X.no_c(h, c), X.all_noc(t, c), hx), hs)

def sub_noc.push(+x: Char, +c: Char, ps: List<&2, String>, +hx: {Bool.not(Char.is_eq(x, c)) == True{} : Bool},
  +ih: {X.all_noc(ps, c) == True{} : Bool}) -> {X.all_noc(String.split.push(x, ps), c) == True{} : Bool}:
  match ps:
    case Nil{}:
      S.and_intro(X.no_c(SCon{x, SNil{}}, c), True{}, S.and_intro(Bool.not(Char.is_eq(x, c)), True{}, hx, {==}), {==})
    case +p <> +r:
      S.and_intro(X.no_c(SCon{x, p}, c), X.all_noc(r, c),
        S.and_intro(Bool.not(Char.is_eq(x, c)), X.no_c(p, c), hx, P.and_true_l(X.no_c(p, c), X.all_noc(r, c), ih)),
        P.and_true_r(X.no_c(p, c), X.all_noc(r, c), ih))

def sub_noc.fin(+x: Char, +c: Char, ps: List<&2, String>, b: Bool, +hx: {Bool.not(Char.is_eq(x, c)) == True{} : Bool},
  +ih: {X.all_noc(ps, c) == True{} : Bool}) -> {X.all_noc(String.split.fin(x, ps, b), c) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      sub_noc.push(x, c, ps, hx, ih)

# Pieces of a text without c have no c.
law pieces_sub_noc:
  for +s: String
  for +sep: Char
  for +c: Char
  for +h: {X.no_c(s, c) == True{} : Bool}
  {X.all_noc(String.split(s, sep), c) == True{} : Bool}

def pieces_sub_noc(s, sep, c, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      sub_noc.fin(x, c, String.split(t, sep), Char.is_eq(x, sep), P.and_true_l(Bool.not(Char.is_eq(x, c)), X.no_c(t, c), h),
        pieces_sub_noc(t, sep, c, P.and_true_r(Bool.not(Char.is_eq(x, c)), X.no_c(t, c), h)))

law field_noc:
  for +xs: List<&2, String>
  for +i: Nat
  for +c: Char
  for +h: {X.all_noc(xs, c) == True{} : Bool}
  {X.no_c(B.Rec.field(xs, i), c) == True{} : Bool}

def field_noc(xs, i, c, h):
  match xs i:
    case Nil{} _:
      {==}
    case +x <> +t 0n:
      P.and_true_l(X.no_c(x, c), X.all_noc(t, c), h)
    case +x <> +t 1n+j:
      field_noc(t, j, c, P.and_true_r(X.no_c(x, c), X.all_noc(t, c), h))

law shows_noc:
  for +y: List<&2, List<&2, B.Base>>
  for +c: Char
  for +hc: {not_letter(c) == False{} : Bool}
  {X.all_noc(B.Alleles.show(y), c) == True{} : Bool}

def shows_noc(y, c, hc):
  match y:
    case Nil{}:
      {==}
    case +x <> +t:
      S.and_intro(X.no_c(B.Allele.show(x), c), X.all_noc(B.Alleles.show(t), c), show_noc(x, c, hc), shows_noc(t, c, hc))

# INFO after setting END has no c when INFO had none (c not a digit nor in "END=;").
law set_end_noc:
  for +info: String
  for +e: Nat
  for +c: Char
  for +h: {X.no_c(info, c) == True{} : Bool}
  for +hend: {X.no_c(endp(e), c) == True{} : Bool}
  for +hs: {X.no_c(";", c) == True{} : Bool}
  {X.no_c(B.Info.set_end(info, e), c) == True{} : Bool}

def set_end_noc(info, e, c, h, hend, hs):
  join_noc2(B.Info.set_end.go(String.split(info, ';'), e), ";", c, set_noc(String.split(info, ';'), e, c, pieces_sub_noc(info, ';', c, h), hend), hs)
