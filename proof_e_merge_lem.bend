import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_e_defs.bend as SD
import ./proof_run_base.bend as RB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area "merge": general lemmas (Bools, Nat.max, Maybe, strings) and
# the item lists of norm_par.bend's merge against proof_e_defs.bend's
# (notes/parallel_proofs_merge.md).

# Bools
# =====

law not_t:
  for +x: Bool
  for +h: {Bool.not(x) == True{} : Bool}
  {x == False{} : Bool}

def not_t(x, h):
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(h))

# a || b with a false gives b.
law or_fl:
  for +a: Bool
  for +b: Bool
  for +ha: {a == False{} : Bool}
  for +h: {Bool.or(a, b) == True{} : Bool}
  {b == True{} : Bool}

def or_fl(a, b, ha, h):
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == True{} : Bool}, N.true_ne_false(ha))

law or_cong:
  for +a: Bool
  for +a2: Bool
  for +b: Bool
  for +b2: Bool
  for +ea: {a == a2 : Bool}
  for +eb: {b == b2 : Bool}
  {Bool.or(a, b) == Bool.or(a2, b2) : Bool}

def or_cong(a, a2, b, b2, ea, eb):
  %ea : {Bool.or(a, b) == Bool.or(_, b2) : Bool}
  %eb : {Bool.or(a, b) == Bool.or(a, _) : Bool}
  {==}

law and_mk:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_mk(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

law and_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law and3_swap:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(b, a), c) : Bool}

def and3_swap(a, b, c):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Nat.max
# =======

law max_z:
  for +m: Nat
  {Nat.max(m, 0n) == m : Nat}

def max_z(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

law max_comm:
  for +a: Nat
  for +b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

def max_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %max_comm(p, q) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

law max_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}

def max_assoc(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      %max_assoc(p, q, r) : {1n+Nat.max(Nat.max(p, q), r) == 1n+_ : Nat}
      {==}

law max_swap:
  for +m: Nat
  for +a: Nat
  for +z: Nat
  {Nat.max(Nat.max(m, a), z) == Nat.max(Nat.max(m, z), a) : Nat}

def max_swap(m, a, z):
  Equal.trans(Nat, Nat.max(Nat.max(m, a), z), Nat.max(m, Nat.max(a, z)), Nat.max(Nat.max(m, z), a), max_assoc(m, a, z),
    Equal.trans(Nat, Nat.max(m, Nat.max(a, z)), Nat.max(m, Nat.max(z, a)), Nat.max(Nat.max(m, z), a),
      Equal.cong(Nat, Nat, y => Nat.max(m, y), Nat.max(a, z), Nat.max(z, a), max_comm(a, z)),
      Equal.sym(Nat, Nat.max(Nat.max(m, z), a), Nat.max(m, Nat.max(z, a)), max_assoc(m, z, a))))

law le_max_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}

def le_max_l(a, b):
  match a b:
    case 0n _:
      N.le_zero_l(b)
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      le_max_l(p, q)

law le_max_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}

def le_max_r(a, b):
  match a b:
    case 0n _:
      N.le_refl(b)
    case 1n+p 0n:
      N.le_zero_l(1n+p)
    case 1n+p 1n+q:
      le_max_r(p, q)

law max_le:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for +ha: {Nat.is_le(a, k) == True{} : Bool}
  for +hb: {Nat.is_le(b, k) == True{} : Bool}
  {Nat.is_le(Nat.max(a, b), k) == True{} : Bool}

def max_le(a, b, k, ha, hb):
  match a b k:
    case 0n _ _:
      hb
    case 1n+p 0n _:
      ha
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+Nat.max(p, q), 0n) == True{} : Bool}, N.false_ne_true(ha))
    case 1n+p 1n+q 1n+r:
      max_le(p, q, r, ha, hb)

# Maybe
# =====

law or_none:
  for +m: Maybe<&2, NR.Ck>
  {Maybe.or(&2, NR.Ck, m, None{}) == m : Maybe<&2, NR.Ck>}

def or_none(m):
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

law or_some:
  for +m: Maybe<&2, NR.Ck>
  for +x: NR.Ck
  for +y: Maybe<&2, NR.Ck>
  {Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, m, Some{x}), y) == Maybe.or(&2, NR.Ck, m, Some{x}) : Maybe<&2, NR.Ck>}

def or_some(m, x, y):
  match m:
    case None{}:
      {==}
    case Some{+z}:
      {==}

law or_assoc:
  for +a: Maybe<&2, NR.Ck>
  for +b: Maybe<&2, NR.Ck>
  for +c: Maybe<&2, NR.Ck>
  {Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, a, b), c) == Maybe.or(&2, NR.Ck, a, Maybe.or(&2, NR.Ck, b, c)) : Maybe<&2, NR.Ck>}

def or_assoc(a, b, c):
  match a:
    case None{}:
      {==}
    case Some{+z}:
      {==}

# Strings and lists
# =================

law str_assoc:
  for +a: String
  for +b: String
  for +c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def str_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %str_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

law take0:
  for +s: String
  {String.take(s, 0n) == "" : String}

def take0(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      {==}

law take_add:
  for +s: String
  for +a: Nat
  for +b: Nat
  {String.take(s, Nat.add(a, b)) == String.append(String.take(s, a), String.take(String.drop(s, a), b)) : String}

def take_add(s, a, b):
  match s a:
    case SNil{} _:
      {==}
    case SCon{+h, +t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      %take_add(t, p, b) : {SCon{h, String.take(t, Nat.add(p, b))} == SCon{h, _} : String}
      {==}

# A text cut to n letters, cut to n again.
law ctake:
  for +xs: List<&2, U32>
  for +n: Nat
  {String.take(NR.chars(List.take(&2, U32, xs, n)), n) == NR.chars(List.take(&2, U32, xs, n)) : String}

def ctake(xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %ctake(t, p) : {SCon{Chr{x}, String.take(NR.chars(List.take(&2, U32, t, p)), p)} == SCon{Chr{x}, _} : String}
      {==}

law push_eq:
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  {NR.push_cur(c, e) == R.push_cur(c, e) : List<&2, String>}

def push_eq(c, e):
  match c:
    case None{}:
      {==}
    case Some{+s}:
      {==}

law cnt_eq:
  for +a: R.Cnt
  for +b: R.Cnt
  {W.cnt_add(a, b) == SD.cnt_add(a, b) : R.Cnt}

def cnt_eq(a, b):
  match a b:
    case R.Cnt{+a1, +a2, +a3, +a4} R.Cnt{+b1, +b2, +b3, +b4}:
      {==}

law chroms_eq:
  for +xs: List<&2, String>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  {SD.chroms_ok(xs, c0, se, sc) == W.chroms_ok(xs, c0, se, sc) : Bool}

def chroms_eq(xs, c0, se, sc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %chroms_eq(t, c0, se, sc) : {Bool.and(Bool.or(String.eq(x, c0), Bool.and(Bool.not(R.has(x, se)), Bool.not(R.is_cur(sc, x)))), SD.chroms_ok(t, c0, se, sc)) == Bool.and(Bool.or(String.eq(x, c0), Bool.and(Bool.not(R.has(x, se)), Bool.not(R.is_cur(sc, x)))), _) : Bool}
      {==}

law chroms_full:
  for +tc: Maybe<&2, String>
  for +te: List<&2, String>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  {SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc) == W.chroms_ok(List.append(&2, String, W.cur_list(tc), te), c0, se, sc) : Bool}

def chroms_full(tc, te, c0, se, sc):
  match tc:
    case None{}:
      chroms_eq(te, c0, se, sc)
    case Some{+c}:
      chroms_eq(Con{c, te}, c0, se, sc)

# Max of input POS (norm_par.bend's)
# ==================================

law mi_split:
  for +cs: List<&2, NR.Ck>
  for +m: Nat
  {W.max_inpos(cs, m) == Nat.max(m, W.max_inpos(cs, 0n)) : Nat}

def mi_split(cs, m):
  match cs:
    case Nil{}:
      Equal.sym(Nat, Nat.max(m, 0n), m, max_z(m))
    case Con{+x, +t}:
      Equal.trans(Nat, W.max_inpos(t, Nat.max(m, W.ck_inpos(x))), Nat.max(Nat.max(m, W.ck_inpos(x)), W.max_inpos(t, 0n)), Nat.max(m, W.max_inpos(t, W.ck_inpos(x))),
        mi_split(t, Nat.max(m, W.ck_inpos(x))),
        Equal.trans(Nat, Nat.max(Nat.max(m, W.ck_inpos(x)), W.max_inpos(t, 0n)), Nat.max(m, Nat.max(W.ck_inpos(x), W.max_inpos(t, 0n))), Nat.max(m, W.max_inpos(t, W.ck_inpos(x))),
          max_assoc(m, W.ck_inpos(x), W.max_inpos(t, 0n)),
          Equal.cong(Nat, Nat, y => Nat.max(m, y), Nat.max(W.ck_inpos(x), W.max_inpos(t, 0n)), W.max_inpos(t, W.ck_inpos(x)),
            Equal.sym(Nat, W.max_inpos(t, W.ck_inpos(x)), Nat.max(W.ck_inpos(x), W.max_inpos(t, 0n)), mi_split(t, W.ck_inpos(x))))))

law mi_max:
  for +r: List<&2, NR.Ck>
  for +m: Nat
  for +a: Nat
  {W.max_inpos(r, Nat.max(m, a)) == Nat.max(W.max_inpos(r, m), a) : Nat}

def mi_max(r, m, a):
  Equal.trans(Nat, W.max_inpos(r, Nat.max(m, a)), Nat.max(Nat.max(m, a), W.max_inpos(r, 0n)), Nat.max(W.max_inpos(r, m), a),
    mi_split(r, Nat.max(m, a)),
    Equal.trans(Nat, Nat.max(Nat.max(m, a), W.max_inpos(r, 0n)), Nat.max(Nat.max(m, W.max_inpos(r, 0n)), a), Nat.max(W.max_inpos(r, m), a),
      max_swap(m, a, W.max_inpos(r, 0n)),
      Equal.cong(Nat, Nat, y => Nat.max(y, a), Nat.max(m, W.max_inpos(r, 0n)), W.max_inpos(r, m),
        Equal.sym(Nat, W.max_inpos(r, m), Nat.max(m, W.max_inpos(r, 0n)), mi_split(r, m)))))

law mi_app:
  for +f: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  for +m: Nat
  {W.max_inpos(NR.append_ck(f, y), m) == W.max_inpos(y, W.max_inpos(f, m)) : Nat}

def mi_app(f, y, m):
  match f:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      mi_app(t, y, Nat.max(m, W.ck_inpos(x)))

law mi_rev:
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  for +m: Nat
  {W.max_inpos(NR.rev_ck(b, acc), m) == W.max_inpos(acc, W.max_inpos(b, m)) : Nat}

def mi_rev(b, acc, m):
  match b:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, W.max_inpos(NR.rev_ck(t, Con{x, acc}), m), W.max_inpos(acc, Nat.max(W.max_inpos(t, m), W.ck_inpos(x))), W.max_inpos(acc, W.max_inpos(t, Nat.max(m, W.ck_inpos(x)))),
        mi_rev(t, Con{x, acc}, m),
        Equal.cong(Nat, Nat, z => W.max_inpos(acc, z), Nat.max(W.max_inpos(t, m), W.ck_inpos(x)), W.max_inpos(t, Nat.max(m, W.ck_inpos(x))),
          Equal.sym(Nat, W.max_inpos(t, Nat.max(m, W.ck_inpos(x))), Nat.max(W.max_inpos(t, m), W.ck_inpos(x)), mi_max(t, m, W.ck_inpos(x)))))

law mi_comm:
  for +b: List<&2, NR.Ck>
  for +f: List<&2, NR.Ck>
  for +m: Nat
  {W.max_inpos(b, W.max_inpos(f, m)) == W.max_inpos(f, W.max_inpos(b, m)) : Nat}

def mi_comm(b, f, m):
  Equal.trans(Nat, W.max_inpos(b, W.max_inpos(f, m)), Nat.max(W.max_inpos(f, m), W.max_inpos(b, 0n)), W.max_inpos(f, W.max_inpos(b, m)),
    mi_split(b, W.max_inpos(f, m)),
    Equal.trans(Nat, Nat.max(W.max_inpos(f, m), W.max_inpos(b, 0n)), Nat.max(Nat.max(m, W.max_inpos(f, 0n)), W.max_inpos(b, 0n)), W.max_inpos(f, W.max_inpos(b, m)),
      Equal.cong(Nat, Nat, y => Nat.max(y, W.max_inpos(b, 0n)), W.max_inpos(f, m), Nat.max(m, W.max_inpos(f, 0n)), mi_split(f, m)),
      Equal.trans(Nat, Nat.max(Nat.max(m, W.max_inpos(f, 0n)), W.max_inpos(b, 0n)), Nat.max(Nat.max(m, W.max_inpos(b, 0n)), W.max_inpos(f, 0n)), W.max_inpos(f, W.max_inpos(b, m)),
        max_swap(m, W.max_inpos(f, 0n), W.max_inpos(b, 0n)),
        Equal.trans(Nat, Nat.max(Nat.max(m, W.max_inpos(b, 0n)), W.max_inpos(f, 0n)), Nat.max(W.max_inpos(b, m), W.max_inpos(f, 0n)), W.max_inpos(f, W.max_inpos(b, m)),
          Equal.cong(Nat, Nat, y => Nat.max(y, W.max_inpos(f, 0n)), Nat.max(m, W.max_inpos(b, 0n)), W.max_inpos(b, m),
            Equal.sym(Nat, W.max_inpos(b, m), Nat.max(m, W.max_inpos(b, 0n)), mi_split(b, m))),
          Equal.sym(Nat, W.max_inpos(f, W.max_inpos(b, m)), Nat.max(W.max_inpos(b, m), W.max_inpos(f, 0n)), mi_split(f, W.max_inpos(b, m)))))))

# The buffered items (front, then back reversed): their max input POS.
law mi_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  for +m: Nat
  {W.max_inpos(NR.append_ck(f, NR.rev_ck(b, Nil{})), m) == W.max_inpos(f, W.max_inpos(b, m)) : Nat}

def mi_items(f, b, m):
  Equal.trans(Nat, W.max_inpos(NR.append_ck(f, NR.rev_ck(b, Nil{})), m), W.max_inpos(NR.rev_ck(b, Nil{}), W.max_inpos(f, m)), W.max_inpos(f, W.max_inpos(b, m)),
    mi_app(f, NR.rev_ck(b, Nil{}), m),
    Equal.trans(Nat, W.max_inpos(NR.rev_ck(b, Nil{}), W.max_inpos(f, m)), W.max_inpos(b, W.max_inpos(f, m)), W.max_inpos(f, W.max_inpos(b, m)),
      mi_rev(b, Nil{}, W.max_inpos(f, m)),
      mi_comm(b, f, m)))

# Keys (norm_par.bend's keys_ge, the run's keys_le)
# ================================================

law kg_app:
  for +f: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  for +l: Nat
  {W.keys_ge(NR.append_ck(f, y), l) == Bool.and(W.keys_ge(f, l), W.keys_ge(y, l)) : Bool}

def kg_app(f, y, l):
  match f:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, W.keys_ge(NR.append_ck(t, y), l), Bool.and(W.keys_ge(t, l), W.keys_ge(y, l)), kg_app(t, y, l)) : {Bool.and(Nat.is_le(l, NR.Ck.key(x)), _) == Bool.and(Bool.and(Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(t, l)), W.keys_ge(y, l)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(t, l)), W.keys_ge(y, l)), Bool.and(Nat.is_le(l, NR.Ck.key(x)), Bool.and(W.keys_ge(t, l), W.keys_ge(y, l))), and_assoc(Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(t, l), W.keys_ge(y, l)))

law kg_rev:
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  for +l: Nat
  {W.keys_ge(NR.rev_ck(b, acc), l) == Bool.and(W.keys_ge(b, l), W.keys_ge(acc, l)) : Bool}

def kg_rev(b, acc, l):
  match b:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, W.keys_ge(NR.rev_ck(t, Con{x, acc}), l), Bool.and(W.keys_ge(t, l), Bool.and(Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(acc, l))), Bool.and(Bool.and(Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(t, l)), W.keys_ge(acc, l)),
        kg_rev(t, Con{x, acc}, l),
        and3_swap(W.keys_ge(t, l), Nat.is_le(l, NR.Ck.key(x)), W.keys_ge(acc, l)))

law kg_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  for +l: Nat
  {W.keys_ge(NR.append_ck(f, NR.rev_ck(b, Nil{})), l) == Bool.and(W.keys_ge(f, l), W.keys_ge(b, l)) : Bool}

def kg_items(f, b, l):
  Equal.trans(Bool, W.keys_ge(NR.append_ck(f, NR.rev_ck(b, Nil{})), l), Bool.and(W.keys_ge(f, l), W.keys_ge(NR.rev_ck(b, Nil{}), l)), Bool.and(W.keys_ge(f, l), W.keys_ge(b, l)),
    kg_app(f, NR.rev_ck(b, Nil{}), l),
    Equal.cong(Bool, Bool, y => Bool.and(W.keys_ge(f, l), y), W.keys_ge(NR.rev_ck(b, Nil{}), l), W.keys_ge(b, l),
      Equal.trans(Bool, W.keys_ge(NR.rev_ck(b, Nil{}), l), Bool.and(W.keys_ge(b, l), True{}), W.keys_ge(b, l),
        kg_rev(b, Nil{}, l), N.and_true_r_id(W.keys_ge(b, l)))))

law kl_app:
  for +f: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  for +k: Nat
  for +hf: {RD.keys_le(f, k) == True{} : Bool}
  for +hy: {RD.keys_le(y, k) == True{} : Bool}
  {RD.keys_le(NR.append_ck(f, y), k) == True{} : Bool}

def kl_app(f, y, k, hf, hy):
  match f:
    case Nil{}:
      hy
    case Con{+x, +t}:
      and_mk(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(NR.append_ck(t, y), k), N.and_true_l(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), hf), kl_app(t, y, k, N.and_true_r(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), hf), hy))

law kl_rev:
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  for +k: Nat
  for +hb: {RD.keys_le(b, k) == True{} : Bool}
  for +ha: {RD.keys_le(acc, k) == True{} : Bool}
  {RD.keys_le(NR.rev_ck(b, acc), k) == True{} : Bool}

def kl_rev(b, acc, k, hb, ha):
  match b:
    case Nil{}:
      ha
    case Con{+x, +t}:
      kl_rev(t, Con{x, acc}, k, N.and_true_r(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), hb), and_mk(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(acc, k), N.and_true_l(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), hb), ha))

law kl_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  for +k: Nat
  for +hf: {RD.keys_le(f, k) == True{} : Bool}
  for +hb: {RD.keys_le(b, k) == True{} : Bool}
  {RD.keys_le(NR.append_ck(f, NR.rev_ck(b, Nil{})), k) == True{} : Bool}

def kl_items(f, b, k, hf, hb):
  kl_app(f, NR.rev_ck(b, Nil{}), k, hf, kl_rev(b, Nil{}, k, hb, {==}))

# The buffer empty
# ================

law nil_rev:
  for +r: List<&2, NR.Ck>
  for +x: NR.Ck
  for +acc: List<&2, NR.Ck>
  {RD.is_nil(NR.rev_ck(r, Con{x, acc})) == False{} : Bool}

def nil_rev(r, x, acc):
  match r:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      nil_rev(t, y, Con{x, acc})

law nil_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  {RD.is_nil(NR.append_ck(f, NR.rev_ck(b, Nil{}))) == Nat.is_eq(Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), 0n) : Bool}

def nil_items(f, b):
  match f:
    case Con{+x, +t}:
      {==}
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          nil_rev(t, y, Nil{})

# First and last of the buffer
# ============================

law first_app:
  for +f: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  {W.first_ck(NR.append_ck(f, y)) == Maybe.or(&2, NR.Ck, W.first_ck(f), W.first_ck(y)) : Maybe<&2, NR.Ck>}

def first_app(f, y):
  match f:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

law first_rev:
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  {W.first_ck(NR.rev_ck(b, acc)) == Maybe.or(&2, NR.Ck, W.last_ck(b), W.first_ck(acc)) : Maybe<&2, NR.Ck>}

def first_rev(b, acc):
  match b:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Maybe<&2, NR.Ck>, W.first_ck(NR.rev_ck(t, Con{x, acc})), Maybe.or(&2, NR.Ck, W.last_ck(t), Some{x}), Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, W.last_ck(t), Some{x}), W.first_ck(acc)),
        first_rev(t, Con{x, acc}),
        Equal.sym(Maybe<&2, NR.Ck>, Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, W.last_ck(t), Some{x}), W.first_ck(acc)), Maybe.or(&2, NR.Ck, W.last_ck(t), Some{x}), or_some(W.last_ck(t), x, W.first_ck(acc))))

law first_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  {W.first_ck(NR.append_ck(f, NR.rev_ck(b, Nil{}))) == W.buf_first(f, b) : Maybe<&2, NR.Ck>}

def first_items(f, b):
  Equal.trans(Maybe<&2, NR.Ck>, W.first_ck(NR.append_ck(f, NR.rev_ck(b, Nil{}))), Maybe.or(&2, NR.Ck, W.first_ck(f), W.first_ck(NR.rev_ck(b, Nil{}))), W.buf_first(f, b),
    first_app(f, NR.rev_ck(b, Nil{})),
    Equal.cong(Maybe<&2, NR.Ck>, Maybe<&2, NR.Ck>, z => Maybe.or(&2, NR.Ck, W.first_ck(f), z), W.first_ck(NR.rev_ck(b, Nil{})), W.last_ck(b),
      Equal.trans(Maybe<&2, NR.Ck>, W.first_ck(NR.rev_ck(b, Nil{})), Maybe.or(&2, NR.Ck, W.last_ck(b), None{}), W.last_ck(b),
        first_rev(b, Nil{}), or_none(W.last_ck(b)))))

law last_app:
  for +f: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  {W.last_ck(NR.append_ck(f, y)) == Maybe.or(&2, NR.Ck, W.last_ck(y), W.last_ck(f)) : Maybe<&2, NR.Ck>}

def last_app(f, y):
  match f:
    case Nil{}:
      Equal.sym(Maybe<&2, NR.Ck>, Maybe.or(&2, NR.Ck, W.last_ck(y), None{}), W.last_ck(y), or_none(W.last_ck(y)))
    case Con{+x, +t}:
      Equal.trans(Maybe<&2, NR.Ck>, Maybe.or(&2, NR.Ck, W.last_ck(NR.append_ck(t, y)), Some{x}), Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, W.last_ck(y), W.last_ck(t)), Some{x}), Maybe.or(&2, NR.Ck, W.last_ck(y), Maybe.or(&2, NR.Ck, W.last_ck(t), Some{x})),
        Equal.cong(Maybe<&2, NR.Ck>, Maybe<&2, NR.Ck>, z => Maybe.or(&2, NR.Ck, z, Some{x}), W.last_ck(NR.append_ck(t, y)), Maybe.or(&2, NR.Ck, W.last_ck(y), W.last_ck(t)), last_app(t, y)),
        or_assoc(W.last_ck(y), W.last_ck(t), Some{x}))

law last_rev:
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  {W.last_ck(NR.rev_ck(b, acc)) == Maybe.or(&2, NR.Ck, W.last_ck(acc), W.first_ck(b)) : Maybe<&2, NR.Ck>}

def last_rev(b, acc):
  match b:
    case Nil{}:
      Equal.sym(Maybe<&2, NR.Ck>, Maybe.or(&2, NR.Ck, W.last_ck(acc), None{}), W.last_ck(acc), or_none(W.last_ck(acc)))
    case Con{+x, +t}:
      Equal.trans(Maybe<&2, NR.Ck>, W.last_ck(NR.rev_ck(t, Con{x, acc})), Maybe.or(&2, NR.Ck, Maybe.or(&2, NR.Ck, W.last_ck(acc), Some{x}), W.first_ck(t)), Maybe.or(&2, NR.Ck, W.last_ck(acc), Some{x}),
        last_rev(t, Con{x, acc}),
        or_some(W.last_ck(acc), x, W.first_ck(t)))

law last_items:
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  {W.last_ck(NR.append_ck(f, NR.rev_ck(b, Nil{}))) == W.buf_last(f, b) : Maybe<&2, NR.Ck>}

def last_items(f, b):
  Equal.trans(Maybe<&2, NR.Ck>, W.last_ck(NR.append_ck(f, NR.rev_ck(b, Nil{}))), Maybe.or(&2, NR.Ck, W.last_ck(NR.rev_ck(b, Nil{})), W.last_ck(f)), W.buf_last(f, b),
    last_app(f, NR.rev_ck(b, Nil{})),
    Equal.cong(Maybe<&2, NR.Ck>, Maybe<&2, NR.Ck>, z => Maybe.or(&2, NR.Ck, z, W.last_ck(f)), W.last_ck(NR.rev_ck(b, Nil{})), W.first_ck(b), last_rev(b, Nil{})))

# Line numbers moved on
# =====================

law shift_app:
  for +d: Nat
  for +x: List<&2, NR.Ck>
  for +y: List<&2, NR.Ck>
  {W.cks_shift(d, NR.append_ck(x, y)) == NR.append_ck(W.cks_shift(d, x), W.cks_shift(d, y)) : List<&2, NR.Ck>}

def shift_app(d, x, y):
  match x:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %shift_app(d, t, y) : {Con{W.ck_shift(d, c), W.cks_shift(d, NR.append_ck(t, y))} == Con{W.ck_shift(d, c), _} : List<&2, NR.Ck>}
      {==}

law shift_rev:
  for +d: Nat
  for +b: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  {NR.rev_ck(W.cks_shift(d, b), W.cks_shift(d, acc)) == W.cks_shift(d, NR.rev_ck(b, acc)) : List<&2, NR.Ck>}

def shift_rev(d, b, acc):
  match b:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      shift_rev(d, t, Con{c, acc})

law shift_items:
  for +d: Nat
  for +f: List<&2, NR.Ck>
  for +b: List<&2, NR.Ck>
  {NR.append_ck(W.cks_shift(d, f), NR.rev_ck(W.cks_shift(d, b), Nil{})) == W.cks_shift(d, NR.append_ck(f, NR.rev_ck(b, Nil{}))) : List<&2, NR.Ck>}

def shift_items(d, f, b):
  Equal.trans(List<&2, NR.Ck>, NR.append_ck(W.cks_shift(d, f), NR.rev_ck(W.cks_shift(d, b), Nil{})), NR.append_ck(W.cks_shift(d, f), W.cks_shift(d, NR.rev_ck(b, Nil{}))), W.cks_shift(d, NR.append_ck(f, NR.rev_ck(b, Nil{}))),
    Equal.cong(List<&2, NR.Ck>, List<&2, NR.Ck>, z => NR.append_ck(W.cks_shift(d, f), z), NR.rev_ck(W.cks_shift(d, b), Nil{}), W.cks_shift(d, NR.rev_ck(b, Nil{})), shift_rev(d, b, Nil{})),
    Equal.sym(List<&2, NR.Ck>, W.cks_shift(d, NR.append_ck(f, NR.rev_ck(b, Nil{}))), NR.append_ck(W.cks_shift(d, f), W.cks_shift(d, NR.rev_ck(b, Nil{}))), shift_app(d, f, NR.rev_ck(b, Nil{}))))

law lens_shift:
  for +d: Nat
  for +xs: List<&2, NR.Ck>
  {RD.lens(W.cks_shift(d, xs)) == RD.lens(xs) : Nat}

def lens_shift(d, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      match c:
        case NR.Ck{+k, +ip, +ln, +p, +n}:
          %lens_shift(d, t) : {Nat.add(U32.to_nat(n), RD.lens(W.cks_shift(d, t))) == Nat.add(U32.to_nat(n), _) : Nat}
          {==}

law len_shift:
  for +d: Nat
  for +xs: List<&2, NR.Ck>
  {List.length(&2, NR.Ck, W.cks_shift(d, xs)) == List.length(&2, NR.Ck, xs) : Nat}

def len_shift(d, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %len_shift(d, t) : {1n+List.length(&2, NR.Ck, W.cks_shift(d, t)) == 1n+_ : Nat}
      {==}

law kl_shift:
  for +d: Nat
  for +xs: List<&2, NR.Ck>
  for +k: Nat
  {RD.keys_le(W.cks_shift(d, xs), k) == RD.keys_le(xs, k) : Bool}

def kl_shift(d, xs, k):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          %kl_shift(d, t, k) : {Bool.and(Nat.is_le(kk, k), RD.keys_le(W.cks_shift(d, t), k)) == Bool.and(Nat.is_le(kk, k), _) : Bool}
          {==}

