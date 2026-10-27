import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_text.bend as X
import ./proof_run_dec.bend as D
import ./proof_run_rec.bend as C
import ./tan.bend as Tan
import ./proof_var.bend as PV

# A normalized line, rebuilt, is judged again: normalized, same POS, same
# text, same CHROM (for twice_run).

def slen(xs: List<&2, String>) -> Nat:
  List.length(&2, String, xs)

def J(+y: List<&2, List<&2, B.Base>>) -> String:
  String.join(B.Alleles.show(y), ",")

# The fields of a rebuilt record.
def fsA(+fs: List<&2, String>, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>, +info2: String) -> List<&2, String>:
  B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(fs, 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y)), 7n, info2)

law ge8:
  for +n: Nat
  for +h: {Nat.is_lt(n, 8n) == False{} : Bool}
  {n == 8n+Nat.sub(n, 8n) : Nat}

def ge8(n, h):
  match n:
    case 0n:
      Empty.absurd({0n == 8n+Nat.sub(0n, 8n) : Nat}, P.true_ne_false(h))
    case 1n:
      Empty.absurd({1n == 8n+Nat.sub(1n, 8n) : Nat}, P.true_ne_false(h))
    case 2n:
      Empty.absurd({2n == 8n+Nat.sub(2n, 8n) : Nat}, P.true_ne_false(h))
    case 3n:
      Empty.absurd({3n == 8n+Nat.sub(3n, 8n) : Nat}, P.true_ne_false(h))
    case 4n:
      Empty.absurd({4n == 8n+Nat.sub(4n, 8n) : Nat}, P.true_ne_false(h))
    case 5n:
      Empty.absurd({5n == 8n+Nat.sub(5n, 8n) : Nat}, P.true_ne_false(h))
    case 6n:
      Empty.absurd({6n == 8n+Nat.sub(6n, 8n) : Nat}, P.true_ne_false(h))
    case 7n:
      Empty.absurd({7n == 8n+Nat.sub(7n, 8n) : Nat}, P.true_ne_false(h))
    case 8n+k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, P.sub_zero(k)) : {8n+k == 8n+_ : Nat}
      {==}

def LEN(+fs: List<&2, String>, +k: Nat) -> Type:
  {slen(fs) == 8n+k : Nat}

law fa_len:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  {slen(fsA(fs, q, s, y, i2)) == slen(fs) : Nat}

def fa_len(fs, q, s, y, i2):
  +a = B.Rec.put(fs, 1n, Nat.show(q))
  +b = B.Rec.put(a, 3n, B.Allele.show(s))
  +c = B.Rec.put(b, 4n, J(y))
  Equal.trans(Nat, slen(B.Rec.put(c, 7n, i2)), slen(c), slen(fs), C.len_put(c, 7n, i2),
    Equal.trans(Nat, slen(c), slen(b), slen(fs), C.len_put(b, 4n, J(y)),
      Equal.trans(Nat, slen(b), slen(a), slen(fs), C.len_put(a, 3n, B.Allele.show(s)), C.len_put(fs, 1n, Nat.show(q)))))

law fa_f0:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  {B.Rec.field(fsA(fs, q, s, y, i2), 0n) == B.Rec.field(fs, 0n) : String}

def fa_f0(fs, q, s, y, i2):
  +a = B.Rec.put(fs, 1n, Nat.show(q))
  +b = B.Rec.put(a, 3n, B.Allele.show(s))
  +c = B.Rec.put(b, 4n, J(y))
  Equal.trans(String, B.Rec.field(B.Rec.put(c, 7n, i2), 0n), B.Rec.field(c, 0n), B.Rec.field(fs, 0n), C.field_put_ne(c, 7n, 0n, i2, {==}),
    Equal.trans(String, B.Rec.field(c, 0n), B.Rec.field(b, 0n), B.Rec.field(fs, 0n), C.field_put_ne(b, 4n, 0n, J(y), {==}),
      Equal.trans(String, B.Rec.field(b, 0n), B.Rec.field(a, 0n), B.Rec.field(fs, 0n), C.field_put_ne(a, 3n, 0n, B.Allele.show(s), {==}),
        C.field_put_ne(fs, 1n, 0n, Nat.show(q), {==}))))

def lt_of(+i: Nat, +fs: List<&2, String>, +k: Nat, +hl: {slen(fs) == 8n+k : Nat}, +hi: {Nat.is_lt(i, 8n+k) == True{} : Bool}) ->
  {Nat.is_lt(i, slen(fs)) == True{} : Bool}:
  %Equal.sym(Nat, slen(fs), 8n+k, hl) : {Nat.is_lt(i, _) == True{} : Bool}
  hi

def F3(+fs: List<&2, String>, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>) -> List<&2, String>:
  B.Rec.put(B.Rec.put(B.Rec.put(fs, 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y))

def F2(+fs: List<&2, String>, +q: Nat, +s: List<&2, B.Base>) -> List<&2, String>:
  B.Rec.put(B.Rec.put(fs, 1n, Nat.show(q)), 3n, B.Allele.show(s))

def F1(+fs: List<&2, String>, +q: Nat) -> List<&2, String>:
  B.Rec.put(fs, 1n, Nat.show(q))

law l1:
  for +fs: List<&2, String>
  for +q: Nat
  {slen(F1(fs, q)) == slen(fs) : Nat}

def l1(fs, q):
  C.len_put(fs, 1n, Nat.show(q))

law l2:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  {slen(F2(fs, q, s)) == slen(fs) : Nat}

def l2(fs, q, s):
  Equal.trans(Nat, slen(F2(fs, q, s)), slen(F1(fs, q)), slen(fs), C.len_put(F1(fs, q), 3n, B.Allele.show(s)), l1(fs, q))

law l3:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  {slen(F3(fs, q, s, y)) == slen(fs) : Nat}

def l3(fs, q, s, y):
  Equal.trans(Nat, slen(F3(fs, q, s, y)), slen(F2(fs, q, s)), slen(fs), C.len_put(F2(fs, q, s), 4n, J(y)), l2(fs, q, s))

def lt_in(+i: Nat, +xs: List<&2, String>, +fs: List<&2, String>, +k: Nat, +e: {slen(xs) == slen(fs) : Nat},
  +hl: {slen(fs) == 8n+k : Nat}, +hi: {Nat.is_lt(i, 8n+k) == True{} : Bool}) -> {Nat.is_lt(i, slen(xs)) == True{} : Bool}:
  lt_of(i, xs, k, Equal.trans(Nat, slen(xs), slen(fs), 8n+k, e, hl), hi)

law fa_f1:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  {B.Rec.field(fsA(fs, q, s, y, i2), 1n) == Nat.show(q) : String}

def fa_f1(fs, q, s, y, i2, k, hl):
  +a = F1(fs, q)
  +b = F2(fs, q, s)
  +c = F3(fs, q, s, y)
  Equal.trans(String, B.Rec.field(B.Rec.put(c, 7n, i2), 1n), B.Rec.field(c, 1n), Nat.show(q), C.field_put_ne(c, 7n, 1n, i2, {==}),
    Equal.trans(String, B.Rec.field(c, 1n), B.Rec.field(b, 1n), Nat.show(q), C.field_put_ne(b, 4n, 1n, J(y), {==}),
      Equal.trans(String, B.Rec.field(b, 1n), B.Rec.field(a, 1n), Nat.show(q), C.field_put_ne(a, 3n, 1n, B.Allele.show(s), {==}),
        C.field_put_eq(fs, 1n, Nat.show(q), lt_of(1n, fs, k, hl, {==})))))

law fa_f3:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  {B.Rec.field(fsA(fs, q, s, y, i2), 3n) == B.Allele.show(s) : String}

def fa_f3(fs, q, s, y, i2, k, hl):
  +a = F1(fs, q)
  +b = F2(fs, q, s)
  +c = F3(fs, q, s, y)
  Equal.trans(String, B.Rec.field(B.Rec.put(c, 7n, i2), 3n), B.Rec.field(c, 3n), B.Allele.show(s), C.field_put_ne(c, 7n, 3n, i2, {==}),
    Equal.trans(String, B.Rec.field(c, 3n), B.Rec.field(b, 3n), B.Allele.show(s), C.field_put_ne(b, 4n, 3n, J(y), {==}),
      C.field_put_eq(a, 3n, B.Allele.show(s), lt_in(3n, a, fs, k, l1(fs, q), hl, {==}))))

law fa_f4:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  {B.Rec.field(fsA(fs, q, s, y, i2), 4n) == J(y) : String}

def fa_f4(fs, q, s, y, i2, k, hl):
  +b = F2(fs, q, s)
  +c = F3(fs, q, s, y)
  Equal.trans(String, B.Rec.field(B.Rec.put(c, 7n, i2), 4n), B.Rec.field(c, 4n), J(y), C.field_put_ne(c, 7n, 4n, i2, {==}),
    C.field_put_eq(b, 4n, J(y), lt_in(4n, b, fs, k, l2(fs, q, s), hl, {==})))

law fa_f7:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  {B.Rec.field(fsA(fs, q, s, y, i2), 7n) == i2 : String}

def fa_f7(fs, q, s, y, i2, k, hl):
  +c = F3(fs, q, s, y)
  C.field_put_eq(c, 7n, i2, lt_in(7n, c, fs, k, l3(fs, q, s, y), hl, {==}))

# Putting the same values again changes nothing.
law fa_same:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  {B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(fsA(fs, q, s, y, i2), 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y)), 7n,
    B.Rec.field(fsA(fs, q, s, y, i2), 7n)) == fsA(fs, q, s, y, i2) : List<&2, String>}

def fa_same(fs, q, s, y, i2, k, hl):
  +F = fsA(fs, q, s, y, i2)
  %Equal.sym(List<&2, String>, B.Rec.put(F, 1n, Nat.show(q)), F, C.put_same(F, 1n, Nat.show(q), fa_f1(fs, q, s, y, i2, k, hl))) :
    {B.Rec.put(B.Rec.put(B.Rec.put(_, 3n, B.Allele.show(s)), 4n, J(y)), 7n, B.Rec.field(F, 7n)) == F : List<&2, String>}
  %Equal.sym(List<&2, String>, B.Rec.put(F, 3n, B.Allele.show(s)), F, C.put_same(F, 3n, B.Allele.show(s), fa_f3(fs, q, s, y, i2, k, hl))) :
    {B.Rec.put(B.Rec.put(_, 4n, J(y)), 7n, B.Rec.field(F, 7n)) == F : List<&2, String>}
  %Equal.sym(List<&2, String>, B.Rec.put(F, 4n, J(y)), F, C.put_same(F, 4n, J(y), fa_f4(fs, q, s, y, i2, k, hl))) :
    {B.Rec.put(_, 7n, B.Rec.field(F, 7n)) == F : List<&2, String>}
  C.put_same(F, 7n, B.Rec.field(F, 7n), {==})

law fa_noc:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +c: Char
  for +h0: {X.all_noc(fs, c) == True{} : Bool}
  for +h1: {X.no_c(Nat.show(q), c) == True{} : Bool}
  for +h3: {X.no_c(B.Allele.show(s), c) == True{} : Bool}
  for +h4: {X.no_c(J(y), c) == True{} : Bool}
  for +h7: {X.no_c(i2, c) == True{} : Bool}
  {X.all_noc(fsA(fs, q, s, y, i2), c) == True{} : Bool}

def fa_noc(fs, q, s, y, i2, c, h0, h1, h3, h4, h7):
  C.noc_put(F3(fs, q, s, y), 7n, i2, c,
    C.noc_put(F2(fs, q, s), 4n, J(y), c,
      C.noc_put(F1(fs, q), 3n, B.Allele.show(s), c,
        C.noc_put(fs, 1n, Nat.show(q), c, h0, h1), h3), h4), h7)

def eqn(+i: Nat, +xs: List<&2, String>, +fs: List<&2, String>, +k: Nat, +e: {slen(xs) == slen(fs) : Nat},
  +hl: {slen(fs) == 8n+k : Nat}, +b: Bool, +hv: {Nat.is_eq(i, 8n+k) == b : Bool}) -> {Nat.is_eq(i, slen(xs)) == b : Bool}:
  %Equal.sym(Nat, slen(xs), 8n+k, Equal.trans(Nat, slen(xs), slen(fs), 8n+k, e, hl)) : {Nat.is_eq(i, _) == b : Bool}
  hv

def fa_ecr(+fs: List<&2, String>, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>, +i2: String, k: Nat,
  +hl: {slen(fs) == 8n+k : Nat},
  hi: {C.ecr(i2) == True{} : Bool} -> {C.ecr(B.Rec.field(fs, 7n)) == True{} : Bool},
  e: {C.ecr(C.last(fsA(fs, q, s, y, i2))) == True{} : Bool}) -> {C.ecr(C.last(fs)) == True{} : Bool}:
  match k:
    case 0n:
      +c3 = F3(fs, q, s, y)
      +el = C.last_put_eq(c3, 7n, i2, eqn(8n, c3, fs, 0n, l3(fs, q, s, y), hl, True{}, {==}))
      +ef = C.last_field(fs, 7n, eqn(8n, fs, fs, 0n, {==}, hl, True{}, {==}))
      %Equal.sym(String, C.last(fs), B.Rec.field(fs, 7n), ef) : {C.ecr(_) == True{} : Bool}
      hi((%el : {C.ecr(_) == True{} : Bool}; e))
    case 1n+(+j):
      +k = {1n+j : Nat}
      +a = F1(fs, q)
      +b = F2(fs, q, s)
      +c = F3(fs, q, s, y)
      +e1 = C.last_put_ne(c, 7n, i2, eqn(8n, c, fs, k, l3(fs, q, s, y), hl, False{}, {==}))
      +e2 = C.last_put_ne(b, 4n, J(y), eqn(5n, b, fs, k, l2(fs, q, s), hl, False{}, {==}))
      +e3 = C.last_put_ne(a, 3n, B.Allele.show(s), eqn(4n, a, fs, k, l1(fs, q), hl, False{}, {==}))
      +e4 = C.last_put_ne(fs, 1n, Nat.show(q), eqn(2n, fs, fs, k, {==}, hl, False{}, {==}))
      %Equal.trans(String, C.last(fsA(fs, q, s, y, i2)), C.last(c), C.last(fs), e1,
          Equal.trans(String, C.last(c), C.last(b), C.last(fs), e2, Equal.trans(String, C.last(b), C.last(a), C.last(fs), e3, e4))) :
        {C.ecr(_) == True{} : Bool}
      e

law ecr_join2:
  for +xs: List<&2, String>
  for +c: Char
  for +hc: {Char.is_eq(c, '\r') == False{} : Bool}
  {C.ecr(String.join(xs, SCon{c, SNil{}})) == C.ecr(C.last(xs)) : Bool}

def ecr_join2(xs, c, hc):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      C.ecr_join(t, h, c, hc)

def good_re.nc(+b2: String, +body: String, x: Bool, +ex: {C.ecr(b2) == x : Bool}, +h2: {C.ecr(body) == False{} : Bool},
  imp: {C.ecr(b2) == True{} : Bool} -> {C.ecr(body) == True{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, C.ecr(body), False{}, Equal.sym(Bool, C.ecr(body), True{}, imp(ex)), h2)))

def good_re.go(+b2: String, +body: String, +t: String, x: Bool, +ex: {String.eq(t, "\r\n") == x : Bool},
  +hr: {Bool.or(x, Bool.and(String.eq(t, "\n"), Bool.not(C.ecr(body)))) == True{} : Bool},
  imp: {C.ecr(b2) == True{} : Bool} -> {C.ecr(body) == True{} : Bool}) ->
  {Bool.or(x, Bool.and(String.eq(t, "\n"), Bool.not(C.ecr(b2)))) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      +h1 = P.and_true_l(String.eq(t, "\n"), Bool.not(C.ecr(body)), hr)
      +h2 = P.not_true(C.ecr(body), P.and_true_r(String.eq(t, "\n"), Bool.not(C.ecr(body)), hr))
      S.and_intro(String.eq(t, "\n"), Bool.not(C.ecr(b2)), h1, good_re.nc(b2, body, C.ecr(b2), {==}, h2, imp))

# The rebuilt line is good when the line was.
law good_re:
  for +body: String
  for +t: String
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +ef: {String.split(body, '\t') == fs : List<&2, String>}
  for +hl: {slen(fs) == 8n+k : Nat}
  for +hg: {X.goodb(B.Line{body, t}) == True{} : Bool}
  for +hnl: {X.all_noc(fsA(fs, q, s, y, i2), '\n') == True{} : Bool}
  for hi: {C.ecr(i2) == True{} : Bool} -> {C.ecr(B.Rec.field(fs, 7n)) == True{} : Bool}
  {X.goodb(B.Line{String.join(fsA(fs, q, s, y, i2), "\t"), t}) == True{} : Bool}

def good_re(body, t, fs, q, s, y, i2, k, ef, hl, hg, hnl, hi):
  +F = fsA(fs, q, s, y, i2)
  +b2 = String.join(F, "\t")
  +R = Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), Bool.not(C.ecr(body))))
  imp = {(eb => (%C.join_split(body, '\t') : {C.ecr(_) == True{} : Bool};
      %Equal.sym(List<&2, String>, String.split(body, '\t'), fs, ef) : {C.ecr(String.join(_, "\t")) == True{} : Bool};
      %Equal.sym(Bool, C.ecr(String.join(fs, "\t")), C.ecr(C.last(fs)), ecr_join2(fs, '\t', {==})) : {_ == True{} : Bool};
      fa_ecr(fs, q, s, y, i2, k, hl, hi, (%ecr_join2(F, '\t', {==}) : {_ == True{} : Bool}; eb)))) :
    {C.ecr(b2) == True{} : Bool} -> {C.ecr(body) == True{} : Bool}}
  S.and_intro(X.no_c(b2, '\n'), Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), Bool.not(C.ecr(b2)))),
    C.join_noc2(F, "\t", '\n', hnl, {==}),
    good_re.go(b2, body, t, String.eq(t, "\r\n"), {==}, P.and_true_r(X.no_c(body, '\n'), R, hg), imp))

law shows_ne:
  for +y: List<&2, List<&2, B.Base>>
  for +h: {L.all_nonempty(y) == True{} : Bool}
  {B.Text.any_empty(B.Alleles.show(y)) == False{} : Bool}

def shows_ne(y, h):
  match y:
    case Nil{}:
      {==}
    case Nil{} <> +t:
      Empty.absurd({B.Text.any_empty(B.Alleles.show(Nil{} <> t)) == False{} : Bool}, P.false_ne_true(P.and_true_l(Nat.is_le(1n, 0n), L.all_nonempty(t), h)))
    case (+b <> +r) <> +t:
      shows_ne(t, P.and_true_r(Nat.is_le(1n, L.len(b <> r)), L.all_nonempty(t), h))

law shows_letters:
  for +y: List<&2, List<&2, B.Base>>
  for +h: {L.all_nonempty(y) == True{} : Bool}
  {B.Text.any_not_letters(B.Alleles.show(y)) == False{} : Bool}

def shows_letters(y, h):
  match y:
    case Nil{}:
      {==}
    case +x <> +t:
      +hx = P.and_true_l(Nat.is_le(1n, L.len(x)), L.all_nonempty(t), h)
      %Equal.sym(Bool, B.Text.is_letters(B.Allele.show(x)), True{}, C.show_letters(x, hx)) :
        {Bool.or(Bool.not(_), B.Text.any_not_letters(B.Alleles.show(t))) == False{} : Bool}
      shows_letters(t, P.and_true_r(Nat.is_le(1n, L.len(x)), L.all_nonempty(t), h))

law or5:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for +e: Bool
  for +ha: {a == False{} : Bool}
  for +hb: {b == False{} : Bool}
  for +hc: {c == False{} : Bool}
  for +hd: {d == False{} : Bool}
  for +he: {e == False{} : Bool}
  {Bool.or(Bool.or(Bool.or(Bool.or(a, b), c), d), e) == False{} : Bool}

def or5(a, b, c, d, e, ha, hb, hc, hd, he):
  S.or_false_intro(Bool.or(Bool.or(Bool.or(a, b), c), d), e,
    S.or_false_intro(Bool.or(Bool.or(a, b), c), d, S.or_false_intro(Bool.or(a, b), c, S.or_false_intro(a, b, ha, hb), hc), hd), he)

def alts_rt.go(y: List<&2, List<&2, B.Base>>, +h: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, y)) == True{} : Bool}) ->
  {String.split(J(y), ',') == B.Alleles.show(y) : List<&2, String>}:
  match y:
    case Nil{}:
      Empty.absurd({String.split(J(Nil{}), ',') == Nil{} : List<&2, String>}, P.false_ne_true(h))
    case +x <> +t:
      C.split_join(B.Alleles.show(t), B.Allele.show(x), ',', C.show_noc(x, ',', {==}), C.shows_noc(t, ',', {==}))

def fields_rt(xs: List<&2, String>, +c: Char, +hx: {X.all_noc(xs, c) == True{} : Bool}, ne: {xs == Nil{} : List<&2, String>} -> Empty) ->
  {String.split(String.join(xs, SCon{c, SNil{}}), c) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      Empty.absurd({String.split(String.join(Nil{}, SCon{c, SNil{}}), c) == Nil{} : List<&2, String>}, ne({==}))
    case +h <> +t:
      C.split_join(t, h, c, P.and_true_l(X.no_c(h, c), X.all_noc(t, c), hx), P.and_true_r(X.no_c(h, c), X.all_noc(t, c), hx))

def len_ne(+xs: List<&2, String>, +k: Nat, +hl: {slen(xs) == 8n+k : Nat}, e: {xs == Nil{} : List<&2, String>}) -> Empty:
  P.succ_ne_zero(7n+k, Equal.trans(Nat, 8n+k, slen(xs), 0n, Equal.sym(Nat, slen(xs), 8n+k, hl),
    Equal.cong(List<&2, String>, Nat, z => slen(z), xs, Nil{}, e)))

def RES(+q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>, +F: List<&2, String>) -> B.Res:
  B.Res{B.Normalized{}, q, String.join(F, "\t"), B.Rec.stale(F, B.Var{q, s, y}, B.Var{q, s, y})}

# A rebuilt normalized record is judged normalized again, as itself.
law rejudge:
  for +fa: List<&2, B.Contig>
  for +fs: List<&2, String>
  for +raw: String
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  for +hf0: {String.is_empty(B.Rec.field(fs, 0n)) == False{} : Bool}
  for +hfind: {B.Fasta.find(fa, B.Rec.field(fs, 0n)) == Some{raw} : Maybe<&2, String>}
  for +htab: {X.all_noc(fs, '\t') == True{} : Bool}
  for +hi2: {X.no_c(i2, '\t') == True{} : Bool}
  for +hend: {B.Info.end_ok(i2, Nat.sub(Nat.add(q, L.len(s)), 1n)) == True{} : Bool}
  for +hv: {L.valid(B.Bases.of_fasta(raw), B.Var{q, s, y}) == True{} : Bool}
  for +htw: {Tan.normal(B.Bases.of_fasta(raw), B.Var{q, s, y}) == B.Var{q, s, y} : B.Var}
  {L.judge(fa, String.join(fsA(fs, q, s, y, i2), "\t")) == RES(q, s, y, fsA(fs, q, s, y, i2)) : B.Res}

def rejudge(fa, fs, raw, q, s, y, i2, k, hl, hf0, hfind, htab, hi2, hend, hv, htw):
  +seq = B.Bases.of_fasta(raw)
  +W = {B.Var{q, s, y} : B.Var}
  +F = fsA(fs, q, s, y, i2)
  +b2 = String.join(F, "\t")
  +R = RES(q, s, y, F)
  +hlF = Equal.trans(Nat, slen(F), slen(fs), 8n+k, fa_len(fs, q, s, y, i2), hl)
  +h12 = C.valid_c12(seq, q, s, y, hv)
  +hs1 = P.and_true_r(C.c1(q), C.c2(s), h12)
  +hy1 = C.valid_c3(seq, q, s, y, hv)
  +hyn = C.valid_c4(seq, q, s, y, hv)
  +nq = C.digits_noc(Nat.show(q), '\t', D.show_digits(q), {==})
  +noc = fa_noc(fs, q, s, y, i2, '\t', htab, nq, C.show_noc(s, '\t', {==}),
    C.join_noc2(B.Alleles.show(y), ",", '\t', C.shows_noc(y, '\t', {==}), {==}), hi2)
  +sF = fields_rt(F, '\t', noc, e => len_ne(F, k, hlF, e))
  +f1 = fa_f1(fs, q, s, y, i2, k, hl)
  +f3 = fa_f3(fs, q, s, y, i2, k, hl)
  +f4 = fa_f4(fs, q, s, y, i2, k, hl)
  +f7 = fa_f7(fs, q, s, y, i2, k, hl)
  +aF = {(%Equal.sym(String, B.Rec.field(F, 4n), J(y), f4) : {String.split(_, ',') == B.Alleles.show(y) : List<&2, String>}; alts_rt.go(y, hy1)) : {B.Rec.alts(F) == B.Alleles.show(y) : List<&2, String>}}
  +pF = {(%Equal.sym(String, B.Rec.field(F, 1n), Nat.show(q), f1) : {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == q : Nat};
    %Equal.sym(Maybe<&2, Nat>, B.Pos.read(Nat.show(q)), Some{q}, D.show_read(q)) : {Maybe.default(&2, Nat, _, 0n) == q : Nat}; {==}) : {B.Rec.pos(F) == q : Nat}}
  +ef0 = fa_f0(fs, q, s, y, i2)
  +m1 = {(%Equal.sym(Nat, slen(F), 8n+k, hlF) : {Nat.is_lt(_, 8n) == False{} : Bool}; P.lt_zero(k)) : {Nat.is_lt(slen(F), 8n) == False{} : Bool}}
  +m2 = {(%Equal.sym(String, B.Rec.field(F, 0n), B.Rec.field(fs, 0n), ef0) : {String.is_empty(_) == False{} : Bool}; hf0) :
    {String.is_empty(B.Rec.field(F, 0n)) == False{} : Bool}}
  +m3 = {(%Equal.sym(String, B.Rec.field(F, 1n), Nat.show(q), f1) : {Maybe.is_none(&2, Nat, B.Pos.read(_)) == False{} : Bool};
    %Equal.sym(Maybe<&2, Nat>, B.Pos.read(Nat.show(q)), Some{q}, D.show_read(q)) : {Maybe.is_none(&2, Nat, _) == False{} : Bool}; {==}) :
    {Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(F, 1n))) == False{} : Bool}}
  +m4 = {(%Equal.sym(String, B.Rec.field(F, 3n), B.Allele.show(s), f3) : {Bool.not(B.Text.is_letters(_)) == False{} : Bool};
    %Equal.sym(Bool, B.Text.is_letters(B.Allele.show(s)), True{}, C.show_letters(s, hs1)) : {Bool.not(_) == False{} : Bool}; {==}) :
    {Bool.not(B.Text.is_letters(B.Rec.field(F, 3n))) == False{} : Bool}}
  +m5 = {(%Equal.sym(List<&2, String>, B.Rec.alts(F), B.Alleles.show(y), aF) : {B.Text.any_empty(_) == False{} : Bool}; shows_ne(y, hyn)) :
    {B.Text.any_empty(B.Rec.alts(F)) == False{} : Bool}}
  +mal = or5(Nat.is_lt(slen(F), 8n), String.is_empty(B.Rec.field(F, 0n)), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(F, 1n))),
    Bool.not(B.Text.is_letters(B.Rec.field(F, 3n))), B.Text.any_empty(B.Rec.alts(F)), m1, m2, m3, m4, m5)
  +oos = {(%Equal.sym(List<&2, String>, B.Rec.alts(F), B.Alleles.show(y), aF) : {B.Text.any_not_letters(_) == False{} : Bool}; shows_letters(y, hyn)) :
    {B.Rec.out_of_scope(F) == False{} : Bool}}
  +hE = {(%Equal.sym(String, B.Rec.field(F, 7n), i2, f7) : {B.Info.end_ok(_, Nat.sub(Nat.add(B.Rec.pos(F), String.length(B.Rec.field(F, 3n))), 1n)) == True{} : Bool};
    %Equal.sym(Nat, B.Rec.pos(F), q, pF) : {B.Info.end_ok(i2, Nat.sub(Nat.add(_, String.length(B.Rec.field(F, 3n))), 1n)) == True{} : Bool};
    %Equal.sym(String, B.Rec.field(F, 3n), B.Allele.show(s), f3) : {B.Info.end_ok(i2, Nat.sub(Nat.add(q, String.length(_)), 1n)) == True{} : Bool};
    %Equal.sym(Nat, String.length(B.Allele.show(s)), L.len(s), C.show_len(s)) : {B.Info.end_ok(i2, Nat.sub(Nat.add(q, _), 1n)) == True{} : Bool};
    hend) : {B.Info.end_ok(B.Rec.field(F, 7n), Nat.sub(Nat.add(B.Rec.pos(F), String.length(B.Rec.field(F, 3n))), 1n)) == True{} : Bool}}
  +hR = {(%Equal.sym(String, B.Rec.field(F, 3n), B.Allele.show(s), f3) : {B.Allele.read(_) == Some{s} : Maybe<&2, List<&2, B.Base>>}; C.allele_rt(s)) :
    {B.Allele.read(B.Rec.field(F, 3n)) == Some{s} : Maybe<&2, List<&2, B.Base>>}}
  +hA = {(%Equal.sym(List<&2, String>, B.Rec.alts(F), B.Alleles.show(y), aF) : {B.Alleles.read(_) == Some{y} : Maybe<&2, List<&2, List<&2, B.Base>>>}; C.alleles_rt(y)) :
    {B.Alleles.read(B.Rec.alts(F)) == Some{y} : Maybe<&2, List<&2, List<&2, B.Base>>>}}
  %Equal.sym(List<&2, String>, String.split(b2, '\t'), F, sF) :
    {L.judge.shape(B.Rec.malformed(_), B.Rec.out_of_scope(_), fa, _, b2) == R : B.Res}
  %Equal.sym(Bool, B.Rec.malformed(F), False{}, mal) : {L.judge.shape(_, B.Rec.out_of_scope(F), fa, F, b2) == R : B.Res}
  %Equal.sym(Bool, B.Rec.out_of_scope(F), False{}, oos) : {L.judge.shape(False{}, _, fa, F, b2) == R : B.Res}
  %Equal.sym(String, B.Rec.field(F, 0n), B.Rec.field(fs, 0n), ef0) : {L.judge.contig(B.Fasta.find(fa, _), F, b2) == R : B.Res}
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(fs, 0n)), Some{raw}, hfind) : {L.judge.contig(_, F, b2) == R : B.Res}
  %Equal.sym(Bool, B.Info.end_ok(B.Rec.field(F, 7n), Nat.sub(Nat.add(B.Rec.pos(F), String.length(B.Rec.field(F, 3n))), 1n)), True{}, hE) :
    {L.judge.bases(_, B.Allele.read(B.Rec.field(F, 3n)), B.Alleles.read(B.Rec.alts(F)), F, b2, seq) == R : B.Res}
  %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(B.Rec.field(F, 3n)), Some{s}, hR) :
    {L.judge.bases(True{}, _, B.Alleles.read(B.Rec.alts(F)), F, b2, seq) == R : B.Res}
  %Equal.sym(Maybe<&2, List<&2, List<&2, B.Base>>>, B.Alleles.read(B.Rec.alts(F)), Some{y}, hA) :
    {L.judge.bases(True{}, Some{s}, _, F, b2, seq) == R : B.Res}
  %Equal.sym(Nat, B.Rec.pos(F), q, pF) : {L.problem(L.checks(True{}, seq, B.Var{_, s, y}), F, b2, seq, B.Var{_, s, y}) == R : B.Res}
  %Equal.sym(Maybe<&2, B.Code>, L.checks(True{}, seq, W), None{}, C.checks_valid(seq, q, s, y, hv)) : {L.problem(_, F, b2, seq, W) == R : B.Res}
  %Equal.sym(B.Var, Tan.normal(seq, W), W, htw) : {B.Res{B.Normalized{}, L.pos_of(_), B.Rec.rebuild(F, W, _), B.Rec.stale(F, W, _)} == R : B.Res}
  %Equal.sym(Bool, Nat.is_eq(q, q), True{}, P.eq_refl(q)) :
    {B.Res{B.Normalized{}, q, String.join(B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(F, 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y)), 7n,
      B.Rec.info(Bool.not(Bool.and(_, Nat.is_eq(L.len(s), L.len(s)))), B.Rec.field(F, 7n), W)), "\t"), B.Rec.stale(F, W, W)} == R : B.Res}
  %Equal.sym(Bool, Nat.is_eq(L.len(s), L.len(s)), True{}, P.eq_refl(L.len(s))) :
    {B.Res{B.Normalized{}, q, String.join(B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(F, 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y)), 7n,
      B.Rec.info(Bool.not(Bool.and(True{}, _)), B.Rec.field(F, 7n), W)), "\t"), B.Rec.stale(F, W, W)} == R : B.Res}
  %Equal.sym(List<&2, String>, B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(F, 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, J(y)), 7n, B.Rec.field(F, 7n)), F,
    fa_same(fs, q, s, y, i2, k, hl)) :
    {B.Res{B.Normalized{}, q, String.join(_, "\t"), B.Rec.stale(F, W, W)} == R : B.Res}
  {==}

law rb_fields:
  for +fs: List<&2, String>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +i2: String
  for +k: Nat
  for +hl: {slen(fs) == 8n+k : Nat}
  for +htab: {X.all_noc(fs, '\t') == True{} : Bool}
  for +hi2: {X.no_c(i2, '\t') == True{} : Bool}
  {String.split(String.join(fsA(fs, q, s, y, i2), "\t"), '\t') == fsA(fs, q, s, y, i2) : List<&2, String>}

def rb_fields(fs, q, s, y, i2, k, hl, htab, hi2):
  +F = fsA(fs, q, s, y, i2)
  +hlF = Equal.trans(Nat, slen(F), slen(fs), 8n+k, fa_len(fs, q, s, y, i2), hl)
  +noc = fa_noc(fs, q, s, y, i2, '\t', htab, C.digits_noc(Nat.show(q), '\t', D.show_digits(q), {==}), C.show_noc(s, '\t', {==}),
    C.join_noc2(B.Alleles.show(y), ",", '\t', C.shows_noc(y, '\t', {==}), {==}), hi2)
  fields_rt(F, '\t', noc, e => len_ne(F, k, hlF, e))
