import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./tan.bend as V
import ./norm_line.bend as J
import ./norm.bend as Norm
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_rec.bend as RR
import ./proof_var_lists.bend as VL

# Proofs for the machine's fast paths: J.pfs (the first 8 fields, cut without
# splitting the rest of the line) agrees with B.Rec.fields on everything
# judging reads; J.same implies judge_in gives the record unchanged; and
# Norm.same_done is body_done with that result.

def Strs() -> Data:
  List<&2, String>

# Cutting at the first tab
# ========================

def cl(c: J.Cut) -> List<&2, String>:
  match c:
    case J.Cut{f, r, True{}}:
      f <> String.split(r, '\t')
    case J.Cut{f, r, False{}}:
      [f]

law cl_k:
  for +h: Char
  for +c: J.Cut
  {cl(J.cut.k(h, c)) == String.split.push(h, cl(c)) : List<&2, String>}

def cl_k(h, c):
  match c:
    case J.Cut{f, r, True{}}:
      {==}
    case J.Cut{f, r, False{}}:
      {==}

law cut_go:
  for +t: String
  for +b: Bool
  for +h: Char
  {cl(J.cut.go(t, b, h)) == String.split.fin(h, String.split(t, '\t'), b) : List<&2, String>}

def cut_go(t, b, h):
  match t b:
    case SNil{} True{}:
      {==}
    case SCon{+c, +t2} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, +t2} False{}:
      +X = J.cut.go(t2, Char.is_eq(c, '\t'), c)
      %Equal.sym(Strs(), cl(J.cut.k(h, X)), String.split.push(h, cl(X)), cl_k(h, X)) :
        {_ == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      %Equal.sym(Strs(), cl(X), String.split(SCon{c, t2}, '\t'), cut_go(t2, Char.is_eq(c, '\t'), c)) :
        {String.split.push(h, _) == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      {==}

law cut_split:
  for +s: String
  {cl(J.cut(s)) == String.split(s, '\t') : List<&2, String>}

def cut_split(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      cut_go(t, Char.is_eq(h, '\t'), h)

law take0:
  for +xs: List<&2, String>
  {List.take(&2, String, xs, 0n) == Nil{} : List<&2, String>}

def take0(xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      {==}

law cuts_cl:
  for +n: Nat
  for +c: J.Cut
  {J.cuts(n, c) == List.take(&2, String, cl(c), 1n+n) : List<&2, String>}

def cuts_cl(n, c):
  match n c:
    case 0n J.Cut{f, r, True{}}:
      %Equal.sym(Strs(), List.take(&2, String, String.split(r, '\t'), 0n), Nil{}, take0(String.split(r, '\t'))) :
        {[f] == f <> _ : List<&2, String>}
      {==}
    case 0n J.Cut{f, r, False{}}:
      {==}
    case 1n+m J.Cut{f, r, True{}}:
      %Equal.sym(Strs(), J.cuts(m, J.cut(r)), List.take(&2, String, cl(J.cut(r)), 1n+m), cuts_cl(m, J.cut(r))) :
        {f <> _ == List.take(&2, String, f <> String.split(r, '\t'), 2n+m) : List<&2, String>}
      %Equal.sym(Strs(), cl(J.cut(r)), String.split(r, '\t'), cut_split(r)) :
        {f <> List.take(&2, String, _, 1n+m) == List.take(&2, String, f <> String.split(r, '\t'), 2n+m) : List<&2, String>}
      {==}
    case 1n+m J.Cut{f, r, False{}}:
      {==}

# The machine's fields are the first 8 of the line's fields.
law pfs_take:
  for +body: String
  {J.pfs(body) == List.take(&2, String, B.Rec.fields(body), 8n) : List<&2, String>}

def pfs_take(body):
  %cut_split(body) :
    {J.cuts(7n, J.cut(body)) == List.take(&2, String, _, 8n) : List<&2, String>}
  cuts_cl(7n, J.cut(body))

# The first 8 fields agree with all of them
# ========================================

law lt8:
  for +n: Nat
  {Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+n, 8n) == False{} : Bool}

def lt8(n):
  P.lt_zero(n)

def tk(+ys: List<&2, String>) -> List<&2, String>:
  List.take(&2, String, ys, 8n)

law tk_mal:
  for +ys: List<&2, String>
  {B.Rec.malformed(tk(ys)) == B.Rec.malformed(ys) : Bool}

def tk_mal(ys):
  match ys:
    case Nil{}:
      {==}
    case +y0 <> Nil{}:
      {==}
    case +y0 <> +y1 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> +y3 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> +y3 <> +y4 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> +y3 <> +y4 <> +y5 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> +y3 <> +y4 <> +y5 <> +y6 <> Nil{}:
      {==}
    case +y0 <> +y1 <> +y2 <> +y3 <> +y4 <> +y5 <> +y6 <> +y7 <> +r:
      %Equal.sym(Bool, Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+List.length(&2, String, r), 8n), False{}, lt8(List.length(&2, String, r))) :
        {B.Rec.malformed(tk(y0 <> y1 <> y2 <> y3 <> y4 <> y5 <> y6 <> y7 <> r)) ==
          (((_ || String.is_empty(y0)) || Maybe.is_none(&2, Nat, B.Pos.read(y1))) || Bool.not(B.Text.is_letters(y3))) || B.Text.any_empty(String.split(y4, ',')) : Bool}
      %Equal.sym(Strs(), List.take(&2, String, r, 0n), Nil{}, take0(r)) :
        {B.Rec.malformed(y0 <> y1 <> y2 <> y3 <> y4 <> y5 <> y6 <> y7 <> _) ==
          (((False{} || String.is_empty(y0)) || Maybe.is_none(&2, Nat, B.Pos.read(y1))) || Bool.not(B.Text.is_letters(y3))) || B.Text.any_empty(String.split(y4, ',')) : Bool}
      {==}

law get_take:
  for +xs: List<&2, String>
  for +n: Nat
  for +i: Nat
  for +h: {Nat.is_lt(i, n) == True{} : Bool}
  {List.get(&2, String, List.take(&2, String, xs, n), i) == List.get(&2, String, xs, i) : Maybe<&2, String>}

def get_take(xs, n, i, h):
  match xs n i:
    case Nil{} _ _:
      {==}
    case +y <> +t 0n _:
      Empty.absurd({List.get(&2, String, List.take(&2, String, y <> t, 0n), i) == List.get(&2, String, y <> t, i) : Maybe<&2, String>},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)), h)))
    case +y <> +t 1n+p 0n:
      {==}
    case +y <> +t 1n+p 1n+j:
      get_take(t, p, j, h)

law tk_field:
  for +ys: List<&2, String>
  for +i: Nat
  for +h: {Nat.is_lt(i, 8n) == True{} : Bool}
  {B.Rec.field(tk(ys), i) == B.Rec.field(ys, i) : String}

def tk_field(ys, i, h):
  %Equal.sym(Maybe<&2, String>, List.get(&2, String, tk(ys), i), List.get(&2, String, ys, i), get_take(ys, 8n, i, h)) :
    {Maybe.default(&2, String, _, "") == B.Rec.field(ys, i) : String}
  {==}

def f1(+ys: List<&2, String>) -> {B.Rec.field(ys, 1n) == B.Rec.field(tk(ys), 1n) : String}:
  Equal.sym(String, B.Rec.field(tk(ys), 1n), B.Rec.field(ys, 1n), tk_field(ys, 1n, {==}))

def f3(+ys: List<&2, String>) -> {B.Rec.field(ys, 3n) == B.Rec.field(tk(ys), 3n) : String}:
  Equal.sym(String, B.Rec.field(tk(ys), 3n), B.Rec.field(ys, 3n), tk_field(ys, 3n, {==}))

def f4(+ys: List<&2, String>) -> {B.Rec.field(ys, 4n) == B.Rec.field(tk(ys), 4n) : String}:
  Equal.sym(String, B.Rec.field(tk(ys), 4n), B.Rec.field(ys, 4n), tk_field(ys, 4n, {==}))

def f7(+ys: List<&2, String>) -> {B.Rec.field(ys, 7n) == B.Rec.field(tk(ys), 7n) : String}:
  Equal.sym(String, B.Rec.field(tk(ys), 7n), B.Rec.field(ys, 7n), tk_field(ys, 7n, {==}))

law tk_oos:
  for +ys: List<&2, String>
  {B.Rec.out_of_scope(tk(ys)) == B.Rec.out_of_scope(ys) : Bool}

def tk_oos(ys):
  %f4(ys) : {B.Text.any_not_letters(String.split(_, ',')) == B.Rec.out_of_scope(ys) : Bool}
  {==}

law tk_pos:
  for +ys: List<&2, String>
  {B.Rec.pos(tk(ys)) == B.Rec.pos(ys) : Nat}

def tk_pos(ys):
  %f1(ys) : {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == B.Rec.pos(ys) : Nat}
  {==}

law same_go_tk:
  for +b: Bool
  for +s: Bool
  for +a: Maybe<&2, Pr.Ans>
  for +ys: List<&2, String>
  {J.same.go(b, s, a, tk(ys)) == J.same.go(b, s, a, ys) : Bool}

def same_go_tk(b, s, a, ys):
  match b s:
    case False{} False{}:
      %f1(ys) : {J.same.ans(a, Maybe.default(&2, Nat, B.Pos.read(_), 0n), _, B.Rec.field(tk(ys), 3n), B.Rec.field(tk(ys), 4n), B.Rec.field(tk(ys), 7n),
        String.split(B.Rec.field(tk(ys), 4n), ',')) == J.same.go(False{}, False{}, a, ys) : Bool}
      %f3(ys) : {J.same.ans(a, B.Rec.pos(ys), B.Rec.field(ys, 1n), _, B.Rec.field(tk(ys), 4n), B.Rec.field(tk(ys), 7n),
        String.split(B.Rec.field(tk(ys), 4n), ',')) == J.same.go(False{}, False{}, a, ys) : Bool}
      %f4(ys) : {J.same.ans(a, B.Rec.pos(ys), B.Rec.field(ys, 1n), B.Rec.field(ys, 3n), _, B.Rec.field(tk(ys), 7n),
        String.split(_, ',')) == J.same.go(False{}, False{}, a, ys) : Bool}
      %f7(ys) : {J.same.ans(a, B.Rec.pos(ys), B.Rec.field(ys, 1n), B.Rec.field(ys, 3n), B.Rec.field(ys, 4n), _,
        B.Rec.alts(ys)) == J.same.go(False{}, False{}, a, ys) : Bool}
      {==}
    case False{} True{}:
      {==}
    case True{} _:
      {==}

law same_tk:
  for +a: Maybe<&2, Pr.Ans>
  for +ys: List<&2, String>
  {J.same(a, tk(ys)) == J.same(a, ys) : Bool}

def same_tk(a, ys):
  %Equal.sym(Bool, B.Rec.malformed(tk(ys)), B.Rec.malformed(ys), tk_mal(ys)) :
    {J.same.go(_, B.Rec.out_of_scope(tk(ys)), a, tk(ys)) == J.same(a, ys) : Bool}
  %Equal.sym(Bool, B.Rec.out_of_scope(tk(ys)), B.Rec.out_of_scope(ys), tk_oos(ys)) :
    {J.same.go(B.Rec.malformed(ys), _, a, tk(ys)) == J.same(a, ys) : Bool}
  same_go_tk(B.Rec.malformed(ys), B.Rec.out_of_scope(ys), a, ys)

# Judging without an answer reads the same from the machine's fields
law jgo_tk:
  for +b: Bool
  for +s: Bool
  for +ys: List<&2, String>
  for +body: String
  {J.judge_in.go(b, s, None{}, tk(ys), body) == J.judge_in.go(b, s, None{}, ys, body) : Maybe<&2, B.Res>}

def jgo_tk(b, s, ys, body):
  match b s:
    case True{} _:
      %Equal.sym(Nat, B.Rec.pos(tk(ys)), B.Rec.pos(ys), tk_pos(ys)) : {Some{B.Res{B.Broken{}, _, body, False{}}} == J.judge_in.go(True{}, s, None{}, ys, body) : Maybe<&2, B.Res>}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, B.Rec.pos(tk(ys)), B.Rec.pos(ys), tk_pos(ys)) : {Some{B.Res{B.Skipped{}, _, body, False{}}} == J.judge_in.go(False{}, True{}, None{}, ys, body) : Maybe<&2, B.Res>}
      {==}
    case False{} False{}:
      {==}

law judge_none:
  for +body: String
  {J.judge_fs(None{}, J.pfs(body), body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}

def judge_none(body):
  +F = B.Rec.fields(body)
  %Equal.sym(Strs(), J.pfs(body), tk(B.Rec.fields(body)), pfs_take(body)) : {J.judge_fs(None{}, _, body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}
  %Equal.sym(Bool, B.Rec.malformed(tk(F)), B.Rec.malformed(F), tk_mal(F)) :
    {J.judge_in.go(_, B.Rec.out_of_scope(tk(F)), None{}, tk(F), body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}
  %Equal.sym(Bool, B.Rec.out_of_scope(tk(F)), B.Rec.out_of_scope(F), tk_oos(F)) :
    {J.judge_in.go(B.Rec.malformed(F), _, None{}, tk(F), body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}
  jgo_tk(B.Rec.malformed(F), B.Rec.out_of_scope(F), F, body)

law pfs_field:
  for +body: String
  for +i: Nat
  for +h: {Nat.is_lt(i, 8n) == True{} : Bool}
  {B.Rec.field(J.pfs(body), i) == B.Rec.field(B.Rec.fields(body), i) : String}

def pfs_field(body, i, h):
  %Equal.sym(Strs(), J.pfs(body), tk(B.Rec.fields(body)), pfs_take(body)) : {B.Rec.field(_, i) == B.Rec.field(B.Rec.fields(body), i) : String}
  tk_field(B.Rec.fields(body), i, h)

law pfs_pos:
  for +body: String
  {B.Rec.pos(J.pfs(body)) == B.Rec.pos(B.Rec.fields(body)) : Nat}

def pfs_pos(body):
  %Equal.sym(Strs(), J.pfs(body), tk(B.Rec.fields(body)), pfs_take(body)) : {B.Rec.pos(_) == B.Rec.pos(B.Rec.fields(body)) : Nat}
  tk_pos(B.Rec.fields(body))

# J.same: judge_in gives the record as it is
# ==========================================

def RES(+p: Nat, +body: String) -> Maybe<&2, B.Res>:
  Some{B.Res{B.Normalized{}, p, body, False{}}}

law same_var_sound:
  for +v: B.Var
  for +w: B.Var
  for +e: {B.Rec.same_var(v, w) == True{} : Bool}
  {w == v : B.Var}

def same_var_sound(v, w, e):
  match v w:
    case B.Var{+p, +r, +x} B.Var{+q, +s, +y}:
      +e12 = P.and_true_l(Bool.and(Nat.is_eq(p, q), B.Bases.eq(r, s)), B.Alleles.eq(x, y), e)
      +hp = P.eq_sound(p, q, P.and_true_l(Nat.is_eq(p, q), B.Bases.eq(r, s), e12))
      +hr = VL.bases_sound(r, s, P.and_true_r(Nat.is_eq(p, q), B.Bases.eq(r, s), e12))
      +hx = VL.alleles_sound(x, y, P.and_true_r(Bool.and(Nat.is_eq(p, q), B.Bases.eq(r, s)), B.Alleles.eq(x, y), e))
      %Equal.sym(Nat, p, q, hp) : {B.Var{q, s, y} == B.Var{_, r, x} : B.Var}
      %Equal.sym(List<&2, B.Base>, r, s, hr) : {B.Var{q, s, y} == B.Var{q, _, x} : B.Var}
      %Equal.sym(List<&2, List<&2, B.Base>>, x, y, hx) : {B.Var{q, s, y} == B.Var{q, s, _} : B.Var}
      {==}

def RBG(+fs: List<&2, String>, +x1: String, +x3: String, +x4: String, +x7: String) -> String:
  String.join(B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(fs, 1n, x1), 3n, x3), 4n, x4), 7n, x7), "\t")

# The record rewritten for itself is its text, when POS, REF and ALT are
# written as rebuild writes them.
law rebuild_same:
  for +fs: List<&2, String>
  for +p: Nat
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +body: String
  for +hj: {String.join(fs, "\t") == body : String}
  for +ht: {J.same.text(B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Var{p, r, a}) == True{} : Bool}
  {B.Rec.rebuild(fs, B.Var{p, r, a}, B.Var{p, r, a}) == body : String}

def rebuild_same(fs, p, r, a, body, hj, ht):
  +s1 = String.eq(Nat.show(p), B.Rec.field(fs, 1n))
  +s3 = String.eq(B.Allele.show(r), B.Rec.field(fs, 3n))
  +s4 = String.eq(String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n))
  +h13 = P.and_true_l(Bool.and(s1, s3), s4, ht)
  +e1 = Q.str_eq_sound(Nat.show(p), B.Rec.field(fs, 1n), P.and_true_l(s1, s3, h13))
  +e3 = Q.str_eq_sound(B.Allele.show(r), B.Rec.field(fs, 3n), P.and_true_r(s1, s3, h13))
  +e4 = Q.str_eq_sound(String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n), P.and_true_r(Bool.and(s1, s3), s4, ht))
  +nr = List.length(&2, B.Base, r)
  %Equal.sym(Bool, Nat.is_eq(p, p), True{}, P.eq_refl(p)) :
    {RBG(fs, Nat.show(p), B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.info(Bool.not(Bool.and(_, Nat.is_eq(nr, nr))), B.Rec.field(fs, 7n), B.Var{p, r, a})) == body : String}
  %Equal.sym(Bool, Nat.is_eq(nr, nr), True{}, P.eq_refl(nr)) :
    {RBG(fs, Nat.show(p), B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.info(Bool.not(Bool.and(True{}, _)), B.Rec.field(fs, 7n), B.Var{p, r, a})) == body : String}
  %Equal.sym(String, Nat.show(p), B.Rec.field(fs, 1n), e1) :
    {RBG(fs, _, B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(String, B.Allele.show(r), B.Rec.field(fs, 3n), e3) :
    {RBG(fs, B.Rec.field(fs, 1n), _, String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(String, String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n), e4) :
    {RBG(fs, B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), _, B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 1n, B.Rec.field(fs, 1n)), fs, RR.put_same(fs, 1n, B.Rec.field(fs, 1n), {==})) :
    {String.join(B.Rec.put(B.Rec.put(B.Rec.put(_, 3n, B.Rec.field(fs, 3n)), 4n, B.Rec.field(fs, 4n)), 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 3n, B.Rec.field(fs, 3n)), fs, RR.put_same(fs, 3n, B.Rec.field(fs, 3n), {==})) :
    {String.join(B.Rec.put(B.Rec.put(_, 4n, B.Rec.field(fs, 4n)), 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 4n, B.Rec.field(fs, 4n)), fs, RR.put_same(fs, 4n, B.Rec.field(fs, 4n), {==})) :
    {String.join(B.Rec.put(_, 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 7n, B.Rec.field(fs, 7n)), fs, RR.put_same(fs, 7n, B.Rec.field(fs, 7n), {==})) :
    {String.join(_, "\t") == body : String}
  hj

def fT(+fs: List<&2, String>) -> String:
  B.Rec.field(fs, 1n)

law l_norm:
  for +m: Maybe<&2, B.Var>
  for +fs: List<&2, String>
  for +body: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.norm(m, B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Var{p, r, a}) == True{} : Bool}
  {J.found.norm(m, fs, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}

def l_norm(m, fs, body, p, r, a, hj, h):
  match m:
    case None{}:
      Empty.absurd({J.found.norm(None{}, fs, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case Some{+w}:
      +v = {B.Var{p, r, a} : B.Var}
      +sv = B.Rec.same_var(v, w)
      +tx = J.same.text(B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), v)
      +hsv = P.and_true_l(sv, tx, h)
      %Equal.sym(Bool, sv, True{}, hsv) :
        {Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(fs, v, w), B.Rec.stale.if(_, fs)}} == RES(p, body) : Maybe<&2, B.Res>}
      %Equal.sym(B.Var, w, v, same_var_sound(v, w, hsv)) :
        {Some{B.Res{B.Normalized{}, B.Var.pos(_), B.Rec.rebuild(fs, v, _), False{}}} == RES(p, body) : Maybe<&2, B.Res>}
      %Equal.sym(String, B.Rec.rebuild(fs, v, v), body, rebuild_same(fs, p, r, a, body, hj, P.and_true_r(sv, tx, h))) :
        {Some{B.Res{B.Normalized{}, p, _, False{}}} == RES(p, body) : Maybe<&2, B.Res>}
      {==}

law l_ref:
  for +ok: Maybe<&2, Bool>
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +fs: List<&2, String>
  for +body: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.ref(ok, off, bases, B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Var{p, r, a}) == True{} : Bool}
  {J.found.ref(ok, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}

def l_ref(ok, off, bases, fs, body, p, r, a, hj, h):
  match ok:
    case Some{True{}}:
      l_norm(V.var_in(off, bases, B.Var{p, r, a}), fs, body, p, r, a, hj, h)
    case Some{False{}}:
      Empty.absurd({J.found.ref(Some{False{}}, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case None{}:
      Empty.absurd({J.found.ref(None{}, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}, P.false_ne_true(h))

law l_problem:
  for +z: Bool
  for +d: Bool
  for +clen: Nat
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +fs: List<&2, String>
  for +body: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.problem(z, d, clen, off, bases, B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Var{p, r, a}) == True{} : Bool}
  {J.found.problem(z, d, clen, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}

def l_problem(z, d, clen, off, bases, fs, body, p, r, a, hj, h):
  match z d:
    case False{} True{}:
      l_ref(J.ref_check(clen, off, bases, Nat.sub(p, 1n), r), off, bases, fs, body, p, r, a, hj, h)
    case False{} False{}:
      Empty.absurd({J.found.problem(False{}, False{}, clen, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case True{} _:
      Empty.absurd({J.found.problem(True{}, d, clen, off, bases, fs, body, B.Var{p, r, a}) == RES(p, body) : Maybe<&2, B.Res>}, P.false_ne_true(h))

law l_found:
  for +e: Bool
  for +rr: Maybe<&2, List<&2, B.Base>>
  for +aa: Maybe<&2, List<&2, List<&2, B.Base>>>
  for +clen: Nat
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +fs: List<&2, String>
  for +body: String
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.found(e, rr, aa, clen, off, bases, B.Rec.pos(fs), B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n)) == True{} : Bool}
  {J.found(e, rr, aa, clen, off, bases, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}

def l_found(e, rr, aa, clen, off, bases, fs, body, hj, h):
  match e rr aa:
    case True{} Some{+ref} Some{+alts}:
      l_problem(Nat.is_eq(B.Rec.pos(fs), 0n), B.Alleles.distinct(ref <> alts), clen, off, bases, fs, body, B.Rec.pos(fs), ref, alts, hj, h)
    case True{} Some{ref} None{}:
      Empty.absurd({J.found(True{}, Some{ref}, None{}, clen, off, bases, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case True{} None{} _:
      Empty.absurd({J.found(True{}, None{}, aa, clen, off, bases, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case False{} _ _:
      Empty.absurd({J.found(False{}, rr, aa, clen, off, bases, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))

law l_ans:
  for +a: Maybe<&2, Pr.Ans>
  for +fs: List<&2, String>
  for +body: String
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.ans(a, B.Rec.pos(fs), B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Rec.field(fs, 7n), B.Rec.alts(fs)) == True{} : Bool}
  {J.judge_in.ans(a, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}

def l_ans(a, fs, body, hj, h):
  match a:
    case Some{Pr.Known{+clen, +off, +raw}}:
      +ref = B.Rec.field(fs, 3n)
      +e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      l_found(J.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, B.Bases.of_fasta(raw), fs, body, hj, h)
    case Some{Pr.Unknown{}}:
      Empty.absurd({J.judge_in.ans(Some{Pr.Unknown{}}, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case None{}:
      Empty.absurd({J.judge_in.ans(None{}, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))

law l_go:
  for +b: Bool
  for +s: Bool
  for +a: Maybe<&2, Pr.Ans>
  for +fs: List<&2, String>
  for +body: String
  for +hj: {String.join(fs, "\t") == body : String}
  for +h: {J.same.go(b, s, a, fs) == True{} : Bool}
  {J.judge_in.go(b, s, a, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}

def l_go(b, s, a, fs, body, hj, h):
  match b s:
    case False{} False{}:
      l_ans(a, fs, body, hj, h)
    case False{} True{}:
      Empty.absurd({J.judge_in.go(False{}, True{}, a, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))
    case True{} _:
      Empty.absurd({J.judge_in.go(True{}, s, a, fs, body) == RES(B.Rec.pos(fs), body) : Maybe<&2, B.Res>}, P.false_ne_true(h))

# J.same on the machine's fields: judge_in gives the record unchanged.
law same_judge:
  for +a: Maybe<&2, Pr.Ans>
  for +body: String
  for +h: {J.same(a, J.pfs(body)) == True{} : Bool}
  {J.judge_in(a, body) == RES(B.Rec.pos(B.Rec.fields(body)), body) : Maybe<&2, B.Res>}

def same_judge(a, body, h):
  +F = B.Rec.fields(body)
  +h2 = Equal.trans(Bool, J.same(a, F), J.same(a, tk(F)), True{}, Equal.sym(Bool, J.same(a, tk(F)), J.same(a, F), same_tk(a, F)),
    Equal.trans(Bool, J.same(a, tk(F)), J.same(a, J.pfs(body)), True{},
      Equal.cong(List<&2, String>, Bool, x => J.same(a, x), tk(F), J.pfs(body), Equal.sym(Strs(), J.pfs(body), tk(F), pfs_take(body))), h))
  l_go(B.Rec.malformed(F), B.Rec.out_of_scope(F), a, F, body, RR.join_split(body, '\t'), h2)

# Norm.same_done is body_done with judge's result for a record left as it is.
law same_done:
  for +o: B.Opts
  for +rs: R.RunSt
  for +l: B.Line
  for +fs: List<&2, String>
  for +pend: String
  for +q: List<&2, B.Line>
  for +e: Bool
  {Norm.same_done(o, rs, l, fs, pend, q, e) == Norm.body_done(B.Res{B.Normalized{}, B.Rec.pos(fs), B.Line.body(l), False{}}, o, rs, l, fs, pend, q, e) : Norm.Adv}

def same_done(o, rs, l, fs, pend, q, e):
  match l:
    case B.Line{+b, +t}:
      +rs1 = R.tick(rs)
      +at = {B.At{R.RunSt.n(rs1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      %Equal.sym(Bool, String.eq(b, b), True{}, Q.str_eq_refl(b)) :
        {Norm.same_done(o, rs, B.Line{b, t}, fs, pend, q, e) ==
          Norm.went(o, R.keyed(rs1, R.Opts.w(o), R.Item{B.Rec.pos(fs), B.Rec.pos(fs), at, String.append(b, t)}, R.stale_note(False{}, at),
            R.bump(R.RunSt.cnt(rs1), Bool.not(_), False{}, False{})), pend, q, e) : Norm.Adv}
      {==}
