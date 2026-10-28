import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm.bend as Norm
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./proof_window_defs.bend as WS
import ./proof_b_defs.bend as P
import ./proof_b_fasteq.bend as FE
import ./norm_fast.bend as NF
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ./proof_b_cache_lem.bend as X
import ./proof_b_cache_te.bend as TE
import ./proof_b_cache_hit.bend as H
import ./proof_b_enc_lem.bend as EL
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-words/proof_u32.bend as U
import ./proof_b_enc.bend as PE
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-arrays/proof_base.bend as AB
import ./proof_window_lists.bend as WL
import ./proof_b_cachedefs.bend as CD

# The proofs about the machine's reference cache (definitions:
# proof_b_cachedefs.bend).

# ---------------------------------------------------------------------------
# Lemmas
# ---------------------------------------------------------------------------

# holds's test for a window of contig c read from x up to y (WPKnown and
# WPStr test the same).
def hk_test(+fa: List<&2, B.Contig>, +c: String, +x: Nat, +y: Nat, +a: Nat, +e: Nat, +r: String,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hx: {Nat.is_le(x, a) == True{} : Bool},
  +hy: {Nat.is_le(e, y) == True{} : Bool}) ->
  {Bool.and(Maybe.is_some(&2, String, B.Fasta.find(fa, c)), Bool.and(Bool.and(String.eq(c, c), Nat.is_le(x, a)), Nat.is_le(Nat.min(e, CD.wp.clen.k(B.Fasta.find(fa, c))), Nat.min(y, CD.wp.clen.k(B.Fasta.find(fa, c)))))) == True{} : Bool}:
  +l = String.length(r)
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) :
    {Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c, c), Nat.is_le(x, a)), Nat.is_le(Nat.min(e, CD.wp.clen.k(_)), Nat.min(y, CD.wp.clen.k(_))))) == True{} : Bool}
  %Equal.sym(Bool, String.eq(c, c), True{}, X.str_eq_refl(c)) : {Bool.and(Bool.and(_, Nat.is_le(x, a)), Nat.is_le(Nat.min(e, l), Nat.min(y, l))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(x, a), True{}, hx) : {Bool.and(Bool.and(True{}, _), Nat.is_le(Nat.min(e, l), Nat.min(y, l))) == True{} : Bool}
  X.min_mono(e, y, l, hy)

def hk_pick(+fa: List<&2, B.Contig>, +c: String, +x: Nat, +y: Nat, +a: Nat, +e: Nat, +r: String, +p: Bool,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hx: {Nat.is_le(x, a) == True{} : Bool},
  +hy: {Nat.is_le(e, y) == True{} : Bool}) ->
  {CD.holds(fa, Bool.pick(CD.WP, p, CD.WPKnown{c, x, y}, CD.WPStr{c, x, y}), c, a, e) == True{} : Bool}:
  match p:
    case True{}:
      hk_test(fa, c, x, y, a, e, r, hf, hx, hy)
    case False{}:
      hk_test(fa, c, x, y, a, e, r, hf, hx, hy)

def wp_holds.k(+fa: List<&2, B.Contig>, +c: String, +x: Nat, +y: Nat, +a: Nat, +e: Nat, +m: Maybe<&2, String>,
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +hx: {Nat.is_le(x, a) == True{} : Bool},
  +hy: {Nat.is_le(e, y) == True{} : Bool}) ->
  {CD.holds(fa, CD.wpOf(fa, c, x, y), c, a, e) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {CD.holds(fa, CD.wpOf.k(_, c, x, y), c, a, e) == True{} : Bool}
      X.str_eq_refl(c)
    case Some{r}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {CD.holds(fa, CD.wpOf.k(_, c, x, y), c, a, e) == True{} : Bool}
      hk_pick(fa, c, x, y, a, e, r, Norm.le31(Nat.sub(y, x)), hm, hx, hy)

# The window of the reads x .. y holds the read (a, e) when x <= a and
# e <= y.
def wp_holds(+fa: List<&2, B.Contig>, +c: String, +x: Nat, +y: Nat, +a: Nat, +e: Nat,
  +hx: {Nat.is_le(x, a) == True{} : Bool},
  +hy: {Nat.is_le(e, y) == True{} : Bool}) ->
  {CD.holds(fa, CD.wpOf(fa, c, x, y), c, a, e) == True{} : Bool}:
  wp_holds.k(fa, c, x, y, a, e, B.Fasta.find(fa, c), {==}, hx, hy)

def rq.p(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +e: Nat, +p: Bool) ->
  {CD.holds(fa, Bool.pick(CD.WP, p, CD.wpOf(fa, c, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead()))), CD.wpOf(fa, c, a, e)), c, a, e) == True{} : Bool}:
  match p:
    case True{}:
      wp_holds(fa, c, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead())), a, e, X.sub_le(a, Norm.margin()), X.le_max_l(e, Nat.add(a, Norm.ahead())))
    case False{}:
      wp_holds(fa, c, a, e, a, e, N.le_refl(a), N.le_refl(e))

# ---------------------------------------------------------------------------
# The window's answers (win_truths)
# ---------------------------------------------------------------------------

def some_inj(+x: String, +y: String, e: {Some{x} == Some{y} : Maybe<&2, String>}) -> {x == y : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, x), Some{x}, Some{y}, e)

def fb.k(+n: String, +r0: String, +t: List<&2, B.Contig>, +c: String, +r: String, +q: Bool,
  +hq: {String.eq(n, c) == q : Bool},
  +hb: {Bool.and(E.is_bytes(r0), CD.fa_bytes(t)) == True{} : Bool},
  +hf: {B.Fasta.find.put(String.eq(n, c), r0, B.Fasta.find(t, c)) == Some{r} : Maybe<&2, String>},
  ih: {B.Fasta.find(t, c) == Some{r} : Maybe<&2, String>} -> {E.is_bytes(r) == True{} : Bool}) ->
  {E.is_bytes(r) == True{} : Bool}:
  match q:
    case True{}:
      +e = AB.subst(Bool, z => {B.Fasta.find.put(z, r0, B.Fasta.find(t, c)) == Some{r} : Maybe<&2, String>}, String.eq(n, c), True{}, hq, hf)
      AB.subst(String, z => {E.is_bytes(z) == True{} : Bool}, r0, r, some_inj(r0, r, e), N.and_true_l(E.is_bytes(r0), CD.fa_bytes(t), hb))
    case False{}:
      ih(AB.subst(Bool, z => {B.Fasta.find.put(z, r0, B.Fasta.find(t, c)) == Some{r} : Maybe<&2, String>}, String.eq(n, c), False{}, hq, hf))

# A contig found in a FASTA file of bytes has byte letters.
def find_bytes(+fa: List<&2, B.Contig>, +c: String, +r: String,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>}) ->
  {E.is_bytes(r) == True{} : Bool}:
  match fa:
    case Nil{}:
      Empty.absurd({E.is_bytes(r) == True{} : Bool}, N.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{r}, hf)))
    case Con{B.Contig{n, r0}, t}:
      fb.k(n, r0, t, c, r, String.eq(n, c), {==}, hb, hf, h => find_bytes(t, c, r, N.and_true_r(E.is_bytes(r0), CD.fa_bytes(t), hb), h))

def letters_bytes(+r: String, +a: Nat, +b: Nat, +h: {E.is_bytes(r) == True{} : Bool}) ->
  {E.is_bytes(CD.letters(r, a, b)) == True{} : Bool}:
  X.bytes_take(String.drop(r, a), Nat.sub(b, a), X.bytes_drop(r, a, h))

def letters_le(+r: String, +a: Nat, +b: Nat) -> {Nat.is_le(String.length(CD.letters(r, a, b)), Nat.sub(b, a)) == True{} : Bool}:
  X.take_len_le(String.drop(r, a), Nat.sub(b, a))

# a <= m <= b: the letters from a up to m, then from m up to b.
def letters_cat(+r: String, +a: Nat, +m: Nat, +b: Nat,
  +ham: {Nat.is_le(a, m) == True{} : Bool},
  +hmb: {Nat.is_le(m, b) == True{} : Bool}) ->
  {String.append(CD.letters(r, a, m), CD.letters(r, m, b)) == CD.letters(r, a, b) : String}:
  +s = String.drop(r, a)
  +i = Nat.sub(m, a)
  +j = Nat.sub(b, m)
  +hd = Equal.trans(String, String.drop(s, i), String.drop(r, Nat.add(a, i)), String.drop(r, m), X.drop_drop_s(r, a, i), Equal.cong(Nat, String, z => String.drop(r, z), Nat.add(a, i), m, N.le_sub_add(a, m, ham)))
  %hd : {String.append(String.take(s, i), String.take(_, j)) == String.take(s, Nat.sub(b, a)) : String}
  Equal.trans(String, String.append(String.take(s, i), String.take(String.drop(s, i), j)), String.take(s, Nat.add(i, j)), String.take(s, Nat.sub(b, a)),
    X.take_app_s(s, i, j), Equal.cong(Nat, String, z => String.take(s, z), Nat.add(i, j), Nat.sub(b, a), X.sub_add_sub(a, m, b, ham, hmb)))

# A read within le31, as enc_ok wants it.
def l31_of(+n: Nat, +x: Nat, +h: {Nat.is_le(n, x) == True{} : Bool}, +hx: {Norm.le31(x) == True{} : Bool}) ->
  {P.le31(n) == True{} : Bool}:
  X.le31_mono(n, x, h, hx)

# A list of two reads or more, the first on contig c from a: win_of reads it
# in parts, up to the last read's end.
def W2.t(+t: List<&2, Pr.Req>, +c1: String, +a1: Nat, +e1: Nat, +c: String, +a: Nat, +z: Nat, -as: List<&1, Pr.Ans>,
  +h1: {X.hd1(Con{Pr.Req{c1, a1, e1}, t}, c, a) == True{} : Bool},
  +h2: {Nat.is_le(2n, List.length(&2, Pr.Req, Con{Pr.Req{c1, a1, e1}, t})) == True{} : Bool}) ->
  {Norm.win_of(Con{Pr.Req{c1, a1, e1}, t}, as) == Norm.win_parts(c, a, Norm.last_b(Con{Pr.Req{c1, a1, e1}, t}, z), as) : Norm.Win}:
  match t:
    case Nil{}:
      Empty.absurd({Norm.win_of(Con{Pr.Req{c1, a1, e1}, Nil{}}, as) == Norm.win_parts(c, a, Norm.last_b(Con{Pr.Req{c1, a1, e1}, Nil{}}, z), as) : Norm.Win}, N.false_ne_true(h2))
    case Con{r2, t2}:
      +ec = WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      +ea = N.eq_sound(a1, a, N.and_true_r(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      %ec : {Norm.win_parts(c1, a1, Norm.last_b(Con{r2, t2}, e1), as) == Norm.win_parts(_, a, Norm.last_b(Con{r2, t2}, e1), as) : Norm.Win}
      %ea : {Norm.win_parts(c1, a1, Norm.last_b(Con{r2, t2}, e1), as) == Norm.win_parts(c1, _, Norm.last_b(Con{r2, t2}, e1), as) : Norm.Win}
      {==}

def W2(+rs: List<&2, Pr.Req>, +c: String, +a: Nat, +z: Nat, -as: List<&1, Pr.Ans>,
  +h1: {X.hd1(rs, c, a) == True{} : Bool},
  +h2: {Nat.is_le(2n, List.length(&2, Pr.Req, rs)) == True{} : Bool}) ->
  {Norm.win_of(rs, as) == Norm.win_parts(c, a, Norm.last_b(rs, z), as) : Norm.Win}:
  match rs:
    case Nil{}:
      Empty.absurd({Norm.win_of(Nil{}, as) == Norm.win_parts(c, a, Norm.last_b(Nil{}, z), as) : Norm.Win}, N.false_ne_true(h1))
    case Con{Pr.Req{c1, a1, e1}, t}:
      W2.t(t, c1, a1, e1, c, a, z, as, h1, h2)

# The answers to reads from a on a contig found: one window of its letters.
def WP_some(+rs: List<&2, Pr.Req>, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +h1: {X.hd1(rs, c, a) == True{} : Bool}) ->
  {Norm.win_parts(c, a, b, M.truths(fa, rs)) == Norm.WStr{c, a, b, String.length(r), Nat.min(a, String.length(r)), Norm.raws(M.truths(fa, rs))} : Norm.Win}:
  match rs:
    case Nil{}:
      Empty.absurd({Norm.win_parts(c, a, b, M.truths(fa, Nil{})) == Norm.WStr{c, a, b, String.length(r), Nat.min(a, String.length(r)), Norm.raws(M.truths(fa, Nil{}))} : Norm.Win}, N.false_ne_true(h1))
    case Con{Pr.Req{c1, a1, e1}, t}:
      +l = String.length(r)
      +ec = WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      +ea = N.eq_sound(a1, a, N.and_true_r(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      %Equal.sym(String, c1, c, ec) : {Norm.win_parts(c, a, b, Con{M.truth.of(B.Fasta.find(fa, _), a1, e1), M.truths(fa, t)}) == Norm.WStr{c, a, b, l, Nat.min(a, l), Norm.raws(Con{M.truth.of(B.Fasta.find(fa, _), a1, e1), M.truths(fa, t)})} : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.win_parts(c, a, b, Con{M.truth.of(_, a1, e1), M.truths(fa, t)}) == Norm.WStr{c, a, b, l, Nat.min(a, l), Norm.raws(Con{M.truth.of(_, a1, e1), M.truths(fa, t)})} : Norm.Win}
      %ea : {Norm.win_parts(c, a, b, Con{M.truth.of(Some{r}, a1, e1), M.truths(fa, t)}) == Norm.WStr{c, a, b, l, Nat.min(_, l), Norm.raws(Con{M.truth.of(Some{r}, a1, e1), M.truths(fa, t)})} : Norm.Win}
      {==}

# The same, contig not found: unknown.
def WP_none(+rs: List<&2, Pr.Req>, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hm: {B.Fasta.find(fa, c) == None{} : Maybe<&2, String>},
  +h1: {X.hd1(rs, c, a) == True{} : Bool}) ->
  {Norm.win_parts(c, a, b, M.truths(fa, rs)) == Norm.WUnk{c} : Norm.Win}:
  match rs:
    case Nil{}:
      Empty.absurd({Norm.win_parts(c, a, b, M.truths(fa, Nil{})) == Norm.WUnk{c} : Norm.Win}, N.false_ne_true(h1))
    case Con{Pr.Req{c1, a1, e1}, t}:
      +ec = WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), h1))
      %Equal.sym(String, c1, c, ec) : {Norm.win_parts(c, a, b, Con{M.truth.of(B.Fasta.find(fa, _), a1, e1), M.truths(fa, t)}) == Norm.WUnk{c} : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {Norm.win_parts(c, a, b, Con{M.truth.of(_, a1, e1), M.truths(fa, t)}) == Norm.WUnk{c} : Norm.Win}
      {==}

# The answers to reads on contig c, joined: those of the first reads, then
# of the rest.
def rt_app(+fa: List<&2, B.Contig>, +c: String, +r: String,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +xs: List<&2, Pr.Req>, +ys: List<&2, Pr.Req>,
  +h: {X.allc(xs, c) == True{} : Bool}) ->
  {Norm.raws(M.truths(fa, List.append(&2, Pr.Req, xs, ys))) == String.append(Norm.raws(M.truths(fa, xs)), Norm.raws(M.truths(fa, ys))) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{Pr.Req{c1, a1, e1}, t}:
      +ec = WL.string_eq_sound(c1, c, N.and_true_l(String.eq(c1, c), X.allc(t, c), h))
      +A = Norm.raws(M.truths(fa, t))
      +Bs = Norm.raws(M.truths(fa, ys))
      %Equal.sym(String, c1, c, ec) : {Norm.raws(Con{M.truth.of(B.Fasta.find(fa, _), a1, e1), M.truths(fa, List.append(&2, Pr.Req, t, ys))}) == String.append(Norm.raws(Con{M.truth.of(B.Fasta.find(fa, _), a1, e1), M.truths(fa, t)}), Bs) : String}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.raws(Con{M.truth.of(_, a1, e1), M.truths(fa, List.append(&2, Pr.Req, t, ys))}) == String.append(Norm.raws(Con{M.truth.of(_, a1, e1), M.truths(fa, t)}), Bs) : String}
      +TX = Norm.text_of(E.enc(String.take(String.drop(r, a1), Nat.sub(e1, a1))))
      %Equal.sym(String, Norm.raws(M.truths(fa, List.append(&2, Pr.Req, t, ys))), String.append(A, Bs), rt_app(fa, c, r, hf, t, ys, N.and_true_r(String.eq(c1, c), X.allc(t, c), h))) :
        {String.append(TX, _) == String.append(String.append(TX, A), Bs) : String}
      Equal.sym(String, String.append(String.append(TX, A), Bs), String.append(TX, String.append(A, Bs)), X.str_assoc(TX, A, Bs))

# The answers to the reads of a .. b (contig found), decoded and joined:
# the letters a .. b.
def rw(+fuel: Nat, +one: Bool, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +ho: {Norm.le31(Nat.sub(b, a)) == one : Bool},
  +hfu: {Nat.is_le(Nat.sub(b, a), fuel) == True{} : Bool}) ->
  {Norm.raws(M.truths(fa, Norm.parts.go(fuel, one, c, a, b))) == CD.letters(r, a, b) : String}:
  match fuel one:
    case _ True{}:
      +l = CD.letters(r, a, b)
      %Equal.sym(List<&2, Pr.Req>, Norm.parts.go(fuel, True{}, c, a, b), [Pr.Req{c, a, b}], X.pp_true(fuel, c, a, b)) : {Norm.raws(M.truths(fa, _)) == l : String}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.raws(Con{M.truth.of(_, a, b), Nil{}}) == l : String}
      %Equal.sym(String, Norm.text_of(E.enc(l)), l, TE.te(l, letters_bytes(r, a, b, hbr), l31_of(String.length(l), Nat.sub(b, a), letters_le(r, a, b), ho))) : {String.append(_, "") == l : String}
      X.str_nil(l)
    case 0n False{}:
      X.pg_none(a, b, {Norm.raws(M.truths(fa, Norm.parts.go(0n, False{}, c, a, b))) == CD.letters(r, a, b) : String}, ho, hfu)
    case 1n+f False{}:
      +m = X.PM(a, b)
      +o1 = Norm.le31(Nat.sub(m, a))
      +o2 = Norm.le31(Nat.sub(b, m))
      +xs = Norm.parts.go(f, o1, c, a, m)
      +ys = Norm.parts.go(f, o2, c, m, b)
      %Equal.sym(String, Norm.raws(M.truths(fa, List.append(&2, Pr.Req, xs, ys))), String.append(Norm.raws(M.truths(fa, xs)), Norm.raws(M.truths(fa, ys))), rt_app(fa, c, r, hf, xs, ys, X.pallc(f, o1, c, a, m))) :
        {_ == CD.letters(r, a, b) : String}
      %Equal.sym(String, Norm.raws(M.truths(fa, xs)), CD.letters(r, a, m), rw(f, o1, fa, c, a, m, r, hbr, hf, {==}, X.hf_a(f, a, b, ho, hfu))) :
        {String.append(_, Norm.raws(M.truths(fa, ys))) == CD.letters(r, a, b) : String}
      %Equal.sym(String, Norm.raws(M.truths(fa, ys)), CD.letters(r, m, b), rw(f, o2, fa, c, m, b, r, hbr, hf, {==}, X.hf_b(f, a, b, ho, hfu))) :
        {String.append(CD.letters(r, a, m), _) == CD.letters(r, a, b) : String}
      +x = Nat.sub(b, a)
      letters_cat(r, a, m, b, N.le_add_r(a, X.HV(x)), X.le_add_of_sub(a, X.HV(x), b, X.half_lt(x, N.le_trans(1n, 2n, x, {==}, X.two_of(x, ho)))))

# The window of reads in parts, contig found.
def wt.s(+fuel: Nat, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +ho: {Norm.le31(Nat.sub(b, a)) == False{} : Bool},
  +hfu: {Nat.is_le(Nat.sub(b, a), fuel) == True{} : Bool}) ->
  {Norm.win_of(Norm.parts.go(fuel, False{}, c, a, b), M.truths(fa, Norm.parts.go(fuel, False{}, c, a, b))) == CD.mkWin(fa, CD.WPStr{c, a, b}) : Norm.Win}:
  match fuel:
    case 0n:
      X.pg_none(a, b, {Norm.win_of(Norm.parts.go(0n, False{}, c, a, b), M.truths(fa, Norm.parts.go(0n, False{}, c, a, b))) == CD.mkWin(fa, CD.WPStr{c, a, b}) : Norm.Win}, ho, hfu)
    case 1n+f:
      +rs = Norm.parts.go(1n+f, False{}, c, a, b)
      +l = String.length(r)
      %Equal.sym(Norm.Win, Norm.win_of(rs, M.truths(fa, rs)), Norm.win_parts(c, a, Norm.last_b(rs, 0n), M.truths(fa, rs)), W2(rs, c, a, 0n, M.truths(fa, rs), X.ph(1n+f, False{}, c, a, b), X.pl2(f, c, a, b))) :
        {_ == CD.mkWin(fa, CD.WPStr{c, a, b}) : Norm.Win}
      %Equal.sym(Nat, Norm.last_b(rs, 0n), b, X.plast(1n+f, False{}, c, a, b, 0n)) : {Norm.win_parts(c, a, _, M.truths(fa, rs)) == CD.mkWin(fa, CD.WPStr{c, a, b}) : Norm.Win}
      %Equal.sym(Norm.Win, Norm.win_parts(c, a, b, M.truths(fa, rs)), Norm.WStr{c, a, b, l, Nat.min(a, l), Norm.raws(M.truths(fa, rs))}, WP_some(rs, fa, c, a, b, r, hf, X.ph(1n+f, False{}, c, a, b))) :
        {_ == CD.mkWin(fa, CD.WPStr{c, a, b}) : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.WStr{c, a, b, l, Nat.min(a, l), Norm.raws(M.truths(fa, rs))} == CD.mkWin.k(_, c, a, b, True{}) : Norm.Win}
      Equal.cong(String, Norm.Win, z => Norm.WStr{c, a, b, l, Nat.min(a, l), z}, Norm.raws(M.truths(fa, rs)), CD.letters(r, a, b), rw(1n+f, False{}, fa, c, a, b, r, hbr, hf, ho, hfu))

# The window of reads in parts, contig not found.
def wt.n(+fuel: Nat, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hm: {B.Fasta.find(fa, c) == None{} : Maybe<&2, String>},
  +ho: {Norm.le31(Nat.sub(b, a)) == False{} : Bool},
  +hfu: {Nat.is_le(Nat.sub(b, a), fuel) == True{} : Bool}) ->
  {Norm.win_of(Norm.parts.go(fuel, False{}, c, a, b), M.truths(fa, Norm.parts.go(fuel, False{}, c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}:
  match fuel:
    case 0n:
      X.pg_none(a, b, {Norm.win_of(Norm.parts.go(0n, False{}, c, a, b), M.truths(fa, Norm.parts.go(0n, False{}, c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}, ho, hfu)
    case 1n+f:
      +rs = Norm.parts.go(1n+f, False{}, c, a, b)
      %Equal.sym(Norm.Win, Norm.win_of(rs, M.truths(fa, rs)), Norm.win_parts(c, a, Norm.last_b(rs, 0n), M.truths(fa, rs)), W2(rs, c, a, 0n, M.truths(fa, rs), X.ph(1n+f, False{}, c, a, b), X.pl2(f, c, a, b))) :
        {_ == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {Norm.win_parts(c, a, Norm.last_b(rs, 0n), M.truths(fa, rs)) == CD.mkWin(fa, CD.wpOf.k(_, c, a, b)) : Norm.Win}
      WP_none(rs, fa, c, a, Norm.last_b(rs, 0n), hm, X.ph(1n+f, False{}, c, a, b))

def wt.k(+m: Maybe<&2, String>, +one: Bool, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +ho: {Norm.le31(Nat.sub(b, a)) == one : Bool}) ->
  {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}:
  match m one:
    case None{} True{}:
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), True{}, ho) :
        {Norm.win_of(Norm.parts.go(Nat.sub(b, a), _, c, a, b), M.truths(fa, Norm.parts.go(Nat.sub(b, a), _, c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
      %Equal.sym(List<&2, Pr.Req>, Norm.parts.go(Nat.sub(b, a), True{}, c, a, b), [Pr.Req{c, a, b}], X.pp_true(Nat.sub(b, a), c, a, b)) :
        {Norm.win_of(_, M.truths(fa, _)) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) :
        {Norm.win_of.single(c, a, b, Con{M.truth.of(_, a, b), Nil{}}) == CD.mkWin(fa, CD.wpOf.k(_, c, a, b)) : Norm.Win}
      {==}
    case None{} False{}:
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), False{}, ho) :
        {Norm.win_of(Norm.parts.go(Nat.sub(b, a), _, c, a, b), M.truths(fa, Norm.parts.go(Nat.sub(b, a), _, c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
      wt.n(Nat.sub(b, a), fa, c, a, b, hm, ho, N.le_refl(Nat.sub(b, a)))
    case Some{r} True{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) :
        {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == CD.mkWin(fa, CD.wpOf.k(_, c, a, b)) : Norm.Win}
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), True{}, ho) :
        {Norm.win_of(Norm.parts.go(Nat.sub(b, a), _, c, a, b), M.truths(fa, Norm.parts.go(Nat.sub(b, a), _, c, a, b))) == CD.mkWin(fa, Bool.pick(CD.WP, _, CD.WPKnown{c, a, b}, CD.WPStr{c, a, b})) : Norm.Win}
      %Equal.sym(List<&2, Pr.Req>, Norm.parts.go(Nat.sub(b, a), True{}, c, a, b), [Pr.Req{c, a, b}], X.pp_true(Nat.sub(b, a), c, a, b)) :
        {Norm.win_of(_, M.truths(fa, _)) == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) :
        {Norm.win_of.single(c, a, b, Con{M.truth.of(_, a, b), Nil{}}) == CD.mkWin.k(_, c, a, b, False{}) : Norm.Win}
      {==}
    case Some{r} False{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) :
        {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == CD.mkWin(fa, CD.wpOf.k(_, c, a, b)) : Norm.Win}
      %Equal.sym(Bool, Norm.le31(Nat.sub(b, a)), False{}, ho) :
        {Norm.win_of(Norm.parts.go(Nat.sub(b, a), _, c, a, b), M.truths(fa, Norm.parts.go(Nat.sub(b, a), _, c, a, b))) == CD.mkWin(fa, Bool.pick(CD.WP, _, CD.WPKnown{c, a, b}, CD.WPStr{c, a, b})) : Norm.Win}
      wt.s(Nat.sub(b, a), fa, c, a, b, r, find_bytes(fa, c, r, hb, hm), hm, ho, N.le_refl(Nat.sub(b, a)))

def wo.p(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +p: Bool,
  +hp: {Norm.le31(Nat.sub(b, a)) == p : Bool}) ->
  {CD.wp_ok(fa, Bool.pick(CD.WP, p, CD.WPKnown{c, a, b}, CD.WPStr{c, a, b})) == True{} : Bool}:
  match p:
    case True{}:
      hp
    case False{}:
      {==}

def wo.k(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  {CD.wp_ok(fa, CD.wpOf(fa, c, a, b)) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {CD.wp_ok(fa, CD.wpOf.k(_, c, a, b)) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {Maybe.is_none(&2, String, _) == True{} : Bool}
      {==}
    case Some{r}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) : {CD.wp_ok(fa, CD.wpOf.k(_, c, a, b)) == True{} : Bool}
      wo.p(fa, c, a, b, Norm.le31(Nat.sub(b, a)), {==})

# ---------------------------------------------------------------------------
# Serving from a window (serve_ok)
# ---------------------------------------------------------------------------

def none_of(+m: Maybe<&2, String>, +h: {Maybe.is_none(&2, String, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>}, N.false_ne_true(h))

# The window from a0, read from a: its letters from 0 when a0 = a = 0.
def ws0(+x: Char, +t: String, +b0: Nat, +q: Nat,
  +hb: {Nat.is_le(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(b0, String.length(SCon{x, t}))) == True{} : Bool}) ->
  {String.take(String.drop(CD.letters(SCon{x, t}, 0n, b0), Nat.sub(Nat.min(0n, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))), Nat.sub(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))) == CD.letters(SCon{x, t}, 0n, 1n+q) : String}:
  match b0:
    case 0n:
      Empty.absurd({String.take(String.drop(CD.letters(SCon{x, t}, 0n, 0n), Nat.sub(Nat.min(0n, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))), Nat.sub(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))) == CD.letters(SCon{x, t}, 0n, 1n+q) : String}, N.false_ne_true(hb))
    case 1n+q0:
      %X.tt(t, q0, q, hb) : {SCon{x, String.take(String.take(t, q0), Nat.min(q, String.length(t)))} == SCon{x, _} : String}
      {==}

# A window of contig r's letters a0 .. b0, cut to the read a .. b it holds
# (a0 <= a, b no later than b0, both cut at the contig's end): the read's
# letters.
def ws(+r: String, +a0: Nat, +a: Nat, +b0: Nat, +b: Nat,
  +ha: {Nat.is_le(a0, a) == True{} : Bool},
  +hb: {Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))) == True{} : Bool}) ->
  {String.take(String.drop(CD.letters(r, a0, b0), Nat.sub(Nat.min(a, String.length(r)), Nat.min(a0, String.length(r)))), Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r)))) == CD.letters(r, a, b) : String}:
  match r a0 a b0 b:
    case SNil{} _ _ _ _:
      {==}
    case SCon{x, t} _ _ _ 0n:
      +y = String.drop(CD.letters(SCon{x, t}, a0, b0), Nat.sub(Nat.min(a, String.length(SCon{x, t})), Nat.min(a0, String.length(SCon{x, t}))))
      Equal.trans(String, String.take(y, 0n), "", CD.letters(SCon{x, t}, a, 0n), X.take0_s(y), Equal.sym(String, String.take(String.drop(SCon{x, t}, a), 0n), "", X.take0_s(String.drop(SCon{x, t}, a))))
    case SCon{x, t} 1n+p0 0n _ 1n+q:
      Empty.absurd({String.take(String.drop(CD.letters(SCon{x, t}, 1n+p0, b0), Nat.sub(Nat.min(0n, String.length(SCon{x, t})), Nat.min(1n+p0, String.length(SCon{x, t})))), Nat.sub(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))) == CD.letters(SCon{x, t}, 0n, 1n+q) : String}, N.false_ne_true(ha))
    case SCon{x, t} 0n 0n _ 1n+q:
      ws0(x, t, b0, q, hb)
    case SCon{x, t} 0n 1n+p 0n 1n+q:
      Empty.absurd({String.take(String.drop(CD.letters(SCon{x, t}, 0n, 0n), Nat.sub(Nat.min(1n+p, String.length(SCon{x, t})), Nat.min(0n, String.length(SCon{x, t})))), Nat.sub(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(1n+p, String.length(SCon{x, t})))) == CD.letters(SCon{x, t}, 1n+p, 1n+q) : String}, N.false_ne_true(hb))
    case SCon{x, t} 0n 1n+p 1n+q0 1n+q:
      +l = String.length(t)
      +e1 = Equal.trans(String, String.take(String.drop(t, 0n), Nat.sub(q0, 0n)), String.take(t, Nat.sub(q0, 0n)), String.take(t, q0),
        Equal.cong(String, String, z => String.take(z, Nat.sub(q0, 0n)), String.drop(t, 0n), t, X.drop0_s(t)),
        Equal.cong(Nat, String, z => String.take(t, z), Nat.sub(q0, 0n), q0, N.sub_zero(q0)))
      %e1 : {String.take(String.drop(_, Nat.min(p, l)), Nat.sub(Nat.min(q, l), Nat.min(p, l))) == CD.letters(t, p, q) : String}
      %N.sub_zero(Nat.min(p, l)) : {String.take(String.drop(String.take(String.drop(t, 0n), Nat.sub(q0, 0n)), _), Nat.sub(Nat.min(q, l), Nat.min(p, l))) == CD.letters(t, p, q) : String}
      ws(t, 0n, p, q0, q, N.le_zero_l(p), hb)
    case SCon{x, t} 1n+p0 1n+p 0n 1n+q:
      Empty.absurd({String.take(String.drop(CD.letters(SCon{x, t}, 1n+p0, 0n), Nat.sub(Nat.min(1n+p, String.length(SCon{x, t})), Nat.min(1n+p0, String.length(SCon{x, t})))), Nat.sub(Nat.min(1n+q, String.length(SCon{x, t})), Nat.min(1n+p, String.length(SCon{x, t})))) == CD.letters(SCon{x, t}, 1n+p, 1n+q) : String}, N.false_ne_true(hb))
    case SCon{x, t} 1n+p0 1n+p 1n+q0 1n+q:
      ws(t, p0, p, q0, q, ha, hb)

# The length of a window's letters.
def len_letters(+r: String, +a0: Nat, +b0: Nat) ->
  {String.length(CD.letters(r, a0, b0)) == Nat.sub(Nat.min(b0, String.length(r)), Nat.min(a0, String.length(r))) : Nat}:
  match r a0 b0:
    case SNil{} _ 0n:
      {==}
    case SNil{} _ 1n+q:
      {==}
    case SCon{x, t} 0n 0n:
      {==}
    case SCon{x, t} 0n 1n+q:
      %X.take_len(t, q) : {1n+String.length(String.take(t, q)) == 1n+_ : Nat}
      {==}
    case SCon{x, t} 1n+p 0n:
      %Equal.sym(String, String.take(String.drop(t, p), 0n), "", X.take0_s(String.drop(t, p))) : {String.length(_) == 0n : Nat}
      {==}
    case SCon{x, t} 1n+p 1n+q:
      len_letters(t, p, q)

# The read's bytes, nothing to read (n = 0): no letters.
def cx.z(+r: String, +a0: Nat, +b0: Nat, +a: Nat, +b: Nat,
  +hn: {Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))) == 0n : Nat}) ->
  {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), U32.from_nat(Nat.sub(Nat.min(a, String.length(r)), Nat.min(a0, String.length(r)))), U32.from_nat(Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))))))) == CD.letters(r, a, b) : String}:
  +l = String.length(r)
  +lt = CD.letters(r, a0, b0)
  +LW = U32.from_nat(String.length(lt))
  +TW = PE.enc_t(lt)
  +S = U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l)))
  %Equal.sym(Nat, Nat.sub(Nat.min(b, l), Nat.min(a, l)), 0n, hn) : {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(LW, TW), S, U32.from_nat(_)))) == CD.letters(r, a, b) : String}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(LW, TW), S), (C.BT(LW, TW), C.AT(LW, TW, S)), C.at_pair_t(LW, TW, S)) :
    {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.go(U32.to_nat(0), _, S))) == CD.letters(r, a, b) : String}
  Equal.sym(String, CD.letters(r, a, b), "", X.len0(CD.letters(r, a, b), Equal.trans(Nat, String.length(CD.letters(r, a, b)), Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), 0n, len_letters(r, a, b), hn)))

# The bound for to_list's view law, and the indices as Nats.
def cx.hs(+r: String, +a0: Nat, +b0: Nat, +a: Nat, +b: Nat, +i: Nat, +n: Nat,
  +hi: {U32.to_nat(U32.from_nat(i)) == i : Nat},
  +hn: {U32.to_nat(U32.from_nat(n)) == n : Nat},
  +hl: {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0)))) == String.length(CD.letters(r, a0, b0)) : Nat},
  +h: {Nat.is_le(Nat.add(i, n), String.length(CD.letters(r, a0, b0))) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(U32.to_nat(U32.from_nat(i)), U32.to_nat(U32.from_nat(n))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0))))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, hi) : {Nat.is_le(Nat.add(_, U32.to_nat(U32.from_nat(n))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0))))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, hn) : {Nat.is_le(Nat.add(i, _), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0))))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0)))), String.length(CD.letters(r, a0, b0)), hl) : {Nat.is_le(Nat.add(i, n), _) == True{} : Bool}
  h

# The read's bytes (n >= 1), given enc_ok's parts for the window's letters.
def cx.s(+r: String, +a0: Nat, +b0: Nat, +a: Nat, +b: Nat, +k: Nat,
  +ha: {Nat.is_le(a0, a) == True{} : Bool},
  +hbd: {Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))) == True{} : Bool},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hn: {Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))) == 1n+k : Nat},
  +hok: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), E.depth(String.length(CD.letters(r, a0, b0)))) == True{} : Bool},
  +hview: {D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0)))) == E.codes(CD.letters(r, a0, b0)) : List<&2, U32>}) ->
  {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), U32.from_nat(Nat.sub(Nat.min(a, String.length(r)), Nat.min(a0, String.length(r)))), U32.from_nat(Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))))))) == CD.letters(r, a, b) : String}:
  +l = String.length(r)
  +lt = CD.letters(r, a0, b0)
  +LW = U32.from_nat(String.length(lt))
  +TW = PE.enc_t(lt)
  +i = Nat.sub(Nat.min(a, l), Nat.min(a0, l))
  +n = Nat.sub(Nat.min(b, l), Nat.min(a, l))
  +mb = Nat.min(b, l)
  +a2 = Nat.min(a, l)
  +off = Nat.min(a0, l)
  +hoff = X.min_mono(a0, a, l, ha)
  +ha2 = X.sub_pos(mb, a2, k, hn)
  +hsum = N.le_trans(Nat.add(i, n), Nat.sub(mb, off), String.length(lt),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.sub(mb, off)) == True{} : Bool}, Nat.sub(mb, off), Nat.add(i, n), Equal.sym(Nat, Nat.add(i, n), Nat.sub(mb, off), X.sub_add_sub(off, a2, mb, hoff, ha2)), N.le_refl(Nat.sub(mb, off))),
    AB.subst(Nat, z => {Nat.is_le(Nat.sub(mb, off), z) == True{} : Bool}, Nat.sub(Nat.min(b0, l), off), String.length(lt), Equal.sym(Nat, String.length(lt), Nat.sub(Nat.min(b0, l), off), len_letters(r, a0, b0)), X.sub_mono(mb, Nat.min(b0, l), off, hbd)))
  +hlt = X.le31_mono(String.length(lt), Nat.sub(b0, a0), letters_le(r, a0, b0), hv)
  +hfi = X.le31_fit(i, X.le31_mono(i, String.length(lt), X.le_add_l2(i, n, String.length(lt), hsum), hlt))
  +hfn = X.le31_fit(n, X.le31_mono(n, String.length(lt), X.le_add_r2(i, n, String.length(lt), hsum), hlt))
  +hfl = X.le31_fit(String.length(lt), hlt)
  %Equal.sym(List<&2, U32>, Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(LW, TW), U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l))), U32.from_nat(Nat.sub(Nat.min(b, l), Nat.min(a, l))))), D.slice(D.view(C.BT(LW, TW)), U32.to_nat(U32.from_nat(i)), U32.to_nat(U32.from_nat(n))),
    SM.to_list_view_t(LW, TW, E.depth(String.length(lt)), U32.from_nat(i), U32.from_nat(n), hok, cx.hs(r, a0, b0, a, b, i, n, hfi, hfn, hfl, hsum))) :
    {Norm.chars(_) == CD.letters(r, a, b) : String}
  %Equal.sym(List<&2, U32>, D.view(C.BT(LW, TW)), E.codes(lt), hview) : {Norm.chars(D.slice(_, U32.to_nat(U32.from_nat(i)), U32.to_nat(U32.from_nat(n)))) == CD.letters(r, a, b) : String}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, hfi) : {Norm.chars(D.slice(E.codes(lt), _, U32.to_nat(U32.from_nat(n)))) == CD.letters(r, a, b) : String}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, hfn) : {Norm.chars(D.slice(E.codes(lt), i, _)) == CD.letters(r, a, b) : String}
  %X.codes_drop(lt, i) : {Norm.chars(List.take(&2, U32, _, n)) == CD.letters(r, a, b) : String}
  %X.codes_take(String.drop(lt, i), n) : {Norm.chars(_) == CD.letters(r, a, b) : String}
  %Equal.sym(String, Norm.chars(E.codes(String.take(String.drop(lt, i), n))), String.take(String.drop(lt, i), n), Pair.snd({E.chars(E.codes(String.take(String.drop(lt, i), n))) == String.take(String.drop(lt, i), n) : String}, {Norm.chars(E.codes(String.take(String.drop(lt, i), n))) == String.take(String.drop(lt, i), n) : String}, PE.chars_codes(String.take(String.drop(lt, i), n)))) :
    {_ == CD.letters(r, a, b) : String}
  ws(r, a0, a, b0, b, ha, hbd)

def cx.e(+r: String, +a0: Nat, +b0: Nat, +a: Nat, +b: Nat, +k: Nat,
  +ha: {Nat.is_le(a0, a) == True{} : Bool},
  +hbd: {Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))) == True{} : Bool},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hn: {Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))) == 1n+k : Nat},
  h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), E.depth(String.length(CD.letters(r, a0, b0)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0)))) == E.codes(CD.letters(r, a0, b0)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a0, b0))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a0, b0)))) == String.length(CD.letters(r, a0, b0)) : Nat}))) ->
  {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), U32.from_nat(Nat.sub(Nat.min(a, String.length(r)), Nat.min(a0, String.length(r)))), U32.from_nat(Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))))))) == CD.letters(r, a, b) : String}:
  (h1, h234) = h
  (h2, h34) = h234
  cx.s(r, a0, b0, a, b, k, ha, hbd, hv, hn, h1, h2)

def cx.k(+n: Nat, +r: String, +a0: Nat, +b0: Nat, +a: Nat, +b: Nat,
  +ha: {Nat.is_le(a0, a) == True{} : Bool},
  +hbd: {Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))) == True{} : Bool},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hn: {Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))) == n : Nat}) ->
  {Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(U32.from_nat(String.length(CD.letters(r, a0, b0))), PE.enc_t(CD.letters(r, a0, b0))), U32.from_nat(Nat.sub(Nat.min(a, String.length(r)), Nat.min(a0, String.length(r)))), U32.from_nat(Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))))))) == CD.letters(r, a, b) : String}:
  match n:
    case 0n:
      cx.z(r, a0, b0, a, b, hn)
    case 1n+k:
      cx.e(r, a0, b0, a, b, k, ha, hbd, hv, hn, PE.enc_ok(CD.letters(r, a0, b0), letters_bytes(r, a0, b0, hbr), X.le31_mono(String.length(CD.letters(r, a0, b0)), Nat.sub(b0, a0), letters_le(r, a0, b0), hv)))

# A window read at once that holds the read: serve answers its letters.
def sv.kt(+fa: List<&2, B.Contig>, +c0: String, +a0: Nat, +b0: Nat, +c: String, +a: Nat, +b: Nat, +r: String,
  +hm: {B.Fasta.find(fa, c0) == Some{r} : Maybe<&2, String>},
  +hc: {String.eq(c0, c) == True{} : Bool},
  +ha: {Nat.is_le(a0, a) == True{} : Bool},
  +hbd: {Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))) == True{} : Bool},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hbr: {E.is_bytes(r) == True{} : Bool}) ->
  {Norm.serve.known(True{}, Norm.WKnown{c0, NR.of_str(c0), a0, b0, String.length(r), Nat.min(a0, String.length(r)), E.enc(CD.letters(r, a0, b0)), U32.from_nat(Nat.min(a0, String.length(r))), U32.from_nat(String.length(CD.letters(r, a0, b0))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, String.length(r), Nat.min(a0, String.length(r)), E.enc(CD.letters(r, a0, b0)), U32.from_nat(Nat.min(a0, String.length(r))), U32.from_nat(String.length(CD.letters(r, a0, b0))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, Some{CD.jtruth(fa, c, a, b)}, CD.wp.clen(fa, c)} : Norm.Sv}:
  +l = String.length(r)
  +lt = CD.letters(r, a0, b0)
  +LW = U32.from_nat(String.length(lt))
  +TW = PE.enc_t(lt)
  %WL.string_eq_sound(c0, c, hc) : {Norm.serve.known(True{}, Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Some{CD.jtruth(fa, _, a, b)}, CD.wp.clen(fa, _)} : Norm.Sv}
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm) : {Norm.serve.known(True{}, Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Some{CD.jtruth.k(_, a, b)}, CD.wp.clen.k(_)} : Norm.Sv}
  %Equal.sym(D.Bytes, E.enc(lt), C.BT(LW, TW), PE.enc_bt(lt)) : {Norm.serve.known(True{}, Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), _, U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), _, U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Some{J.Known{l, Nat.min(a, l), CD.letters(r, a, b)}}, l} : Norm.Sv}
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(LW, TW), U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l))), U32.from_nat(Nat.sub(Nat.min(b, l), Nat.min(a, l)))), (C.BT(LW, TW), Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(LW, TW), U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l))), U32.from_nat(Nat.sub(Nat.min(b, l), Nat.min(a, l)))))), SM.to_list_pair_t(LW, TW, U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l))), U32.from_nat(Nat.sub(Nat.min(b, l), Nat.min(a, l))))) :
    {Norm.serve.slice(c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0), Nat.min(a, l), _) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), C.BT(LW, TW), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Some{J.Known{l, Nat.min(a, l), CD.letters(r, a, b)}}, l} : Norm.Sv}
  Equal.cong(String, Norm.Sv, z => Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), C.BT(LW, TW), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Some{J.Known{l, Nat.min(a, l), z}}, l}, Norm.chars(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(LW, TW), U32.from_nat(Nat.sub(Nat.min(a, l), Nat.min(a0, l))), U32.from_nat(Nat.sub(Nat.min(b, l), Nat.min(a, l)))))), CD.letters(r, a, b),
    cx.k(Nat.sub(Nat.min(b, l), Nat.min(a, l)), r, a0, b0, a, b, ha, hbd, hv, hbr, {==}))


def sv.kh(+h: Bool, +fa: List<&2, B.Contig>, +c0: String, +a0: Nat, +b0: Nat, +c: String, +a: Nat, +b: Nat, +r: String,
  +hm: {B.Fasta.find(fa, c0) == Some{r} : Maybe<&2, String>},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hh: {Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r)))) == h : Bool}) ->
  {Norm.serve(CD.mkWin.k(Some{r}, c0, a0, b0, False{}), c, a, b) == Norm.Sv{CD.mkWin.k(Some{r}, c0, a0, b0, False{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, Some{r}), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r}))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, Some{r}), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r}))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match h:
    case True{}:
      +l = String.length(r)
      +lt = CD.letters(r, a0, b0)
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l))), True{}, hh) : {Norm.serve.known(_, Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      +hab = N.and_true_l(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l)), hh)
      sv.kt(fa, c0, a0, b0, c, a, b, r, hm, N.and_true_l(String.eq(c0, c), Nat.is_le(a0, a), hab), N.and_true_r(String.eq(c0, c), Nat.is_le(a0, a), hab),
        N.and_true_r(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l)), hh), hv, hbr)
    case False{}:
      +l = String.length(r)
      +lt = CD.letters(r, a0, b0)
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l))), False{}, hh) : {Norm.serve.known(_, Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, a, b) == Norm.Sv{Norm.WKnown{c0, NR.of_str(c0), a0, b0, l, Nat.min(a0, l), E.enc(lt), U32.from_nat(Nat.min(a0, l)), U32.from_nat(String.length(lt)), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a0, l)), Norm.fits31(l)), U32.from_nat(l), 0)}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      {==}

def sv.known(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +c0: String, +a0: Nat, +b0: Nat, +c: String, +a: Nat, +b: Nat,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {Norm.le31(Nat.sub(b0, a0)) == True{} : Bool},
  +hm: {B.Fasta.find(fa, c0) == m : Maybe<&2, String>}) ->
  {Norm.serve(CD.mkWin(fa, CD.WPKnown{c0, a0, b0}), c, a, b) == Norm.Sv{CD.mkWin(fa, CD.WPKnown{c0, a0, b0}), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, CD.WPKnown{c0, a0, b0}, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, CD.WPKnown{c0, a0, b0}, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), None{}, hm) : {Norm.serve(CD.mkWin.k(_, c0, a0, b0, False{}), c, a, b) == Norm.Sv{CD.mkWin.k(_, c0, a0, b0, False{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      {==}
    case Some{r}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm) : {Norm.serve(CD.mkWin.k(_, c0, a0, b0, False{}), c, a, b) == Norm.Sv{CD.mkWin.k(_, c0, a0, b0, False{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      sv.kh(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r})))), fa, c0, a0, b0, c, a, b, r, hm, hv, find_bytes(fa, c0, r, hb, hm), {==})

def sv.sh(+h: Bool, +fa: List<&2, B.Contig>, +c0: String, +a0: Nat, +b0: Nat, +c: String, +a: Nat, +b: Nat, +r: String,
  +hm: {B.Fasta.find(fa, c0) == Some{r} : Maybe<&2, String>},
  +hh: {Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r)))) == h : Bool}) ->
  {Norm.serve(CD.mkWin.k(Some{r}, c0, a0, b0, True{}), c, a, b) == Norm.Sv{CD.mkWin.k(Some{r}, c0, a0, b0, True{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, Some{r}), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r}))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, Some{r}), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r}))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match h:
    case True{}:
      +l = String.length(r)
      +lt = CD.letters(r, a0, b0)
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l))), True{}, hh) : {Norm.serve.str(_, c0, a0, b0, l, Nat.min(a0, l), lt, a, b) == Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      +hab = N.and_true_l(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l)), hh)
      %WL.string_eq_sound(c0, c, N.and_true_l(String.eq(c0, c), Nat.is_le(a0, a), hab)) : {Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Some{J.Known{l, Nat.min(a, l), String.take(String.drop(lt, Nat.sub(Nat.min(a, l), Nat.min(a0, l))), Nat.sub(Nat.min(b, l), Nat.min(a, l)))}}, l} == Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Some{CD.jtruth(fa, _, a, b)}, CD.wp.clen(fa, _)} : Norm.Sv}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm) : {Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Some{J.Known{l, Nat.min(a, l), String.take(String.drop(lt, Nat.sub(Nat.min(a, l), Nat.min(a0, l))), Nat.sub(Nat.min(b, l), Nat.min(a, l)))}}, l} == Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Some{CD.jtruth.k(_, a, b)}, CD.wp.clen.k(_)} : Norm.Sv}
      Equal.cong(String, Norm.Sv, z => Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Some{J.Known{l, Nat.min(a, l), z}}, l}, String.take(String.drop(lt, Nat.sub(Nat.min(a, l), Nat.min(a0, l))), Nat.sub(Nat.min(b, l), Nat.min(a, l))), CD.letters(r, a, b),
        ws(r, a0, a, b0, b, N.and_true_r(String.eq(c0, c), Nat.is_le(a0, a), hab), N.and_true_r(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l)), hh)))
    case False{}:
      +l = String.length(r)
      +lt = CD.letters(r, a0, b0)
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, l), Nat.min(b0, l))), False{}, hh) : {Norm.serve.str(_, c0, a0, b0, l, Nat.min(a0, l), lt, a, b) == Norm.Sv{Norm.WStr{c0, a0, b0, l, Nat.min(a0, l), lt}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      {==}

def sv.str(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +c0: String, +a0: Nat, +b0: Nat, +c: String, +a: Nat, +b: Nat,
  +hm: {B.Fasta.find(fa, c0) == m : Maybe<&2, String>}) ->
  {Norm.serve(CD.mkWin(fa, CD.WPStr{c0, a0, b0}), c, a, b) == Norm.Sv{CD.mkWin(fa, CD.WPStr{c0, a0, b0}), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, CD.WPStr{c0, a0, b0}, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, CD.WPStr{c0, a0, b0}, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), None{}, hm) : {Norm.serve(CD.mkWin.k(_, c0, a0, b0, True{}), c, a, b) == Norm.Sv{CD.mkWin.k(_, c0, a0, b0, True{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      {==}
    case Some{r}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), Some{r}, hm) : {Norm.serve(CD.mkWin.k(_, c0, a0, b0, True{}), c, a, b) == Norm.Sv{CD.mkWin.k(_, c0, a0, b0, True{}), Bool.pick(Maybe<&2, J.Ans>, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, Bool.and(Maybe.is_some(&2, String, _), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(_)), Nat.min(b0, CD.wp.clen.k(_))))), CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      sv.sh(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, CD.wp.clen.k(Some{r})), Nat.min(b0, CD.wp.clen.k(Some{r})))), fa, c0, a0, b0, c, a, b, r, hm, {==})

def sv.unk(+fa: List<&2, B.Contig>, +c0: String, +c: String, +a: Nat, +b: Nat, +q: Bool,
  +hq: {String.eq(c0, c) == q : Bool},
  +hv: {Maybe.is_none(&2, String, B.Fasta.find(fa, c0)) == True{} : Bool}) ->
  {Norm.serve(CD.mkWin(fa, CD.WPUnk{c0}), c, a, b) == Norm.Sv{CD.mkWin(fa, CD.WPUnk{c0}), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, CD.WPUnk{c0}, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, CD.WPUnk{c0}, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match q:
    case True{}:
      %Equal.sym(Bool, String.eq(c0, c), True{}, hq) : {Norm.serve.unk(_, c0) == Norm.Sv{Norm.WUnk{c0}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      %WL.string_eq_sound(c0, c, hq) : {Norm.Sv{Norm.WUnk{c0}, Some{J.Unknown{}}, 0n} == Norm.Sv{Norm.WUnk{c0}, Some{CD.jtruth(fa, _, a, b)}, CD.wp.clen(fa, _)} : Norm.Sv}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c0), None{}, none_of(B.Fasta.find(fa, c0), hv)) : {Norm.Sv{Norm.WUnk{c0}, Some{J.Unknown{}}, 0n} == Norm.Sv{Norm.WUnk{c0}, Some{CD.jtruth.k(_, a, b)}, CD.wp.clen.k(_)} : Norm.Sv}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(c0, c), False{}, hq) : {Norm.serve.unk(_, c0) == Norm.Sv{Norm.WUnk{c0}, Bool.pick(Maybe<&2, J.Ans>, _, Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, _, CD.wp.clen(fa, c), 0n)} : Norm.Sv}
      {==}

def sv.k(+fa: List<&2, B.Contig>, +wp: CD.WP, +c: String, +a: Nat, +b: Nat,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  {Norm.serve(CD.mkWin(fa, wp), c, a, b) == Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, wp, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, wp, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  match wp:
    case CD.WPNone{}:
      {==}
    case CD.WPUnk{c0}:
      sv.unk(fa, c0, c, a, b, String.eq(c0, c), {==}, hv)
    case CD.WPKnown{c0, a0, b0}:
      sv.known(B.Fasta.find(fa, c0), fa, c0, a0, b0, c, a, b, hb, hv, {==})
    case CD.WPStr{c0, a0, b0}:
      sv.str(B.Fasta.find(fa, c0), fa, c0, a0, b0, c, a, b, {==})

# E.reqs_ok tests le31 on every read.
def rok31_eq(+rs: List<&2, Pr.Req>) -> {E.reqs_ok(rs) == X.rok31(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{Pr.Req{c, a, b}, t}:
      Equal.cong(Bool, Bool, z => Bool.and(Norm.le31(Nat.sub(b, a)), z), E.reqs_ok(t), X.rok31(t), rok31_eq(t))

# ---------------------------------------------------------------------------
# against_hit
# ---------------------------------------------------------------------------

def ah.z0(+c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == False{} : Bool}) ->
  {Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}:
  %Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), False{}, hz) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, NF.same.if(_, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32))) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  {==}

def ah.v0(+c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == False{} : Bool}) ->
  {Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}:
  %Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), True{}, hz) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, NF.same.if(_, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32))) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)), (C.BT(bl, bt), (C.BT(cbl, cbt), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))))), SM.same_pair_t(bl, bt, cbl, cbt, s, 0, (e0 - s : U32))) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, _) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), False{}, hv) : {Norm.win.chrom(_, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  {==}

def ah.c0(+c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == False{} : Bool}) ->
  {Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}:
  %Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), True{}, hz) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, NF.same.if(_, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32))) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)), (C.BT(bl, bt), (C.BT(cbl, cbt), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))))), SM.same_pair_t(bl, bt, cbl, cbt, s, 0, (e0 - s : U32))) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, _) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), True{}, hv) : {Norm.win.chrom(_, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  %Equal.sym(Bool, Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), False{}, hc) : {Norm.win.cover(_, U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WNeed{}} : Norm.Wo}
  {==}

def ah.f0(+c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == False{} : Bool}) ->
  {Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}:
  %Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), True{}, hz) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, NF.same.if(_, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32))) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}
  %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)), (C.BT(bl, bt), (C.BT(cbl, cbt), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))))), SM.same_pair_t(bl, bt, cbl, cbt, s, 0, (e0 - s : U32))) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, _) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}
  %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), True{}, hv) : {Norm.win.chrom(_, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}
  %Equal.sym(Bool, Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), True{}, hc) : {Norm.win.cover(_, U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}
  %Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), False{}, hf) : {Norm.win.cover(True{}, _, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Norm.WMiss{}} : Norm.Wo}
  {==}

def ah.q(+c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool},
  +eqv: Bool,
  +hq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == eqv : Bool}) ->
  {Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}:
  %Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), True{}, hz) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, NF.same.if(_, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32))) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)), (C.BT(bl, bt), (C.BT(cbl, cbt), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))))), SM.same_pair_t(bl, bt, cbl, cbt, s, 0, (e0 - s : U32))) : {Norm.win.same(c, a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), pos, rs, rl, _) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), True{}, hv) : {Norm.win.chrom(_, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(Bool, Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), True{}, hc) : {Norm.win.cover(_, U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), True{}, hf) : {Norm.win.cover(True{}, _, c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), C.BT(bl, bt), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(D.Bytes & (D.Bytes & Bool), NF.refeq.k(U32.to_nat(rl), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}, BY.at(C.BT(bl, bt), rs), BY.at(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32))), (C.BT(bl, bt), (C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}))), H.rq_pair(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{})) : {Norm.win.ref(c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0), _) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  %Equal.sym(Bool, H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}), eqv, hq) : {Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, _, Norm.WHit{}, Norm.WMiss{})} == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), Bool.pick(Norm.Wr, eqv, Norm.WHit{}, Norm.WMiss{})} : Norm.Wo}
  {==}


# ---------------------------------------------------------------------------
# against_hit: the REF test passed means the String path's REF check passes
# ---------------------------------------------------------------------------

def f3.f(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hoff31: {Norm.fits31(Nat.min(a, String.length(r))) == True{} : Bool},
  +hL31: {Norm.fits31(String.length(r)) == True{} : Bool},
  +hfit1: {U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(String.length(r))) == True{} : Bool},
  +okrw: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool},
  +viewrw: {D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  +lt = CD.letters(r, a, b)
  +off = Nat.min(a, String.length(r))
  +l = String.length(r)
  +nr = U32.to_nat(rl)
  +st = Nat.sub(U32.to_nat(pos), 1n)
  +W31 = Nat.pow(2n, 31n)
  +toff = H.f31_eq(off, hoff31)
  +tLL = H.f31_eq(l, hL31)
  +ep = H.tpp(pos, hp)
  +tend = H.tend(pos, rl, bl, bt, bd, rs, hok, hr, hp, hps)
  +hlL = N.le_trans(String.length(lt), Nat.min(b, l), l,
    AB.subst(Nat, z => {Nat.is_le(z, Nat.min(b, l)) == True{} : Bool}, Nat.sub(Nat.min(b, l), Nat.min(a, l)), String.length(lt), Equal.sym(Nat, String.length(lt), Nat.sub(Nat.min(b, l), Nat.min(a, l)), len_letters(r, a, b)), X.sub_le(Nat.min(b, l), Nat.min(a, l))),
    H.min_le_r(b, l))
  +hl31 = X.le31_mono(String.length(lt), l, hlL, H.fits_le31(l, hL31))
  +tlen = X.le31_fit(String.length(lt), hl31)
  +hc1u = N.and_true_l(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), hcov)
  +hc2u = N.and_true_r(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), hcov)
  +c1a = Equal.trans(Bool, Nat.is_le(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat((pos - 1 : U32))), U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), True{}, Equal.sym(Bool, U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), Nat.is_le(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat((pos - 1 : U32))), U.is_le_to_nat(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32))), hc1u)
  +c1b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat((pos - 1 : U32))) == True{} : Bool}, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff, c1a)
  +c1 = AB.subst(Nat, z => {Nat.is_le(off, z) == True{} : Bool}, U32.to_nat((pos - 1 : U32)), st, ep, c1b)
  +hOl = AB.subst(Nat, z => {Nat.is_lt(z, W31) == True{} : Bool}, off, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff), H.f31_lt(off, hoff31))
  +hRl = AB.subst(Nat, z => {Nat.is_le(z, W31) == True{} : Bool}, String.length(lt), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen),
    N.lt_to_le(String.length(lt), W31, N.le_lt_trans(String.length(lt), l, W31, hlL, H.f31_lt(l, hL31))))
  +tsum0 = U.to_nat_add_fits_p(U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), H.sum32(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), hOl, hRl))
  +c2a = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), hc2u)
  +c2b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(st, nr), tend, c2a)
  +c2c = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), z) == True{} : Bool}, U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), Nat.add(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b))))), tsum0, c2b)
  +c2d = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(z, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))))) == True{} : Bool}, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff, c2c)
  +c2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(off, z)) == True{} : Bool}, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen, c2d)
  +c3a = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(U32.from_nat(l))), U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(l)), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(l)), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(U32.from_nat(l))), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), U32.from_nat(l))), hfit1)
  +c3b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(U32.from_nat(l))) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(st, nr), tend, c3a)
  +c3 = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), z) == True{} : Bool}, U32.to_nat(U32.from_nat(l)), l, tLL, c3b)
  +K0 = Nat.sub(st, off)
  +tq = Equal.trans(Nat, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), Nat.sub(U32.to_nat((pos - 1 : U32)), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), K0, U.to_nat_sub_le((pos - 1 : U32), U32.from_nat(Nat.min(a, String.length(r))), hc1u),
    Equal.trans(Nat, Nat.sub(U32.to_nat((pos - 1 : U32)), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), Nat.sub(st, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), K0,
      Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), U32.to_nat((pos - 1 : U32)), st, ep),
      Equal.cong(Nat, Nat, z => Nat.sub(st, z), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff)))
  +hj = H.sub_lin(st, off, nr, String.length(lt), c2, c1)
  +hj2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(z, nr), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b))))) == True{} : Bool}, K0, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), Equal.sym(Nat, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), K0, tq),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(K0, nr), z) == True{} : Bool}, String.length(lt), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen), hj))
  +hrql = H.rq_val(nr, bl, bt, bd, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), E.depth(String.length(lt)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}, hok, okrw, hr, hj2, hrq)
  +Y = D.slice(E.codes(lt), K0, nr)
  +hrql2 = AB.subst(Nat, z => {H.rql(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), D.slice(E.codes(lt), z, nr)) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), K0, tq,
    AB.subst(List<&2, U32>, z => {H.rql(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), D.slice(z, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), nr)) == True{} : Bool}, D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))), E.codes(lt), viewrw, hrql))
  +hvs = Equal.trans(Nat, List.length(&2, U32, D.view(C.BT(bl, bt))), D.size(C.BT(bl, bt)), U32.to_nat(bl), O.view_size_t(bl, bt, bd, hok), {==})
  +hlX = H.sl_len(D.view(C.BT(bl, bt)), U32.to_nat(rs), nr, AB.subst(Nat, z => {Nat.is_le(Nat.add(U32.to_nat(rs), nr), z) == True{} : Bool}, U32.to_nat(bl), List.length(&2, U32, D.view(C.BT(bl, bt))), Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(bl, bt))), U32.to_nat(bl), hvs), hr))
  +hlY = H.sl_len(E.codes(lt), K0, nr, AB.subst(Nat, z => {Nat.is_le(Nat.add(K0, nr), z) == True{} : Bool}, String.length(lt), List.length(&2, U32, E.codes(lt)), EL.length_codes(lt), hj))
  +hbc = Equal.trans(Bool, D.all_bytes(E.codes(lt)), E.is_bytes(lt), True{}, EL.bytes_codes(lt), letters_bytes(r, a, b, hbr))
  +hbq = H.bq(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), Y, hrql2, hu, H.ab_slice(E.codes(lt), K0, nr, hbc), Equal.trans(Nat, List.length(&2, U32, D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, List.length(&2, U32, Y), hlX, Equal.sym(Nat, List.length(&2, U32, Y), nr, hlY)))
  +S2 = String.take(String.drop(lt, K0), nr)
  +eY = Equal.sym(List<&2, U32>, E.codes(S2), Y, Equal.trans(List<&2, U32>, E.codes(S2), List.take(&2, U32, E.codes(String.drop(lt, K0)), nr), Y,
    X.codes_take(String.drop(lt, K0), nr), Equal.cong(List<&2, U32>, List<&2, U32>, z => List.take(&2, U32, z, nr), E.codes(String.drop(lt, K0)), List.drop(&2, U32, E.codes(lt), K0), X.codes_drop(lt, K0))))
  +eC = Equal.trans(String, Norm.chars(Y), Norm.chars(E.codes(S2)), S2, Equal.cong(List<&2, U32>, String, z => Norm.chars(z), Y, E.codes(S2), eY),
    Pair.snd({E.chars(E.codes(S2)) == S2 : String}, {Norm.chars(E.codes(S2)) == S2 : String}, PE.chars_codes(S2)))
  +eF = Equal.trans(List<&2, B.Base>, B.Bases.of_fasta(S2), List.take(&2, B.Base, B.Bases.of_fasta(String.drop(lt, K0)), nr), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr),
    WL.of_fasta_take(String.drop(lt, K0), nr), Equal.cong(List<&2, B.Base>, List<&2, B.Base>, z => List.take(&2, B.Base, z, nr), B.Bases.of_fasta(String.drop(lt, K0)), List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), WL.of_fasta_drop(lt, K0)))
  +heq = AB.subst(List<&2, B.Base>, z => {B.Bases.eq(z, CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == True{} : Bool}, B.Bases.of_fasta(Norm.chars(Y)), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr),
    Equal.trans(List<&2, B.Base>, B.Bases.of_fasta(Norm.chars(Y)), B.Bases.of_fasta(S2), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr), Equal.cong(String, List<&2, B.Base>, z => B.Bases.of_fasta(z), Norm.chars(Y), S2, eC), eF), hbq)
  +hnb = Equal.trans(Nat, List.length(&2, B.Base, CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), List.length(&2, U32, D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, H.len_bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), hlX)
  +c2f = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(off, z)) == True{} : Bool}, String.length(lt), List.length(&2, B.Base, B.Bases.of_fasta(lt)), Equal.sym(Nat, List.length(&2, B.Base, B.Bases.of_fasta(lt)), String.length(lt), WL.of_fasta_len(lt)), c2)
  H.rc(l, off, B.Bases.of_fasta(lt), st, CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, hnb, c3, c1, c2f, heq)

def f3.e(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hoff31: {Norm.fits31(Nat.min(a, String.length(r))) == True{} : Bool},
  +hL31: {Norm.fits31(String.length(r)) == True{} : Bool},
  +hfit1: {U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(String.length(r))) == True{} : Bool},
  h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}))) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  (h1, h234) = h
  (h2, h34) = h234
  f3.f(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, hoff31, hL31, hfit1, h1, h2)

def f3.k(+fb: Bool, +r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hfb: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == fb : Bool},
  +hfit: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  match fb:
    case True{}:
      +hfit1 = AB.subst(Bool, z => {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, z, U32.from_nat(String.length(r)), 0)) == True{} : Bool}, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}, hfb, hfit)
      +hl31 = X.le31_mono(String.length(CD.letters(r, a, b)), String.length(r), N.le_trans(String.length(CD.letters(r, a, b)), Nat.min(b, String.length(r)), String.length(r),
        AB.subst(Nat, z => {Nat.is_le(z, Nat.min(b, String.length(r))) == True{} : Bool}, Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), String.length(CD.letters(r, a, b)), Equal.sym(Nat, String.length(CD.letters(r, a, b)), Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), len_letters(r, a, b)), X.sub_le(Nat.min(b, String.length(r)), Nat.min(a, String.length(r)))),
        H.min_le_r(b, String.length(r))), H.fits_le31(String.length(r), N.and_true_r(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb)))
      f3.e(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, N.and_true_l(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb), N.and_true_r(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb), hfit1,
        PE.enc_ok(CD.letters(r, a, b), letters_bytes(r, a, b, hbr), hl31))
    case False{}:
      +nr = U32.to_nat(rl)
      +hfit0 = AB.subst(Bool, z => {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, z, U32.from_nat(String.length(r)), 0)) == True{} : Bool}, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), False{}, hfb, hfit)
      +n0 = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U32.is_le(((pos - 1 : U32) + rl : U32), 0), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), 0), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), 0)), hfit0)
      +n1 = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(0)) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), H.tend(pos, rl, bl, bt, bd, rs, hok, hr, hp, hps), n0)
      +ez = N.add_eq_zero_r(Nat.sub(U32.to_nat(pos), 1n), nr, X.le_zero_eq(Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), n1))
      +hlt = Equal.trans(Bool, Nat.is_lt(U32.to_nat(0), nr), U32.is_lt(0, rl), True{}, Equal.sym(Bool, U32.is_lt(0, rl), Nat.is_lt(U32.to_nat(0), nr), U.is_lt_to_nat(0, rl)), hrl)
      Empty.absurd({J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}, N.false_ne_true(AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(0), z) == True{} : Bool}, nr, 0n, ez, hlt)))

def f3(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hfit: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  f3.k(Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, {==}, hfit)


def ah.lq(+eqv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool},
  +hq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == eqv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  match eqv:
    case True{}:
      (Norm.WHit{}, (ah.q(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf, True{}, hq),
        (H.f2(bl, bt, bd, s, e0, c, cbl, cbt, cbd, hok, okcb, htx, hs, he, hz, hv),
          f3(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hc, hq, hf))))
    case False{}:
      (Norm.WMiss{}, (ah.q(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf, False{}, hq), ({==}, {==})))

def ah.lf(+fv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == fv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  match fv:
    case True{}:
      ah.lq(H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, hc, hf, {==})
    case False{}:
      (Norm.WMiss{}, (ah.f0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf), ({==}, {==})))

def ah.lc(+cv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == cv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  match cv:
    case True{}:
      ah.lf(U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, hc, {==})
    case False{}:
      (Norm.WNeed{}, (ah.c0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc), ({==}, {==})))

def ah.lv(+v: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == v : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  match v:
    case True{}:
      ah.lc(Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, {==})
    case False{}:
      (Norm.WNeed{}, (ah.v0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv), ({==}, {==})))

def ah.lz(+z: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == z : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  match z:
    case True{}:
      ah.lv(Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, {==})
    case False{}:
      (Norm.WNeed{}, (ah.z0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz), ({==}, {==})))

# The window the picture stands for, with its buffers as mirrors.
def ah.mk(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +cbl: U32, +cbt: AT.Tree<U32>,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +eos: {NR.of_str(c) == C.BT(cbl, cbt) : D.Bytes}) ->
  {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}:
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin.k(_, c, a, b, False{}) : Norm.Win}
  %Equal.sym(D.Bytes, NR.of_str(c), C.BT(cbl, cbt), eos) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == Norm.WKnown{c, _, a, b, String.length(r), Nat.min(a, String.length(r)), E.enc(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} : Norm.Win}
  %Equal.sym(D.Bytes, E.enc(CD.letters(r, a, b)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), PE.enc_bt(CD.letters(r, a, b))) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), _, U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} : Norm.Win}
  {==}

def ah.m(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  g: &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>}))) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  (w, rest) = g
  (e1, cs) = rest
  (w, (AB.subst(Norm.Win, x => {Norm.against(x, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{x, C.BT(bl, bt), w} : Norm.Wo}, Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, a, b}), emk, e1), cs))

def ah.o(+cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +eos: {NR.of_str(c) == C.BT(cbl, cbt) : D.Bytes},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  ah.m(fa, c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, ah.mk(fa, c, a, b, r, cbl, cbt, hf, eos),
    ah.lz(U32.is_eq((e0 - s : U32), cbl), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, {==}))

def ah.k(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  h: &l: U32 -> &t: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(c) == C.BT(l, t) : D.Bytes} & ({D.ok(C.BT(l, t), d) == True{} : Bool} & {NR.chars(D.view(C.BT(l, t))) == c : String}))) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  (cbl, h1) = h
  (cbt, h2) = h1
  (cbd, h3) = h2
  (eos, h4) = h3
  (okcb, htx) = h4
  ah.o(cbl, cbt, cbd, fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, hbr, hf, hok, hs, he, hr, hu, hp, hps, hrl, eos, okcb, htx)

def ah.top(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  ah.k(fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, find_bytes(fa, c, r, hb, hf), hf, hok, hs, he, hr, hu, hp, hps, hrl, H.ofs(c, hcb, hcl))

# jtruth_ok, for the contig found (m).
def jt_k(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +m: Maybe<&2, String>,
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  {WS.truthful(fa, c, Some{CD.jtruth.k(m, a, b)}) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {Maybe.is_none(&2, String, _) == True{} : Bool}
      {==}
    case Some{r}:
      +n = String.length(r)
      +raw = CD.letters(r, a, b)
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) :
        {WS.known.ok(_, n, Nat.min(a, n), raw) == True{} : Bool}
      %Equal.sym(String, String.drop(r, Nat.min(a, n)), String.drop(r, a), X.drop_min(r, a)) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, String.take(_, String.length(raw)))) == True{} : Bool}
      %Equal.sym(String, String.take(String.drop(r, a), String.length(raw)), raw, X.take_len_take(String.drop(r, a), Nat.sub(b, a))) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, _)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.eq_refl(n)) : {Bool.and(_, String.eq(raw, raw)) == True{} : Bool}
      X.str_eq_refl(raw)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# The reads of a window: each within 2^31 letters, at least one, and all but
# the last full (so a window of n letters takes at most n / 2^31 + 1 reads).
def parts_ok(+c: String, +a: Nat, +b: Nat) ->
  {E.reqs_ok(Norm.parts(c, a, b)) == True{} : Bool}
  & ({Nat.is_le(1n, List.length(&2, Pr.Req, Norm.parts(c, a, b))) == True{} : Bool}
  & {Nat.is_le(List.length(&2, Pr.Req, Norm.parts(c, a, b)), Nat.max(1n, Nat.sub(b, a))) == True{} : Bool}):
  +x = Nat.sub(b, a)
  (Equal.trans(Bool, E.reqs_ok(Norm.parts(c, a, b)), X.rok31(Norm.parts(c, a, b)), True{}, rok31_eq(Norm.parts(c, a, b)),
      X.p31(x, Norm.le31(x), c, a, b, {==}, N.le_refl(x))),
    (X.pl1(x, Norm.le31(x), c, a, b),
      X.pmax(x, Norm.le31(x), c, a, b, {==}, N.le_refl(x))))

# The answers to a window's reads, kept: the window of the picture wpOf
# (a picture the machine can have).
def win_truths(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  hb: {CD.fa_bytes(fa) == True{} : Bool}) ->
  {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
  & {CD.wp_ok(fa, CD.wpOf(fa, c, a, b)) == True{} : Bool}:
  (wt.k(B.Fasta.find(fa, c), Norm.le31(Nat.sub(b, a)), fa, c, a, b, hb, {==}, {==}),
    wo.k(B.Fasta.find(fa, c), fa, c, a, b, {==}))

# serve answers truthfully from a window that holds the read, and leaves the
# window as it was; else it answers nothing.
def serve_ok(+fa: List<&2, B.Contig>, +wp: CD.WP, +c: String, +a: Nat, +b: Nat,
  hb: {CD.fa_bytes(fa) == True{} : Bool},
  hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  {Norm.serve(CD.mkWin(fa, wp), c, a, b) ==
    Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, wp, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, wp, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  sv.k(fa, wp, c, a, b, hb, hv)

# After asking Req.of(c, a, e), the window (CD.wpReq) holds the read (a, e):
# the slow path's retry is answered.
def req_holds(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +e: Nat) ->
  {CD.holds(fa, CD.wpReq(fa, c, a, e), c, a, e) == True{} : Bool}:
  rq.p(fa, c, a, e, Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))))

# The truthful answer is truthful in the window laws' sense.
def jtruth_ok(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat) ->
  {WS.truthful(fa, c, Some{CD.jtruth(fa, c, a, b)}) == True{} : Bool}:
  jt_k(fa, c, a, b, B.Fasta.find(fa, c), {==})

# The fast path's window test: the window and the line's buffer are handed
# back; a hit means CHROM is the window's contig and the String path's REF
# check passes on the window's letters (REF: rl upper-case ACGTN bytes from
# rs, at least one; POS pos >= 1 and below 10^9, as its at most 9 digits
# make it).
def against_hit(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String,
  +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  hb: {CD.fa_bytes(fa) == True{} : Bool},
  hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  hu: {CD.up(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  hrl: {U32.is_lt(0, rl) == True{} : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo}
  & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String}
  & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>})):
  ah.top(fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, hb, hf, hcb, hcl, hok, hs, he, hr, hu, hp, hps, hrl)

# After asking the contig from 0 up to e (norm.bend slow.reqs, a grown
# window), every read (a, e) of that line is held.
def zero_holds(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +e: Nat) ->
  {CD.holds(fa, CD.wpOf(fa, c, 0n, e), c, a, e) == True{} : Bool}:
  wp_holds(fa, c, 0n, e, a, e, N.le_zero_l(a), N.le_refl(e))
