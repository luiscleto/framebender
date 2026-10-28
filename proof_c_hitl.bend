import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_base.bend as P
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_b_run_buf.bend as BF
import ../lawful-bytes/defs.bend as D
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C: facts the rewrite path's verdict needs (proof_c_judge.bend's
# fix_res hypotheses), on the alleles' bytes and the window. Every variable
# is reusable.

# ---------------------------------------------------------------------------
# A, C, G, T, N in either case are letters
# ---------------------------------------------------------------------------

def pa10(+x: U32, +e: Bool, +he: {U32.is_eq(x, 110) == e : Bool}, +h: {e == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 110, U.is_eq_true(x, 110, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      Empty.absurd({Char.is_alpha(Chr{x}) == True{} : Bool}, N.false_ne_true(h))

def pa9(+x: U32, +e: Bool, +he: {U32.is_eq(x, 116) == e : Bool}, +h: {Bool.or(e, U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 116, U.is_eq_true(x, 116, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa10(x, U32.is_eq(x, 110), {==}, h)

def pa8(+x: U32, +e: Bool, +he: {U32.is_eq(x, 103) == e : Bool}, +h: {Bool.or(Bool.or(e, U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 103, U.is_eq_true(x, 103, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa9(x, U32.is_eq(x, 116), {==}, h)

def pa7(+x: U32, +e: Bool, +he: {U32.is_eq(x, 99) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 99, U.is_eq_true(x, 99, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa8(x, U32.is_eq(x, 103), {==}, h)

def pa6(+x: U32, +e: Bool, +he: {U32.is_eq(x, 97) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 97, U.is_eq_true(x, 97, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa7(x, U32.is_eq(x, 99), {==}, h)

def pa5(+x: U32, +e: Bool, +he: {U32.is_eq(x, 78) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 78, U.is_eq_true(x, 78, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa6(x, U32.is_eq(x, 97), {==}, h)

def pa4(+x: U32, +e: Bool, +he: {U32.is_eq(x, 84) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 84, U.is_eq_true(x, 84, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa5(x, U32.is_eq(x, 78), {==}, h)

def pa3(+x: U32, +e: Bool, +he: {U32.is_eq(x, 71) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 71, U.is_eq_true(x, 71, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa4(x, U32.is_eq(x, 84), {==}, h)

def pa2(+x: U32, +e: Bool, +he: {U32.is_eq(x, 67) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 67, U.is_eq_true(x, 67, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa3(x, U32.is_eq(x, 71), {==}, h)

def pa1(+x: U32, +e: Bool, +he: {U32.is_eq(x, 65) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 67)), U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool}) ->
  {Char.is_alpha(Chr{x}) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(U32, x, 65, U.is_eq_true(x, 65, he)) : {Char.is_alpha(Chr{_}) == True{} : Bool}
      {==}
    case False{}:
      pa2(x, U32.is_eq(x, 67), {==}, h)

def isl_alpha(+x: U32, +h: {NX.isl(x) == True{} : Bool}) -> {Char.is_alpha(Chr{x}) == True{} : Bool}:
  pa1(x, U32.is_eq(x, 65), {==}, h)

law lets_all:
  for +ys: List<&2, U32>
  for +h: {Q.lets(ys) == True{} : Bool}
  {B.Text.all_letters(Norm.chars(ys)) == True{} : Bool}

def lets_all(ys, h):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, Char.is_alpha(Chr{y}), True{}, isl_alpha(y, N.and_true_l(NX.isl(y), Q.lets(t), h))) :
        {Bool.and(_, B.Text.all_letters(Norm.chars(t))) == True{} : Bool}
      lets_all(t, N.and_true_r(NX.isl(y), Q.lets(t), h))

law lets_letters:
  for +ys: List<&2, U32>
  for +h: {Q.lets(ys) == True{} : Bool}
  for +hn: {Nat.is_le(1n, List.length(&2, U32, ys)) == True{} : Bool}
  {B.Text.is_letters(Norm.chars(ys)) == True{} : Bool}

def lets_letters(ys, h, hn):
  match ys:
    case Nil{}:
      Empty.absurd({B.Text.is_letters(Norm.chars(Nil{})) == True{} : Bool}, N.false_ne_true(hn))
    case Con{+y, +t}:
      lets_all(Con{y, t}, h)

# ---------------------------------------------------------------------------
# The ALT alleles' texts
# ---------------------------------------------------------------------------

law read_strs:
  for +X: List<&2, U32>
  for +als: List<&2, NX.Ap>
  for +h: {Q.ALS_L(X, als) == True{} : Bool}
  {B.Alleles.read(Q.STRS(X, als)) == Some{Q.BFS(X, als)} : Maybe<&2, List<&2, List<&2, B.Base>>>}

def read_strs(X, als, h):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(Norm.chars(Q.SL(X, a))), Some{Q.BF(Q.SL(X, a))}, PE.read_bf(Q.SL(X, a), N.and_true_l(Q.lets(Q.SL(X, a)), Q.ALS_L(X, t), h))) :
        {B.Alleles.read.cons(_, B.Alleles.read(Q.STRS(X, t))) == Some{Q.BFS(X, a <> t)} : Maybe<&2, List<&2, List<&2, B.Base>>>}
      %Equal.sym(Maybe<&2, List<&2, List<&2, B.Base>>>, B.Alleles.read(Q.STRS(X, t)), Some{Q.BFS(X, t)}, read_strs(X, t, N.and_true_r(Q.lets(Q.SL(X, a)), Q.ALS_L(X, t), h))) :
        {B.Alleles.read.cons(Some{Q.BF(Q.SL(X, a))}, _) == Some{Q.BFS(X, a <> t)} : Maybe<&2, List<&2, List<&2, B.Base>>>}
      {==}

law ne_chars1:
  for +ys: List<&2, U32>
  for +hn: {Nat.is_le(1n, List.length(&2, U32, ys)) == True{} : Bool}
  {String.is_empty(Norm.chars(ys)) == False{} : Bool}

def ne_chars1(ys, hn):
  match ys:
    case Nil{}:
      Empty.absurd({String.is_empty(Norm.chars(Nil{})) == False{} : Bool}, N.false_ne_true(hn))
    case Con{+y, +t}:
      {==}

# An allele in X with a byte or more: its slice has a byte or more.
def sl_ne(+X: List<&2, U32>, +L: U32, +a: NX.Ap,
  +h1: {Nat.is_le(1n, U32.to_nat(NX.Ap.ln(a))) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(a)), U32.to_nat(NX.Ap.ln(a))), U32.to_nat(L)) == True{} : Bool},
  +hl: {Nat.is_le(U32.to_nat(L), List.length(&2, U32, X)) == True{} : Bool}) ->
  {Nat.is_le(1n, List.length(&2, U32, Q.SL(X, a))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, Q.SL(X, a)), U32.to_nat(NX.Ap.ln(a)), BF.slice_len(X, U32.to_nat(NX.Ap.st(a)), U32.to_nat(NX.Ap.ln(a)), N.le_trans(Nat.add(U32.to_nat(NX.Ap.st(a)), U32.to_nat(NX.Ap.ln(a))), U32.to_nat(L), List.length(&2, U32, X), h2, hl))) :
    {Nat.is_le(1n, _) == True{} : Bool}
  h1

# Each allele lies in X and has a byte or more: its text is not empty.
law strs_ne:
  for +X: List<&2, U32>
  for +L: U32
  for +als: List<&2, NX.Ap>
  for +h: {Q.ALS_IN(L, als) == True{} : Bool}
  for +hl: {Nat.is_le(U32.to_nat(L), List.length(&2, U32, X)) == True{} : Bool}
  {B.Text.any_empty(Q.STRS(X, als)) == False{} : Bool}

def strs_ne(X, L, als, h, hl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +A1 = Nat.is_le(1n, U32.to_nat(NX.Ap.ln(a)))
      +A2 = Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(a)), U32.to_nat(NX.Ap.ln(a))), U32.to_nat(L))
      +ha = N.and_true_l(Bool.and(A1, A2), Q.ALS_IN(L, t), h)
      %Equal.sym(Bool, String.is_empty(Norm.chars(Q.SL(X, a))), False{}, ne_chars1(Q.SL(X, a), sl_ne(X, L, a, N.and_true_l(A1, A2, ha), N.and_true_r(A1, A2, ha), hl))) :
        {Bool.or(_, B.Text.any_empty(Q.STRS(X, t))) == False{} : Bool}
      strs_ne(X, L, t, N.and_true_r(Bool.and(A1, A2), Q.ALS_IN(L, t), h), hl)

law strs_letters:
  for +X: List<&2, U32>
  for +L: U32
  for +als: List<&2, NX.Ap>
  for +h: {Q.ALS_IN(L, als) == True{} : Bool}
  for +hl: {Nat.is_le(U32.to_nat(L), List.length(&2, U32, X)) == True{} : Bool}
  for +hs: {Q.ALS_L(X, als) == True{} : Bool}
  {B.Text.any_not_letters(Q.STRS(X, als)) == False{} : Bool}

def strs_letters(X, L, als, h, hl, hs):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +A1 = Nat.is_le(1n, U32.to_nat(NX.Ap.ln(a)))
      +A2 = Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(a)), U32.to_nat(NX.Ap.ln(a))), U32.to_nat(L))
      +ha = N.and_true_l(Bool.and(A1, A2), Q.ALS_IN(L, t), h)
      %Equal.sym(Bool, B.Text.is_letters(Norm.chars(Q.SL(X, a))), True{}, lets_letters(Q.SL(X, a), N.and_true_l(Q.lets(Q.SL(X, a)), Q.ALS_L(X, t), hs), sl_ne(X, L, a, N.and_true_l(A1, A2, ha), N.and_true_r(A1, A2, ha), hl))) :
        {Bool.or(Bool.not(_), B.Text.any_not_letters(Q.STRS(X, t))) == False{} : Bool}
      strs_letters(X, L, t, N.and_true_r(Bool.and(A1, A2), Q.ALS_IN(L, t), h), hl, N.and_true_r(Q.lets(Q.SL(X, a)), Q.ALS_L(X, t), hs))

# ---------------------------------------------------------------------------
# The window
# ---------------------------------------------------------------------------

law bf_codes:
  for +s: String
  {Q.BF(E.codes(s)) == B.Bases.of_fasta(s) : List<&2, B.Base>}

def bf_codes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(List<&2, B.Base>, Q.BF(E.codes(t)), B.Bases.of_fasta(t), bf_codes(t)) :
        {Q.bf(x) <> _ == B.Bases.of_fasta(SCon{Chr{x}, t}) : List<&2, B.Base>}
      {==}

def RCC(+off: Nat, +bases: List<&2, B.Base>, +st: Nat, +ref: List<&2, B.Base>) -> Type:
  {Nat.is_le(off, st) == True{} : Bool} & {Nat.is_le(Nat.add(st, List.length(&2, B.Base, ref)), Nat.add(off, List.length(&2, B.Base, bases))) == True{} : Bool}

def rcc.k(+fits: Bool, +cov: Bool, +eq: Bool, +off: Nat, +bases: List<&2, B.Base>, +st: Nat, +ref: List<&2, B.Base>,
  +hc: {Bool.and(Nat.is_le(off, st), Nat.is_le(Nat.add(st, List.length(&2, B.Base, ref)), Nat.add(off, List.length(&2, B.Base, bases)))) == cov : Bool},
  +h: {J.ref_check.go(fits, cov, eq) == Some{True{}} : Maybe<&2, Bool>}) -> RCC(off, bases, st, ref):
  match fits cov:
    case False{} _:
      Empty.absurd(RCC(off, bases, st, ref), P.true_ne_false(Equal.cong(Maybe<&2, Bool>, Bool, m => Maybe.default(&2, Bool, m, False{}), Some{True{}}, Some{False{}}, Equal.sym(Maybe<&2, Bool>, Some{False{}}, Some{True{}}, h))))
    case True{} False{}:
      Empty.absurd(RCC(off, bases, st, ref), P.true_ne_false(Equal.cong(Maybe<&2, Bool>, Bool, m => Maybe.is_none(&2, Bool, m), None{}, Some{True{}}, h)))
    case True{} True{}:
      (N.and_true_l(Nat.is_le(off, st), Nat.is_le(Nat.add(st, List.length(&2, B.Base, ref)), Nat.add(off, List.length(&2, B.Base, bases))), hc),
       N.and_true_r(Nat.is_le(off, st), Nat.is_le(Nat.add(st, List.length(&2, B.Base, ref)), Nat.add(off, List.length(&2, B.Base, bases))), hc))

# A passed REF check: the window holds REF.
def rc_cov(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +st: Nat, +ref: List<&2, B.Base>,
  +h: {J.ref_check(clen, off, bases, st, ref) == Some{True{}} : Maybe<&2, Bool>}) -> RCC(off, bases, st, ref):
  +n = List.length(&2, B.Base, ref)
  rcc.k(Nat.is_le(Nat.add(st, n), clen), Bool.and(Nat.is_le(off, st), Nat.is_le(Nat.add(st, n), Nat.add(off, List.length(&2, B.Base, bases)))), B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(st, off)), n), ref), off, bases, st, ref, {==}, h)

law take_all:
  for +xs: List<&2, U32>
  {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}

def take_all(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, List.length(&2, U32, t)), t, take_all(t)) : {Con{x, _} == Con{x, t} : List<&2, U32>}
      {==}

law slice_all:
  for +xs: List<&2, U32>
  {D.slice(xs, 0n, List.length(&2, U32, xs)) == xs : List<&2, U32>}

def slice_all(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      take_all(Con{x, t})
