import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_var_lists.bend as VL
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import ./proof_b_alleles_spec.bend as SP
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The fast path's allele tests (norm_fast.bend: NF.alleles) against the
# String path: alleles that pass are read, written and normalized as they
# are; then J.fast gives Same for any reference answer whose REF check
# passes.
#
# Notation: a buffer is its mirror C.BT(len, t); n(x) is U32.to_nat(x).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# Bytes a .. b-1.
def sl(+xs: List<&2, U32>, +a: U32, +b: U32) -> List<&2, U32>:
  D.slice(xs, n(a), Nat.sub(n(b), n(a)))

# Every byte is an upper-case A, C, G, T or N.
def up(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      NF.is_base(x) && up(t)

# The base an upper-case letter byte names (N for anything else).
def lb(+x: U32) -> B.Base:
  Maybe.default(&2, B.Base, B.Base.of_letter(Chr{x}), B.N{})

def bases_of(xs: List<&2, U32>) -> List<&2, B.Base>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      lb(x) <> bases_of(t)

def bases_all(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, B.Base>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      bases_of(p) <> bases_all(t)

# REF's and the ALT alleles' bases.
def REF(+xs: List<&2, U32>, +s3: U32, +e3: U32) -> List<&2, B.Base>:
  bases_of(sl(xs, s3, e3))

def ALTS(+xs: List<&2, U32>, +s4: U32, +e4: U32) -> List<&2, List<&2, B.Base>>:
  bases_all(FD.split(sl(xs, s4, e4), 44))

# ---------------------------------------------------------------------------
# Proofs: the byte loops are described in proof_b_alleles_loop.bend (a list
# test LP.spec on the view), its consequences in proof_b_alleles_spec.bend;
# here they are lifted to Base lists and Strings.
# ---------------------------------------------------------------------------

def L32() -> Data:
  List<&2, U32>

def LL() -> Data:
  List<&2, List<&2, U32>>

def Bs() -> Data:
  List<&2, B.Base>

def Strs() -> Data:
  List<&2, String>

law up_eq:
  for +xs: L32()
  {up(xs) == LP.up(xs) : Bool}

def up_eq(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %up_eq(t) : {Bool.and(NF.is_base(x), up(t)) == Bool.and(NF.is_base(x), _) : Bool}
      {==}

# One byte that is a base
# =======================

def bc.e(-Q: U32 -> Type, +x: U32, +c: U32, +e: {U32.is_eq(x, c) == True{} : Bool}, q: Q(c)) -> Q(x):
  %Equal.sym(U32, x, c, U.is_eq_true(x, c, e)) : Q(_)
  q

def bc.go(-Q: U32 -> Type, +x: U32, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool,
  +e1: {U32.is_eq(x, 65) == b1 : Bool}, +e2: {U32.is_eq(x, 67) == b2 : Bool}, +e3: {U32.is_eq(x, 71) == b3 : Bool},
  +e4: {U32.is_eq(x, 84) == b4 : Bool}, +e5: {U32.is_eq(x, 78) == b5 : Bool},
  +h: {Bool.or(Bool.or(Bool.or(Bool.or(b1, b2), b3), b4), b5) == True{} : Bool},
  q65: Q(65), q67: Q(67), q71: Q(71), q84: Q(84), q78: Q(78)) -> Q(x):
  match b1 b2 b3 b4 b5:
    case True{} _ _ _ _:
      bc.e(Q, x, 65, e1, q65)
    case False{} True{} _ _ _:
      bc.e(Q, x, 67, e2, q67)
    case False{} False{} True{} _ _:
      bc.e(Q, x, 71, e3, q71)
    case False{} False{} False{} True{} _:
      bc.e(Q, x, 84, e4, q84)
    case False{} False{} False{} False{} True{}:
      bc.e(Q, x, 78, e5, q78)
    case False{} False{} False{} False{} False{}:
      Empty.absurd(Q(x), LS.ft(h))

# A fact about a base byte, from the five cases.
def base_cases(-Q: U32 -> Type, +x: U32, +h: {NF.is_base(x) == True{} : Bool},
  q65: Q(65), q67: Q(67), q71: Q(71), q84: Q(84), q78: Q(78)) -> Q(x):
  bc.go(Q, x, U32.is_eq(x, 65), U32.is_eq(x, 67), U32.is_eq(x, 71), U32.is_eq(x, 84), U32.is_eq(x, 78), {==}, {==}, {==}, {==}, {==}, h, q65, q67, q71, q84, q78)

law of_letter_lb:
  for +x: U32
  for +h: {NF.is_base(x) == True{} : Bool}
  {B.Base.of_letter(Chr{x}) == Some{lb(x)} : Maybe<&2, B.Base>}

def of_letter_lb(x, h):
  base_cases(y => {B.Base.of_letter(Chr{y}) == Some{lb(y)} : Maybe<&2, B.Base>}, x, h, {==}, {==}, {==}, {==}, {==})

law letter_lb:
  for +x: U32
  for +h: {NF.is_base(x) == True{} : Bool}
  {B.Base.letter(lb(x)) == Chr{x} : Char}

def letter_lb(x, h):
  base_cases(y => {B.Base.letter(lb(y)) == Chr{y} : Char}, x, h, {==}, {==}, {==}, {==}, {==})

law alpha_lb:
  for +x: U32
  for +h: {NF.is_base(x) == True{} : Bool}
  {Char.is_alpha(Chr{x}) == True{} : Bool}

def alpha_lb(x, h):
  base_cases(y => {Char.is_alpha(Chr{y}) == True{} : Bool}, x, h, {==}, {==}, {==}, {==}, {==})

def BEQ(+x: U32, +y: U32) -> Type:
  {B.Base.is_eq(lb(x), lb(y)) == U32.is_eq(x, y) : Bool}

law base_eq:
  for +x: U32
  for +y: U32
  for +hx: {NF.is_base(x) == True{} : Bool}
  for +hy: {NF.is_base(y) == True{} : Bool}
  BEQ(x, y)

def base_eq(x, y, hx, hy):
  base_cases(z => BEQ(z, y), x, hx,
    base_cases(z => BEQ(65, z), y, hy, {==}, {==}, {==}, {==}, {==}),
    base_cases(z => BEQ(67, z), y, hy, {==}, {==}, {==}, {==}, {==}),
    base_cases(z => BEQ(71, z), y, hy, {==}, {==}, {==}, {==}, {==}),
    base_cases(z => BEQ(84, z), y, hy, {==}, {==}, {==}, {==}, {==}),
    base_cases(z => BEQ(78, z), y, hy, {==}, {==}, {==}, {==}, {==}))

# Text of the bytes
# =================

def mapc(ps: LL()) -> Strs():
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Norm.chars(p) <> mapc(t)

def cs.k(+x: U32, +b: Bool, +r: LL()) -> {String.split.fin(Chr{x}, mapc(r), b) == mapc(FD.split.fin(x, r, b)) : Strs()}:
  match b r:
    case True{} _:
      {==}
    case False{} Nil{}:
      {==}
    case False{} Con{+h, +t}:
      {==}

# Splitting the text at commas: the text of the byte pieces.
law csplit:
  for +xs: L32()
  {String.split(Norm.chars(xs), ',') == mapc(FD.split(xs, 44)) : Strs()}

def csplit(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Strs(), String.split(Norm.chars(t), ','), mapc(FD.split(t, 44)), csplit(t)) :
        {String.split.fin(Chr{x}, _, U32.is_eq(x, 44)) == mapc(FD.split(x <> t, 44)) : Strs()}
      cs.k(x, U32.is_eq(x, 44), FD.split(t, 44))

def JG(+ps: LL()) -> String:
  String.join(mapc(ps), ",")

law jg_cons:
  for +L: Strs()
  for +c: Char
  for +s: String
  {String.join.go(L, SCon{c, s}, ",") == SCon{c, String.join.go(L, s, ",")} : String}

def jg_cons(L, c, s):
  match L:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

def jstep(+x: U32, +h: L32(), +r: LL(), +T: String, +b: Bool, +eb: {U32.is_eq(x, 44) == b : Bool}, +ih: {JG(Con{h, r}) == T : String}) ->
  {JG(FD.split.fin(x, Con{h, r}, b)) == SCon{Chr{x}, T} : String}:
  match b:
    case True{}:
      %Equal.sym(U32, x, 44, U.is_eq_true(x, 44, eb)) : {SCon{',', String.join.go(mapc(r), Norm.chars(h), ",")} == SCon{Chr{_}, T} : String}
      %ih : {SCon{',', String.join.go(mapc(r), Norm.chars(h), ",")} == SCon{',', _} : String}
      {==}
    case False{}:
      %Equal.sym(String, String.join.go(mapc(r), SCon{Chr{x}, Norm.chars(h)}, ","), SCon{Chr{x}, String.join.go(mapc(r), Norm.chars(h), ",")}, jg_cons(mapc(r), Chr{x}, Norm.chars(h))) :
        {_ == SCon{Chr{x}, T} : String}
      %ih : {SCon{Chr{x}, String.join.go(mapc(r), Norm.chars(h), ",")} == SCon{Chr{x}, _} : String}
      {==}

# Joining the text of the pieces with commas gives the text back.
law jsplit:
  for +xs: L32()
  {JG(FD.split(xs, 44)) == Norm.chars(xs) : String}

def jsplit(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = D.run_len(t, 44)
      +A = LS.take(t, r)
      +R = LS.tsplit(LS.drop(t, r), 44)
      %Equal.sym(LL(), FD.split(t, 44), LS.SR(t, 44), LS.split_run(t, 44)) :
        {JG(FD.split.fin(x, _, U32.is_eq(x, 44))) == SCon{Chr{x}, Norm.chars(t)} : String}
      jstep(x, A, R, Norm.chars(t), U32.is_eq(x, 44), {==},
        %LS.split_run(t, 44) : {JG(_) == Norm.chars(t) : String}; jsplit(t))

# Reading and writing alleles
# ===========================

law read_up:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  {B.Allele.read(Norm.chars(xs)) == Some{bases_of(xs)} : Maybe<&2, Bs()>}

def read_up(xs, hu):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LS.and_l(NF.is_base(x), LP.up(t), hu)
      +ht = LS.and_r(NF.is_base(x), LP.up(t), hu)
      %Equal.sym(Maybe<&2, B.Base>, B.Base.of_letter(Chr{x}), Some{lb(x)}, of_letter_lb(x, hx)) :
        {B.Allele.read.cons(_, B.Allele.read(Norm.chars(t))) == Some{lb(x) <> bases_of(t)} : Maybe<&2, Bs()>}
      %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(Norm.chars(t)), Some{bases_of(t)}, read_up(t, ht)) :
        {B.Allele.read.cons(Some{lb(x)}, _) == Some{lb(x) <> bases_of(t)} : Maybe<&2, Bs()>}
      {==}

law show_up:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  {B.Allele.show(bases_of(xs)) == Norm.chars(xs) : String}

def show_up(xs, hu):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LS.and_l(NF.is_base(x), LP.up(t), hu)
      +ht = LS.and_r(NF.is_base(x), LP.up(t), hu)
      %Equal.sym(Char, B.Base.letter(lb(x)), Chr{x}, letter_lb(x, hx)) : {SCon{_, B.Allele.show(bases_of(t))} == SCon{Chr{x}, Norm.chars(t)} : String}
      %Equal.sym(String, B.Allele.show(bases_of(t)), Norm.chars(t), show_up(t, ht)) : {SCon{Chr{x}, _} == SCon{Chr{x}, Norm.chars(t)} : String}
      {==}

law letters_up:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  {B.Text.all_letters(Norm.chars(xs)) == True{} : Bool}

def letters_up(xs, hu):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      SP.and_tt(Char.is_alpha(Chr{x}), B.Text.all_letters(Norm.chars(t)),
        alpha_lb(x, LS.and_l(NF.is_base(x), LP.up(t), hu)), letters_up(t, LS.and_r(NF.is_base(x), LP.up(t), hu)))

law is_letters_up:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  for +hn: {Nat.is_lt(0n, List.length(&2, U32, xs)) == True{} : Bool}
  {B.Text.is_letters(Norm.chars(xs)) == True{} : Bool}

def is_letters_up(xs, hu, hn):
  match xs:
    case Nil{}:
      Empty.absurd({B.Text.is_letters(Norm.chars(Nil{})) == True{} : Bool}, LS.ft(hn))
    case Con{+x, +t}:
      letters_up(x <> t, hu)

def UL(+q: L32()) -> Bool:
  Bool.and(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)))

law aread:
  for +ps: LL()
  for +h: {SP.allok(ps) == True{} : Bool}
  {B.Alleles.read(mapc(ps)) == Some{bases_all(ps)} : Maybe<&2, List<&2, Bs()>>}

def aread(ps, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), h)
      %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(Norm.chars(q)), Some{bases_of(q)}, read_up(q, LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq))) :
        {B.Alleles.read.cons(_, B.Alleles.read(mapc(t))) == Some{bases_of(q) <> bases_all(t)} : Maybe<&2, List<&2, Bs()>>}
      %Equal.sym(Maybe<&2, List<&2, Bs()>>, B.Alleles.read(mapc(t)), Some{bases_all(t)}, aread(t, LS.and_r(UL(q), SP.allok(t), h))) :
        {B.Alleles.read.cons(Some{bases_of(q)}, _) == Some{bases_of(q) <> bases_all(t)} : Maybe<&2, List<&2, Bs()>>}
      {==}

def ne.k(+q: L32(), +hn: {Nat.is_lt(0n, List.length(&2, U32, q)) == True{} : Bool}) -> {String.is_empty(Norm.chars(q)) == False{} : Bool}:
  match q:
    case Nil{}:
      Empty.absurd({String.is_empty(Norm.chars(Nil{})) == False{} : Bool}, LS.ft(hn))
    case Con{+x, +t}:
      {==}

law anyempty:
  for +ps: LL()
  for +h: {SP.allok(ps) == True{} : Bool}
  {B.Text.any_empty(mapc(ps)) == False{} : Bool}

def anyempty(ps, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), h)
      %Equal.sym(Bool, String.is_empty(Norm.chars(q)), False{}, ne.k(q, LS.and_r(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq))) :
        {Bool.or(_, B.Text.any_empty(mapc(t))) == False{} : Bool}
      anyempty(t, LS.and_r(UL(q), SP.allok(t), h))

law anynl:
  for +ps: LL()
  for +h: {SP.allok(ps) == True{} : Bool}
  {B.Text.any_not_letters(mapc(ps)) == False{} : Bool}

def anynl(ps, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), h)
      %Equal.sym(Bool, B.Text.is_letters(Norm.chars(q)), True{}, is_letters_up(q, LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq), LS.and_r(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq))) :
        {Bool.or(Bool.not(_), B.Text.any_not_letters(mapc(t))) == False{} : Bool}
      anynl(t, LS.and_r(UL(q), SP.allok(t), h))

law ashow:
  for +ps: LL()
  for +h: {SP.allok(ps) == True{} : Bool}
  {B.Alleles.show(bases_all(ps)) == mapc(ps) : Strs()}

def ashow(ps, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), h)
      %Equal.sym(String, B.Allele.show(bases_of(q)), Norm.chars(q), show_up(q, LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq))) : {_ <> B.Alleles.show(bases_all(t)) == Norm.chars(q) <> mapc(t) : Strs()}
      %Equal.sym(Strs(), B.Alleles.show(bases_all(t)), mapc(t), ashow(t, LS.and_r(UL(q), SP.allok(t), h))) : {Norm.chars(q) <> _ == Norm.chars(q) <> mapc(t) : Strs()}
      {==}

# Equal alleles
# =============

law beq:
  for +x: L32()
  for +y: L32()
  for +hx: {LP.up(x) == True{} : Bool}
  for +hy: {LP.up(y) == True{} : Bool}
  {B.Bases.eq(bases_of(x), bases_of(y)) == D.list_eq(x, y) : Bool}

def beq(x, y, hx, hy):
  match x y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +s}:
      {==}
    case Con{+a, +r} Nil{}:
      {==}
    case Con{+a, +r} Con{+b, +s}:
      %Equal.sym(Bool, B.Base.is_eq(lb(a), lb(b)), U32.is_eq(a, b), base_eq(a, b, LS.and_l(NF.is_base(a), LP.up(r), hx), LS.and_l(NF.is_base(b), LP.up(s), hy))) :
        {Bool.and(_, B.Bases.eq(bases_of(r), bases_of(s))) == Bool.and(U32.is_eq(a, b), D.list_eq(r, s)) : Bool}
      %Equal.sym(Bool, B.Bases.eq(bases_of(r), bases_of(s)), D.list_eq(r, s), beq(r, s, LS.and_r(NF.is_base(a), LP.up(r), hx), LS.and_r(NF.is_base(b), LP.up(s), hy))) :
        {Bool.and(U32.is_eq(a, b), _) == Bool.and(U32.is_eq(a, b), D.list_eq(r, s)) : Bool}
      {==}

law amemb:
  for +x: L32()
  for +ps: LL()
  for +hx: {LP.up(x) == True{} : Bool}
  for +hps: {SP.allok(ps) == True{} : Bool}
  {B.Alleles.member(bases_of(x), bases_all(ps)) == LP.memb(x, ps) : Bool}

def amemb(x, ps, hx, hps):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), hps)
      %Equal.sym(Bool, B.Bases.eq(bases_of(x), bases_of(q)), D.list_eq(x, q), beq(x, q, hx, LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq))) :
        {Bool.or(_, B.Alleles.member(bases_of(x), bases_all(t))) == Bool.or(D.list_eq(x, q), LP.memb(x, t)) : Bool}
      %Equal.sym(Bool, B.Alleles.member(bases_of(x), bases_all(t)), LP.memb(x, t), amemb(x, t, hx, LS.and_r(UL(q), SP.allok(t), hps))) :
        {Bool.or(D.list_eq(x, q), _) == Bool.or(D.list_eq(x, q), LP.memb(x, t)) : Bool}
      {==}

law adist:
  for +ps: LL()
  for +hps: {SP.allok(ps) == True{} : Bool}
  {B.Alleles.distinct(bases_all(ps)) == SP.dist(ps) : Bool}

def adist(ps, hps):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), hps)
      +ht = LS.and_r(UL(q), SP.allok(t), hps)
      %Equal.sym(Bool, B.Alleles.member(bases_of(q), bases_all(t)), LP.memb(q, t), amemb(q, t, LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq), ht)) :
        {Bool.and(Bool.not(_), B.Alleles.distinct(bases_all(t))) == Bool.and(Bool.not(LP.memb(q, t)), SP.dist(t)) : Bool}
      %Equal.sym(Bool, B.Alleles.distinct(bases_all(t)), SP.dist(t), adist(t, ht)) :
        {Bool.and(Bool.not(LP.memb(q, t)), _) == Bool.and(Bool.not(LP.memb(q, t)), SP.dist(t)) : Bool}
      {==}

# First and last bases, lengths
# =============================

law lgo:
  for +t: L32()
  for +x: U32
  {List.last.go(&2, B.Base, bases_of(t), lb(x)) == lb(LP.lastb(t, x)) : B.Base}

def lgo(t, x):
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      lgo(r, y)

law last_of:
  for +xs: L32()
  for +hn: {Nat.is_lt(0n, List.length(&2, U32, xs)) == True{} : Bool}
  {List.last(&2, B.Base, bases_of(xs)) == Some{lb(LP.lastb(xs, 0))} : Maybe<&2, B.Base>}

def last_of(xs, hn):
  match xs:
    case Nil{}:
      Empty.absurd({List.last(&2, B.Base, bases_of(Nil{})) == Some{lb(LP.lastb(Nil{}, 0))} : Maybe<&2, B.Base>}, LS.ft(hn))
    case Con{+x, +t}:
      %Equal.sym(B.Base, List.last.go(&2, B.Base, bases_of(t), lb(x)), lb(LP.lastb(t, x)), lgo(t, x)) : {Some{_} == Some{lb(LP.lastb(t, x))} : Maybe<&2, B.Base>}
      {==}

law head_of:
  for +xs: L32()
  for +hn: {Nat.is_lt(0n, List.length(&2, U32, xs)) == True{} : Bool}
  {List.head(&2, B.Base, bases_of(xs)) == Some{lb(LP.headb(xs, 0))} : Maybe<&2, B.Base>}

def head_of(xs, hn):
  match xs:
    case Nil{}:
      Empty.absurd({List.head(&2, B.Base, bases_of(Nil{})) == Some{lb(LP.headb(Nil{}, 0))} : Maybe<&2, B.Base>}, LS.ft(hn))
    case Con{+x, +t}:
      {==}

law upl:
  for +t: L32()
  for +x: U32
  for +hx: {NF.is_base(x) == True{} : Bool}
  for +hu: {LP.up(t) == True{} : Bool}
  {NF.is_base(LP.lastb(t, x)) == True{} : Bool}

def upl(t, x, hx, hu):
  match t:
    case Nil{}:
      hx
    case Con{+y, +r}:
      upl(r, y, LS.and_l(NF.is_base(y), LP.up(r), hu), LS.and_r(NF.is_base(y), LP.up(r), hu))

law up_last:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  for +hn: {Nat.is_lt(0n, List.length(&2, U32, xs)) == True{} : Bool}
  {NF.is_base(LP.lastb(xs, 0)) == True{} : Bool}

def up_last(xs, hu, hn):
  match xs:
    case Nil{}:
      Empty.absurd({NF.is_base(LP.lastb(Nil{}, 0)) == True{} : Bool}, LS.ft(hn))
    case Con{+x, +t}:
      upl(t, x, LS.and_l(NF.is_base(x), LP.up(t), hu), LS.and_r(NF.is_base(x), LP.up(t), hu))

law up_head:
  for +xs: L32()
  for +hu: {LP.up(xs) == True{} : Bool}
  for +hn: {Nat.is_lt(0n, List.length(&2, U32, xs)) == True{} : Bool}
  {NF.is_base(LP.headb(xs, 0)) == True{} : Bool}

def up_head(xs, hu, hn):
  match xs:
    case Nil{}:
      Empty.absurd({NF.is_base(LP.headb(Nil{}, 0)) == True{} : Bool}, LS.ft(hn))
    case Con{+x, +t}:
      LS.and_l(NF.is_base(x), LP.up(t), hu)

law lenb:
  for +xs: L32()
  {List.length(&2, B.Base, bases_of(xs)) == List.length(&2, U32, xs) : Nat}

def lenb(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat, List.length(&2, B.Base, bases_of(t)), List.length(&2, U32, t), lenb(t)) : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
      {==}

law slast:
  for +z3: U32
  for +ps: LL()
  for +hz: {NF.is_base(z3) == True{} : Bool}
  for +hps: {SP.allok(ps) == True{} : Bool}
  {V.same_last(Some{lb(z3)}, bases_all(ps)) == SP.lasts(z3, ps) : Bool}

def slast(z3, ps, hz, hps):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), hps)
      +hu = LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq)
      +hn = LS.and_r(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq)
      +z = LP.lastb(q, 0)
      %Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, bases_of(q)), Some{lb(z)}, last_of(q, hn)) :
        {Bool.and(V.opt_eq(Some{lb(z3)}, _), V.same_last(Some{lb(z3)}, bases_all(t))) == Bool.and(U32.is_eq(z, z3), SP.lasts(z3, t)) : Bool}
      %Equal.sym(Bool, B.Base.is_eq(lb(z3), lb(z)), U32.is_eq(z3, z), base_eq(z3, z, hz, up_last(q, hu, hn))) :
        {Bool.and(_, V.same_last(Some{lb(z3)}, bases_all(t))) == Bool.and(U32.is_eq(z, z3), SP.lasts(z3, t)) : Bool}
      %SP.u32_eq_sym(z, z3) :
        {Bool.and(_, V.same_last(Some{lb(z3)}, bases_all(t))) == Bool.and(U32.is_eq(z, z3), SP.lasts(z3, t)) : Bool}
      %Equal.sym(Bool, V.same_last(Some{lb(z3)}, bases_all(t)), SP.lasts(z3, t), slast(z3, t, hz, LS.and_r(UL(q), SP.allok(t), hps))) :
        {Bool.and(U32.is_eq(z, z3), _) == Bool.and(U32.is_eq(z, z3), SP.lasts(z3, t)) : Bool}
      {==}

law sfirst:
  for +f3: U32
  for +ps: LL()
  for +hf: {NF.is_base(f3) == True{} : Bool}
  for +hps: {SP.allok(ps) == True{} : Bool}
  {V.same_first(Some{lb(f3)}, bases_all(ps)) == SP.firsts(f3, ps) : Bool}

def sfirst(f3, ps, hf, hps):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +hq = LS.and_l(UL(q), SP.allok(t), hps)
      +hu = LS.and_l(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq)
      +hn = LS.and_r(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)), hq)
      +z = LP.headb(q, 0)
      %Equal.sym(Maybe<&2, B.Base>, List.head(&2, B.Base, bases_of(q)), Some{lb(z)}, head_of(q, hn)) :
        {Bool.and(V.opt_eq(Some{lb(f3)}, _), V.same_first(Some{lb(f3)}, bases_all(t))) == Bool.and(U32.is_eq(z, f3), SP.firsts(f3, t)) : Bool}
      %Equal.sym(Bool, B.Base.is_eq(lb(f3), lb(z)), U32.is_eq(f3, z), base_eq(f3, z, hf, up_head(q, hu, hn))) :
        {Bool.and(_, V.same_first(Some{lb(f3)}, bases_all(t))) == Bool.and(U32.is_eq(z, f3), SP.firsts(f3, t)) : Bool}
      %SP.u32_eq_sym(z, f3) :
        {Bool.and(_, V.same_first(Some{lb(f3)}, bases_all(t))) == Bool.and(U32.is_eq(z, f3), SP.firsts(f3, t)) : Bool}
      %Equal.sym(Bool, V.same_first(Some{lb(f3)}, bases_all(t)), SP.firsts(f3, t), sfirst(f3, t, hf, LS.and_r(UL(q), SP.allok(t), hps))) :
        {Bool.and(U32.is_eq(z, f3), _) == Bool.and(U32.is_eq(z, f3), SP.firsts(f3, t)) : Bool}
      {==}

law slong:
  for +ps: LL()
  {V.all_long(bases_all(ps)) == SP.longs(ps) : Bool}

def slong(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      %Equal.sym(Nat, List.length(&2, B.Base, bases_of(q)), List.length(&2, U32, q), lenb(q)) :
        {Bool.and(Nat.is_le(2n, _), V.all_long(bases_all(t))) == Bool.and(Nat.is_le(2n, List.length(&2, U32, q)), SP.longs(t)) : Bool}
      %Equal.sym(Bool, V.all_long(bases_all(t)), SP.longs(t), slong(t)) :
        {Bool.and(Nat.is_le(2n, List.length(&2, U32, q)), _) == Bool.and(Nat.is_le(2n, List.length(&2, U32, q)), SP.longs(t)) : Bool}
      {==}

# The normalizer stops at once
# ============================

law right_stop:
  for +fuel: Nat
  for +off: Nat
  for +bases: Bs()
  for +pos: Nat
  for +als: List<&2, Bs()>
  {V.right(fuel, V.AStop{}, off, bases, pos, als) == Some{V.Cur{pos, als}} : Maybe<&2, V.Cur>}

def right_stop(fuel, off, bases, pos, als):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

law left_stop:
  for +fuel: Nat
  for +pos: Nat
  for +als: List<&2, Bs()>
  {V.left(fuel, False{}, pos, als) == V.Cur{pos, als} : V.Cur}

def left_stop(fuel, pos, als):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

# Not all ending with the same base, and not (all starting with the same base
# and all long): var_in leaves the variant as it is.
law vin:
  for +off: Nat
  for +bases: Bs()
  for +p: Nat
  for +r: Bs()
  for +a: List<&2, Bs()>
  for +h1: {V.lasts_eq(r <> a) == False{} : Bool}
  for +h2: {Bool.and(V.firsts_eq(r <> a), V.all_long(r <> a)) == False{} : Bool}
  {V.var_in(off, bases, B.Var{p, r, a}) == Some{B.Var{p, r, a}} : Maybe<&2, B.Var>}

def vin(off, bases, p, r, a, h1, h2):
  +als = {r <> a : List<&2, Bs()>}
  +fuel = Nat.add(p, V.total(als))
  %Equal.sym(Bool, V.lasts_eq(als), False{}, h1) :
    {V.left_of(V.right(fuel, V.next_act.if(_, V.all_long(als), Nat.is_le(2n, p), V.Win.get(off, bases, Nat.sub(p, 2n))), off, bases, p, als)) == Some{B.Var{p, r, a}} : Maybe<&2, B.Var>}
  %Equal.sym(Maybe<&2, V.Cur>, V.right(fuel, V.AStop{}, off, bases, p, als), Some{V.Cur{p, als}}, right_stop(fuel, off, bases, p, als)) :
    {V.left_of(_) == Some{B.Var{p, r, a}} : Maybe<&2, B.Var>}
  %Equal.sym(Bool, Bool.and(V.firsts_eq(als), V.all_long(als)), False{}, h2) :
    {Some{V.to_var(V.left(fuel, _, p, als))} == Some{B.Var{p, r, a}} : Maybe<&2, B.Var>}
  %Equal.sym(V.Cur, V.left(fuel, False{}, p, als), V.Cur{p, als}, left_stop(fuel, p, als)) :
    {Some{V.to_var(_)} == Some{B.Var{p, r, a}} : Maybe<&2, B.Var>}
  {==}

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# Alleles that pass NF.alleles: what the String path reads and writes.
def alleles_pass.go(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s3: U32, +e3: U32, +s4: U32, +e4: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h3: {Nat.is_le(n(s3), n(e3)) == True{} : Bool},
  +h34: {Nat.is_le(n(e3), n(s4)) == True{} : Bool},
  +h4: {Nat.is_le(n(s4), n(e4)) == True{} : Bool},
  +hl: {Nat.is_le(n(e4), n(len)) == True{} : Bool},
  +hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}) ->
  {B.Allele.read(Norm.chars(sl(xs(len, t), s3, e3))) == Some{REF(xs(len, t), s3, e3)} : Maybe<&2, List<&2, B.Base>>}
  & ({B.Alleles.read(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == Some{ALTS(xs(len, t), s4, e4)} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  & ({B.Text.is_letters(Norm.chars(sl(xs(len, t), s3, e3))) == True{} : Bool}
  & ({B.Text.any_empty(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Text.any_not_letters(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Allele.show(REF(xs(len, t), s3, e3)) == Norm.chars(sl(xs(len, t), s3, e3)) : String}
  & ({String.join(B.Alleles.show(ALTS(xs(len, t), s4, e4)), ",") == Norm.chars(sl(xs(len, t), s4, e4)) : String}
  & ({B.Alleles.distinct(REF(xs(len, t), s3, e3) <> ALTS(xs(len, t), s4, e4)) == True{} : Bool}
  & ({up(sl(xs(len, t), s3, e3)) == True{} : Bool}
  & {Nat.is_lt(n(s3), n(e3)) == True{} : Bool})))))))):
  +X0 = xs(len, t)
  +R = sl(X0, s3, e3)
  +A = sl(X0, s4, e4)
  +Ps = FD.split(A, 44)
  +he3 = N.le_trans(n(e3), n(s4), n(len), h34, N.le_trans(n(s4), n(e4), n(len), h4, hl))
  +eg = LP.go_true(len, t, d, s3, e3, s4, e4, hok, h3, he3, hp)
  +g1 = LS.and_l(Bool.and(LP.up(R), U32.is_lt(s3, e3)), U32.is_lt(s4, e4), eg)
  +hu = LS.and_l(LP.up(R), U32.is_lt(s3, e3), g1)
  +h33 = LP.lt_n(s3, e3, LS.and_r(LP.up(R), U32.is_lt(s3, e3), g1))
  +hRn = {%Equal.sym(Nat, List.length(&2, U32, R), Nat.sub(n(e3), n(s3)), LP.len_bs(len, t, d, s3, e3, hok, h3, he3)) : {Nat.is_lt(0n, _) == True{} : Bool}; LP.pos_sub(n(s3), n(e3), h33) : {Nat.is_lt(0n, List.length(&2, U32, R)) == True{} : Bool}}
  +hsp = LP.alleles_spec(len, t, d, s3, e3, s4, e4, hok, h3, h4, he3, hl, hp)
  +Z = LP.Z3(len, t, s3, e3)
  +F = C.AT(len, t, s3)
  +G0 = U32.is_le(2, LP.L3(s3, e3))
  +hokp = SP.sp_ok(Ps, [R], Z, F, True{}, True{}, G0, hsp)
  +hd = SP.sp_dist(Ps, [R], Z, F, True{}, True{}, G0, hsp)
  +hdP = LS.and_l(SP.dist(Ps), SP.notin([R], Ps), hd)
  +hnR = LS.and_l(Bool.not(LP.memb(R, Ps)), True{}, LS.and_r(SP.dist(Ps), SP.notin([R], Ps), hd))
  +hokRP = SP.and_tt(UL(R), SP.allok(Ps), SP.and_tt(LP.up(R), Nat.is_lt(0n, List.length(&2, U32, R)), hu, hRn), hokp)
  (read_up(R, hu),
  (%Equal.sym(Strs(), String.split(Norm.chars(A), ','), mapc(Ps), csplit(A)) : {B.Alleles.read(_) == Some{ALTS(X0, s4, e4)} : Maybe<&2, List<&2, Bs()>>}; aread(Ps, hokp),
  (is_letters_up(R, hu, hRn),
  (%Equal.sym(Strs(), String.split(Norm.chars(A), ','), mapc(Ps), csplit(A)) : {B.Text.any_empty(_) == False{} : Bool}; anyempty(Ps, hokp),
  (%Equal.sym(Strs(), String.split(Norm.chars(A), ','), mapc(Ps), csplit(A)) : {B.Text.any_not_letters(_) == False{} : Bool}; anynl(Ps, hokp),
  (show_up(R, hu),
  (%Equal.sym(Strs(), B.Alleles.show(bases_all(Ps)), mapc(Ps), ashow(Ps, hokp)) : {String.join(_, ",") == Norm.chars(A) : String}; jsplit(A),
  (%Equal.sym(Bool, B.Alleles.distinct(bases_all(R <> Ps)), SP.dist(R <> Ps), adist(R <> Ps, hokRP)) : {_ == True{} : Bool}; SP.and_tt(Bool.not(LP.memb(R, Ps)), SP.dist(Ps), hnR, hdP),
  (%Equal.sym(Bool, up(R), LP.up(R), up_eq(R)) : {_ == True{} : Bool}; hu,
  h33)))))))))

def alleles_pass(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s3: U32, +e3: U32, +s4: U32, +e4: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  h3: {Nat.is_le(n(s3), n(e3)) == True{} : Bool},
  h34: {Nat.is_le(n(e3), n(s4)) == True{} : Bool},
  h4: {Nat.is_le(n(s4), n(e4)) == True{} : Bool},
  hl: {Nat.is_le(n(e4), n(len)) == True{} : Bool},
  hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}) ->
  {B.Allele.read(Norm.chars(sl(xs(len, t), s3, e3))) == Some{REF(xs(len, t), s3, e3)} : Maybe<&2, List<&2, B.Base>>}
  & ({B.Alleles.read(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == Some{ALTS(xs(len, t), s4, e4)} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  & ({B.Text.is_letters(Norm.chars(sl(xs(len, t), s3, e3))) == True{} : Bool}
  & ({B.Text.any_empty(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Text.any_not_letters(String.split(Norm.chars(sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Allele.show(REF(xs(len, t), s3, e3)) == Norm.chars(sl(xs(len, t), s3, e3)) : String}
  & ({String.join(B.Alleles.show(ALTS(xs(len, t), s4, e4)), ",") == Norm.chars(sl(xs(len, t), s4, e4)) : String}
  & ({B.Alleles.distinct(REF(xs(len, t), s3, e3) <> ALTS(xs(len, t), s4, e4)) == True{} : Bool}
  & ({up(sl(xs(len, t), s3, e3)) == True{} : Bool}
  & {Nat.is_lt(n(s3), n(e3)) == True{} : Bool})))))))):
  alleles_pass.go(len, t, d, s3, e3, s4, e4, hok, h3, h34, h4, hl, hp)

# Alleles that pass NF.alleles are left as they are by the normalizer,
# whatever the window.
def alleles_norm.go(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s3: U32, +e3: U32, +s4: U32, +e4: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h3: {Nat.is_le(n(s3), n(e3)) == True{} : Bool},
  +h34: {Nat.is_le(n(e3), n(s4)) == True{} : Bool},
  +h4: {Nat.is_le(n(s4), n(e4)) == True{} : Bool},
  +hl: {Nat.is_le(n(e4), n(len)) == True{} : Bool},
  +hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool},
  +off: Nat, +bases: List<&2, B.Base>, +p: Nat) ->
  {V.var_in(off, bases, B.Var{p, REF(xs(len, t), s3, e3), ALTS(xs(len, t), s4, e4)}) == Some{B.Var{p, REF(xs(len, t), s3, e3), ALTS(xs(len, t), s4, e4)}} : Maybe<&2, B.Var>}:
  +X0 = xs(len, t)
  +R = sl(X0, s3, e3)
  +A = sl(X0, s4, e4)
  +Ps = FD.split(A, 44)
  +he3 = N.le_trans(n(e3), n(s4), n(len), h34, N.le_trans(n(s4), n(e4), n(len), h4, hl))
  +eg = LP.go_true(len, t, d, s3, e3, s4, e4, hok, h3, he3, hp)
  +g1 = LS.and_l(Bool.and(LP.up(R), U32.is_lt(s3, e3)), U32.is_lt(s4, e4), eg)
  +hu = LS.and_l(LP.up(R), U32.is_lt(s3, e3), g1)
  +h33 = LP.lt_n(s3, e3, LS.and_r(LP.up(R), U32.is_lt(s3, e3), g1))
  +hRn = {%Equal.sym(Nat, List.length(&2, U32, R), Nat.sub(n(e3), n(s3)), LP.len_bs(len, t, d, s3, e3, hok, h3, he3)) : {Nat.is_lt(0n, _) == True{} : Bool}; LP.pos_sub(n(s3), n(e3), h33) : {Nat.is_lt(0n, List.length(&2, U32, R)) == True{} : Bool}}
  +hsp = LP.alleles_spec(len, t, d, s3, e3, s4, e4, hok, h3, h4, he3, hl, hp)
  +Z = LP.Z3(len, t, s3, e3)
  +F = C.AT(len, t, s3)
  +G0 = U32.is_le(2, LP.L3(s3, e3))
  +hokp = SP.sp_ok(Ps, [R], Z, F, True{}, True{}, G0, hsp)
  +hfl = SP.sp_flags(Ps, [R], Z, F, True{}, True{}, G0, hsp)
  +hL = LS.not_t(SP.lasts(Z, Ps), LS.and_l(Bool.not(SP.lasts(Z, Ps)), Bool.not(Bool.and(SP.firsts(F, Ps), Bool.and(G0, SP.longs(Ps)))), hfl))
  +hFG = LS.not_t(Bool.and(SP.firsts(F, Ps), Bool.and(G0, SP.longs(Ps))), LS.and_r(Bool.not(SP.lasts(Z, Ps)), Bool.not(Bool.and(SP.firsts(F, Ps), Bool.and(G0, SP.longs(Ps)))), hfl))
  +hhd = LP.hd_at(len, t, d, s3, e3, hok, h33, he3)
  +hF = {%hhd : {NF.is_base(_) == True{} : Bool}; up_head(R, hu, hRn) : {NF.is_base(F) == True{} : Bool}}
  vin(off, bases, p, REF(X0, s3, e3), ALTS(X0, s4, e4),
    %Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, bases_of(R)), Some{lb(Z)}, last_of(R, hRn)) : {V.same_last(_, bases_all(Ps)) == False{} : Bool};
    %Equal.sym(Bool, V.same_last(Some{lb(Z)}, bases_all(Ps)), SP.lasts(Z, Ps), slast(Z, Ps, up_last(R, hu, hRn), hokp)) : {_ == False{} : Bool};
    hL,
    %Equal.sym(Maybe<&2, B.Base>, List.head(&2, B.Base, bases_of(R)), Some{lb(LP.headb(R, 0))}, head_of(R, hRn)) :
      {Bool.and(V.same_first(_, bases_all(Ps)), Bool.and(Nat.is_le(2n, List.length(&2, B.Base, bases_of(R))), V.all_long(bases_all(Ps)))) == False{} : Bool};
    %Equal.sym(U32, LP.headb(R, 0), F, hhd) : {Bool.and(V.same_first(Some{lb(_)}, bases_all(Ps)), Bool.and(Nat.is_le(2n, List.length(&2, B.Base, bases_of(R))), V.all_long(bases_all(Ps)))) == False{} : Bool};
    %Equal.sym(Bool, V.same_first(Some{lb(F)}, bases_all(Ps)), SP.firsts(F, Ps), sfirst(F, Ps, hF, hokp)) :
      {Bool.and(_, Bool.and(Nat.is_le(2n, List.length(&2, B.Base, bases_of(R))), V.all_long(bases_all(Ps)))) == False{} : Bool};
    %Equal.sym(Nat, List.length(&2, B.Base, bases_of(R)), List.length(&2, U32, R), lenb(R)) :
      {Bool.and(SP.firsts(F, Ps), Bool.and(Nat.is_le(2n, _), V.all_long(bases_all(Ps)))) == False{} : Bool};
    %Equal.sym(Bool, Nat.is_le(2n, List.length(&2, U32, R)), G0, LP.ge2(len, t, d, s3, e3, hok, h3, he3)) :
      {Bool.and(SP.firsts(F, Ps), Bool.and(_, V.all_long(bases_all(Ps)))) == False{} : Bool};
    %Equal.sym(Bool, V.all_long(bases_all(Ps)), SP.longs(Ps), slong(Ps)) :
      {Bool.and(SP.firsts(F, Ps), Bool.and(G0, _)) == False{} : Bool};
    hFG)

def alleles_norm(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s3: U32, +e3: U32, +s4: U32, +e4: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  h3: {Nat.is_le(n(s3), n(e3)) == True{} : Bool},
  h34: {Nat.is_le(n(e3), n(s4)) == True{} : Bool},
  h4: {Nat.is_le(n(s4), n(e4)) == True{} : Bool},
  hl: {Nat.is_le(n(e4), n(len)) == True{} : Bool},
  hp: {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), True{}) : D.Bytes & Bool},
  +off: Nat, +bases: List<&2, B.Base>, +p: Nat) ->
  {V.var_in(off, bases, B.Var{p, REF(xs(len, t), s3, e3), ALTS(xs(len, t), s4, e4)}) == Some{B.Var{p, REF(xs(len, t), s3, e3), ALTS(xs(len, t), s4, e4)}} : Maybe<&2, B.Var>}:
  alleles_norm.go(len, t, d, s3, e3, s4, e4, hok, h3, h34, h4, hl, hp, off, bases, p)


# J.fast on a record whose first 8 fields are these (INFO as J.pfs keeps
# it, passing the END check), with the alleles' facts above and a passed REF
# check: Same. (String level only.)
def fast_same(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String,
  +body: String, +p: Nat, +r: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +clen: Nat, +off: Nat, +raw: String,
  h0: {String.is_empty(f0) == False{} : Bool},
  h1: {B.Pos.read(f1) == Some{p} : Maybe<&2, Nat>},
  h1s: {Nat.show(p) == f1 : String},
  hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  hr: {B.Allele.read(f3) == Some{r} : Maybe<&2, List<&2, B.Base>>},
  ha: {B.Alleles.read(String.split(f4, ',')) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  hl: {B.Text.is_letters(f3) == True{} : Bool},
  he: {B.Text.any_empty(String.split(f4, ',')) == False{} : Bool},
  hn: {B.Text.any_not_letters(String.split(f4, ',')) == False{} : Bool},
  hs3: {B.Allele.show(r) == f3 : String},
  hs4: {String.join(B.Alleles.show(alts), ",") == f4 : String},
  hd: {B.Alleles.distinct(r <> alts) == True{} : Bool},
  hv: {V.var_in(off, B.Bases.of_fasta(raw), B.Var{p, r, alts}) == Some{B.Var{p, r, alts}} : Maybe<&2, B.Var>},
  hc: {J.ref_check(clen, off, B.Bases.of_fasta(raw), Nat.sub(p, 1n), r) == Some{True{}} : Maybe<&2, Bool>},
  hend: {J.end_ok(f7, Nat.sub(Nat.add(p, String.length(f3)), 1n)) == True{} : Bool}) ->
  {J.fast(Some{J.Known{clen, off, raw}}, [f0, f1, f2, f3, f4, f5, f6, f7], body) == J.Same{} : J.Fast}:
  +e1 = Equal.sym(Maybe<&2, Nat>, B.Pos.read(f1), Some{p}, h1)
  +a = {Some{J.Known{clen, off, raw}} : Maybe<&2, J.Ans>}
  +FS = {[f0, f1, f2, f3, f4, f5, f6, f7] : List<&2, String>}
  +s4 = String.split(f4, ',')
  %Equal.sym(Bool, String.is_empty(f0), False{}, h0) :
    {J.fast.go(Bool.or(Bool.or(Bool.or(_, Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1)))), Bool.not(B.Text.is_letters(f3))), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Text.is_letters(f3), True{}, hl) :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1))), Bool.not(_)), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == J.Same{} : J.Fast}
  %e1 :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, _)), False{}), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Text.any_empty(s4), False{}, he) :
    {J.fast.go(_, B.Text.any_not_letters(s4), a, FS, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Text.any_not_letters(s4), False{}, hn) :
    {J.fast.go(False{}, _, a, FS, body) == J.Same{} : J.Fast}
  +bs = B.Bases.of_fasta(raw)
  +E1 = Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(f1), 0n), String.length(f3)), 1n)
  +hend1 = AB.subst(Maybe<&2, Nat>, z => {J.end_ok(f7, Nat.sub(Nat.add(Maybe.default(&2, Nat, z, 0n), String.length(f3)), 1n)) == True{} : Bool}, Some{p}, B.Pos.read(f1), e1, hend)
  %Equal.sym(Bool, J.end_ok(f7, E1), True{}, hend1) :
    {J.fast.found(_, B.Allele.read(f3), B.Alleles.read(s4), clen, off, bs, Maybe.default(&2, Nat, B.Pos.read(f1), 0n), f1, f3, f4, body) == J.Same{} : J.Fast}
  %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(f3), Some{r}, hr) :
    {J.fast.found(True{}, _, B.Alleles.read(s4), clen, off, bs, Maybe.default(&2, Nat, B.Pos.read(f1), 0n), f1, f3, f4, body) == J.Same{} : J.Fast}
  %Equal.sym(Maybe<&2, List<&2, List<&2, B.Base>>>, B.Alleles.read(s4), Some{alts}, ha) :
    {J.fast.found(True{}, Some{r}, _, clen, off, bs, Maybe.default(&2, Nat, B.Pos.read(f1), 0n), f1, f3, f4, body) == J.Same{} : J.Fast}
  %e1 :
    {J.fast.found(True{}, Some{r}, Some{alts}, clen, off, bs, Maybe.default(&2, Nat, _, 0n), f1, f3, f4, body) == J.Same{} : J.Fast}
  +v = {B.Var{p, r, alts} : B.Var}
  %Equal.sym(Bool, Nat.is_eq(p, 0n), False{}, hz) :
    {J.fast.problem(_, B.Alleles.distinct(r <> alts), clen, off, bs, f1, f3, f4, v, p, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Alleles.distinct(r <> alts), True{}, hd) :
    {J.fast.problem(False{}, _, clen, off, bs, f1, f3, f4, v, p, body) == J.Same{} : J.Fast}
  %Equal.sym(Maybe<&2, Bool>, J.ref_check(clen, off, bs, Nat.sub(p, 1n), r), Some{True{}}, hc) :
    {J.fast.ref(_, off, bs, f1, f3, f4, v, p, body) == J.Same{} : J.Fast}
  %Equal.sym(Maybe<&2, B.Var>, V.var_in(off, bs, v), Some{v}, hv) :
    {J.fast.norm(_, f1, f3, f4, v, body) == J.Same{} : J.Fast}
  +sh4 = String.join(B.Alleles.show(alts), ",")
  %h1s : {J.fast.norm.k(Bool.and(B.Rec.same_var(v, v), J.same.text(_, f3, f4, v)), v, v, body) == J.Same{} : J.Fast}
  %hs3 : {J.fast.norm.k(Bool.and(B.Rec.same_var(v, v), J.same.text(Nat.show(p), _, f4, v)), v, v, body) == J.Same{} : J.Fast}
  %hs4 : {J.fast.norm.k(Bool.and(B.Rec.same_var(v, v), J.same.text(Nat.show(p), B.Allele.show(r), _, v)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, Nat.is_eq(p, p), True{}, P.eq_refl(p)) :
    {J.fast.norm.k(Bool.and(Bool.and(Bool.and(_, B.Bases.eq(r, r)), B.Alleles.eq(alts, alts)), J.same.text(Nat.show(p), B.Allele.show(r), sh4, v)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Bases.eq(r, r), True{}, VL.bases_refl(r)) :
    {J.fast.norm.k(Bool.and(Bool.and(_, B.Alleles.eq(alts, alts)), J.same.text(Nat.show(p), B.Allele.show(r), sh4, v)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, B.Alleles.eq(alts, alts), True{}, VL.alleles_refl(alts)) :
    {J.fast.norm.k(Bool.and(_, J.same.text(Nat.show(p), B.Allele.show(r), sh4, v)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, String.eq(Nat.show(p), Nat.show(p)), True{}, Q.str_eq_refl(Nat.show(p))) :
    {J.fast.norm.k(Bool.and(Bool.and(_, String.eq(B.Allele.show(r), B.Allele.show(r))), String.eq(sh4, sh4)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, String.eq(B.Allele.show(r), B.Allele.show(r)), True{}, Q.str_eq_refl(B.Allele.show(r))) :
    {J.fast.norm.k(Bool.and(_, String.eq(sh4, sh4)), v, v, body) == J.Same{} : J.Fast}
  %Equal.sym(Bool, String.eq(sh4, sh4), True{}, Q.str_eq_refl(sh4)) :
    {J.fast.norm.k(_, v, v, body) == J.Same{} : J.Fast}
  {==}
