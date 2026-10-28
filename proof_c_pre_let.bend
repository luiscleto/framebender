import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_b_alleles_list.bend as LS
import ../lawful-bytes/defs.bend as D
import ../lawful-words/proof_u32.bend as U

# Letters A, C, G, T, N in either case (NX.isl): their bases (Q.bf), the
# letters written for them, and their comparison up to case; Strings of
# bytes compared with String.eq.

# ---------------------------------------------------------------------------
# One letter
# ---------------------------------------------------------------------------

def lc.e(-R: U32 -> Type, +x: U32, +c: U32, +e: {U32.is_eq(x, c) == True{} : Bool}, q: R(c)) -> R(x):
  %Equal.sym(U32, x, c, U.is_eq_true(x, c, e)) : R(_)
  q

def lc.go(-R: U32 -> Type, +x: U32, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool,
  +e1: {U32.is_eq(x, 65) == b1 : Bool}, +e2: {U32.is_eq(x, 67) == b2 : Bool}, +e3: {U32.is_eq(x, 71) == b3 : Bool},
  +e4: {U32.is_eq(x, 84) == b4 : Bool}, +e5: {U32.is_eq(x, 78) == b5 : Bool}, +e6: {U32.is_eq(x, 97) == b6 : Bool},
  +e7: {U32.is_eq(x, 99) == b7 : Bool}, +e8: {U32.is_eq(x, 103) == b8 : Bool}, +e9: {U32.is_eq(x, 116) == b9 : Bool},
  +e10: {U32.is_eq(x, 110) == b10 : Bool},
  +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(b1, b2), b3), b4), b5), b6), b7), b8), b9), b10) == True{} : Bool},
  q65: R(65), q67: R(67), q71: R(71), q84: R(84), q78: R(78), q97: R(97), q99: R(99), q103: R(103), q116: R(116), q110: R(110)) -> R(x):
  match b1 b2 b3 b4 b5 b6 b7 b8 b9 b10:
    case True{} _ _ _ _ _ _ _ _ _:
      lc.e(R, x, 65, e1, q65)
    case False{} True{} _ _ _ _ _ _ _ _:
      lc.e(R, x, 67, e2, q67)
    case False{} False{} True{} _ _ _ _ _ _ _:
      lc.e(R, x, 71, e3, q71)
    case False{} False{} False{} True{} _ _ _ _ _ _:
      lc.e(R, x, 84, e4, q84)
    case False{} False{} False{} False{} True{} _ _ _ _ _:
      lc.e(R, x, 78, e5, q78)
    case False{} False{} False{} False{} False{} True{} _ _ _ _:
      lc.e(R, x, 97, e6, q97)
    case False{} False{} False{} False{} False{} False{} True{} _ _ _:
      lc.e(R, x, 99, e7, q99)
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      lc.e(R, x, 103, e8, q103)
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      lc.e(R, x, 116, e9, q116)
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      lc.e(R, x, 110, e10, q110)
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      Empty.absurd(R(x), LS.ft(h))

# A fact about a letter byte, from the ten cases.
def isl_cases(-R: U32 -> Type, +x: U32, +h: {NX.isl(x) == True{} : Bool},
  q65: R(65), q67: R(67), q71: R(71), q84: R(84), q78: R(78), q97: R(97), q99: R(99), q103: R(103), q116: R(116), q110: R(110)) -> R(x):
  lc.go(R, x, U32.is_eq(x, 65), U32.is_eq(x, 67), U32.is_eq(x, 71), U32.is_eq(x, 84), U32.is_eq(x, 78), U32.is_eq(x, 97), U32.is_eq(x, 99), U32.is_eq(x, 103), U32.is_eq(x, 116), U32.is_eq(x, 110),
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, h, q65, q67, q71, q84, q78, q97, q99, q103, q116, q110)

def OL(+x: U32) -> Type:
  {B.Base.of_letter(Chr{x}) == Some{Q.bf(x)} : Maybe<&2, B.Base>}

def of_letter_bf(+x: U32, +h: {NX.isl(x) == True{} : Bool}) -> OL(x):
  isl_cases(y => OL(y), x, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# The letter written for a letter's base is the letter itself when upper case.
def LC(+x: U32) -> Type:
  {U32.is_eq(B.Char.code(B.Base.letter(Q.bf(x))), x) == U32.is_lt(x, 97) : Bool}

def letter_code(+x: U32, +h: {NX.isl(x) == True{} : Bool}) -> LC(x):
  isl_cases(y => LC(y), x, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# Two letters have the same base when they are equal up to case.
def BQ(+x: U32, +y: U32) -> Type:
  {B.Base.is_eq(Q.bf(x), Q.bf(y)) == U32.is_zero(((x .^. y : U32) .&. 223 : U32)) : Bool}

def bq_row(+c: U32, +y: U32, +hy: {NX.isl(y) == True{} : Bool}) -> Type:
  BQ(c, y)

def beq(+x: U32, +y: U32, +hx: {NX.isl(x) == True{} : Bool}, +hy: {NX.isl(y) == True{} : Bool}) -> BQ(x, y):
  isl_cases(z => BQ(z, y), x, hx,
    isl_cases(z => BQ(65, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(67, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(71, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(84, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(78, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(97, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(99, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(103, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(116, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    isl_cases(z => BQ(110, z), y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# ---------------------------------------------------------------------------
# Bases
# ---------------------------------------------------------------------------

def letter_chr(+b: B.Base) -> {B.Base.letter(b) == Chr{B.Char.code(B.Base.letter(b))} : Char}:
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

def base_sym(+a: B.Base, +b: B.Base) -> {B.Base.is_eq(a, b) == B.Base.is_eq(b, a) : Bool}:
  match a b:
    case B.A{} B.A{}:
      {==}
    case B.A{} B.C{}:
      {==}
    case B.A{} B.G{}:
      {==}
    case B.A{} B.T{}:
      {==}
    case B.A{} B.N{}:
      {==}
    case B.C{} B.A{}:
      {==}
    case B.C{} B.C{}:
      {==}
    case B.C{} B.G{}:
      {==}
    case B.C{} B.T{}:
      {==}
    case B.C{} B.N{}:
      {==}
    case B.G{} B.A{}:
      {==}
    case B.G{} B.C{}:
      {==}
    case B.G{} B.G{}:
      {==}
    case B.G{} B.T{}:
      {==}
    case B.G{} B.N{}:
      {==}
    case B.T{} B.A{}:
      {==}
    case B.T{} B.C{}:
      {==}
    case B.T{} B.G{}:
      {==}
    case B.T{} B.T{}:
      {==}
    case B.T{} B.N{}:
      {==}
    case B.N{} B.A{}:
      {==}
    case B.N{} B.C{}:
      {==}
    case B.N{} B.G{}:
      {==}
    case B.N{} B.T{}:
      {==}
    case B.N{} B.N{}:
      {==}

def bases_sym(+a: List<&2, B.Base>, +b: List<&2, B.Base>) -> {B.Bases.eq(a, b) == B.Bases.eq(b, a) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      {==}
    case +x <> +xt +y <> +yt:
      %base_sym(y, x) : {Bool.and(_, B.Bases.eq(xt, yt)) == Bool.and(B.Base.is_eq(y, x), B.Bases.eq(yt, xt)) : Bool}
      %Equal.sym(Bool, B.Bases.eq(xt, yt), B.Bases.eq(yt, xt), bases_sym(xt, yt)) : {Bool.and(B.Base.is_eq(y, x), _) == Bool.and(B.Base.is_eq(y, x), B.Bases.eq(yt, xt)) : Bool}
      {==}

# Two letter lists, compared up to case byte by byte (as NX.feq does).
def FL(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case +x <> xt +y <> yt:
      U32.is_zero(((x .^. y : U32) .&. 223 : U32)) && FL(xt, yt)
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}

def fl_beq(+xs: List<&2, U32>, +ys: List<&2, U32>, +hx: {Q.lets(xs) == True{} : Bool}, +hy: {Q.lets(ys) == True{} : Bool}) ->
  {B.Bases.eq(Q.BF(xs), Q.BF(ys)) == FL(xs, ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      {==}
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, B.Base.is_eq(Q.bf(x), Q.bf(y)), U32.is_zero(((x .^. y : U32) .&. 223 : U32)), beq(x, y, LS.and_l(NX.isl(x), Q.lets(xt), hx), LS.and_l(NX.isl(y), Q.lets(yt), hy))) :
        {Bool.and(_, B.Bases.eq(Q.BF(xt), Q.BF(yt))) == Bool.and(U32.is_zero(((x .^. y : U32) .&. 223 : U32)), FL(xt, yt)) : Bool}
      %Equal.sym(Bool, B.Bases.eq(Q.BF(xt), Q.BF(yt)), FL(xt, yt), fl_beq(xt, yt, LS.and_r(NX.isl(x), Q.lets(xt), hx), LS.and_r(NX.isl(y), Q.lets(yt), hy))) :
        {Bool.and(U32.is_zero(((x .^. y : U32) .&. 223 : U32)), _) == Bool.and(U32.is_zero(((x .^. y : U32) .&. 223 : U32)), FL(xt, yt)) : Bool}
      {==}

# ---------------------------------------------------------------------------
# Reading and writing letters
# ---------------------------------------------------------------------------

def read_bf(+ys: List<&2, U32>, +hl: {Q.lets(ys) == True{} : Bool}) ->
  {B.Allele.read(Norm.chars(ys)) == Some{Q.BF(ys)} : Maybe<&2, List<&2, B.Base>>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %Equal.sym(Maybe<&2, B.Base>, B.Base.of_letter(Chr{y}), Some{Q.bf(y)}, of_letter_bf(y, LS.and_l(NX.isl(y), Q.lets(yt), hl))) :
        {B.Allele.read.cons(_, B.Allele.read(Norm.chars(yt))) == Some{Q.bf(y) <> Q.BF(yt)} : Maybe<&2, List<&2, B.Base>>}
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(Norm.chars(yt)), Some{Q.BF(yt)}, read_bf(yt, LS.and_r(NX.isl(y), Q.lets(yt), hl))) :
        {B.Allele.read.cons(Some{Q.bf(y)}, _) == Some{Q.bf(y) <> Q.BF(yt)} : Maybe<&2, List<&2, B.Base>>}
      {==}

# The letters written for a list's bases, as bytes.
def UPB(ys: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case +y <> yt:
      B.Char.code(B.Base.letter(Q.bf(y))) <> UPB(yt)

# Every byte is upper case (below 'a').
def UPA(ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case +y <> yt:
      U32.is_lt(y, 97) && UPA(yt)

def show_upb(+ys: List<&2, U32>) -> {B.Allele.show(Q.BF(ys)) == Norm.chars(UPB(ys)) : String}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %Equal.sym(Char, B.Base.letter(Q.bf(y)), Chr{B.Char.code(B.Base.letter(Q.bf(y)))}, letter_chr(Q.bf(y))) : {SCon{_, B.Allele.show(Q.BF(yt))} == SCon{Chr{B.Char.code(B.Base.letter(Q.bf(y)))}, Norm.chars(UPB(yt))} : String}
      %Equal.sym(String, B.Allele.show(Q.BF(yt)), Norm.chars(UPB(yt)), show_upb(yt)) : {SCon{Chr{B.Char.code(B.Base.letter(Q.bf(y)))}, _} == SCon{Chr{B.Char.code(B.Base.letter(Q.bf(y)))}, Norm.chars(UPB(yt))} : String}
      {==}

def len_upb(+ys: List<&2, U32>) -> {List.length(&2, U32, UPB(ys)) == List.length(&2, U32, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %Equal.sym(Nat, List.length(&2, U32, UPB(yt)), List.length(&2, U32, yt), len_upb(yt)) : {1n+_ == 1n+List.length(&2, U32, yt) : Nat}
      {==}

def upb_eq(+ys: List<&2, U32>, +hl: {Q.lets(ys) == True{} : Bool}) -> {D.list_eq(UPB(ys), ys) == UPA(ys) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %Equal.sym(Bool, U32.is_eq(B.Char.code(B.Base.letter(Q.bf(y))), y), U32.is_lt(y, 97), letter_code(y, LS.and_l(NX.isl(y), Q.lets(yt), hl))) : {Bool.and(_, D.list_eq(UPB(yt), yt)) == Bool.and(U32.is_lt(y, 97), UPA(yt)) : Bool}
      %Equal.sym(Bool, D.list_eq(UPB(yt), yt), UPA(yt), upb_eq(yt, LS.and_r(NX.isl(y), Q.lets(yt), hl))) : {Bool.and(U32.is_lt(y, 97), _) == Bool.and(U32.is_lt(y, 97), UPA(yt)) : Bool}
      {==}

# ---------------------------------------------------------------------------
# String.eq on the text of bytes
# ---------------------------------------------------------------------------

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

def ord_c(+s: String, +u: String, +c: Cmp) ->
  {Cmp.is_eq(String.order.go(s, u, c)) == Bool.and(Cmp.is_eq(c), Cmp.is_eq(String.order.go(s, u, EQ{}))) : Bool}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      %Equal.sym(Cmp, String.order.go(s, u, LT{}), LT{}, order_lt(s, u)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, String.order.go(s, u, GT{}), GT{}, order_gt(s, u)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

def sc(+x: U32, +y: U32, +s: String, +u: String) ->
  {String.eq(SCon{Chr{x}, s}, SCon{Chr{y}, u}) == Bool.and(U32.is_eq(x, y), String.eq(s, u)) : Bool}:
  ord_c(s, u, U32.cmp(x, y))

def seq(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {String.eq(Norm.chars(xs), Norm.chars(ys)) == D.list_eq(xs, ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      {==}
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, String.eq(SCon{Chr{x}, Norm.chars(xt)}, SCon{Chr{y}, Norm.chars(yt)}), Bool.and(U32.is_eq(x, y), String.eq(Norm.chars(xt), Norm.chars(yt))), sc(x, y, Norm.chars(xt), Norm.chars(yt))) : {_ == Bool.and(U32.is_eq(x, y), D.list_eq(xt, yt)) : Bool}
      %Equal.sym(Bool, String.eq(Norm.chars(xt), Norm.chars(yt)), D.list_eq(xt, yt), seq(xt, yt)) : {Bool.and(U32.is_eq(x, y), _) == Bool.and(U32.is_eq(x, y), D.list_eq(xt, yt)) : Bool}
      {==}

def predn(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      m

# Equal lengths: compare the heads, then the rest.
def sapp(+a: List<&2, U32>, +b: List<&2, U32>, +x: String, +y: String, +hl: {List.length(&2, U32, a) == List.length(&2, U32, b) : Nat}) ->
  {String.eq(Norm.chars(a) ++ x, Norm.chars(b) ++ y) == Bool.and(D.list_eq(a, b), String.eq(x, y)) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} +q <> +qt:
      Empty.absurd({String.eq(x, SCon{Chr{q}, Norm.chars(qt) ++ y}) == Bool.and(False{}, String.eq(x, y)) : Bool}, LS.ft(Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 0n), 0n, 1n+List.length(&2, U32, qt), hl))))
    case +p <> +pt Nil{}:
      Empty.absurd({String.eq(SCon{Chr{p}, Norm.chars(pt) ++ x}, y) == Bool.and(False{}, String.eq(x, y)) : Bool}, LS.ft(Equal.cong(Nat, Bool, n => Nat.is_eq(n, 0n), 1n+List.length(&2, U32, pt), 0n, hl)))
    case +p <> +pt +q <> +qt:
      +e = U32.is_eq(p, q)
      %Equal.sym(Bool, String.eq(SCon{Chr{p}, Norm.chars(pt) ++ x}, SCon{Chr{q}, Norm.chars(qt) ++ y}), Bool.and(e, String.eq(Norm.chars(pt) ++ x, Norm.chars(qt) ++ y)), sc(p, q, Norm.chars(pt) ++ x, Norm.chars(qt) ++ y)) : {_ == Bool.and(Bool.and(e, D.list_eq(pt, qt)), String.eq(x, y)) : Bool}
      %Equal.sym(Bool, String.eq(Norm.chars(pt) ++ x, Norm.chars(qt) ++ y), Bool.and(D.list_eq(pt, qt), String.eq(x, y)), sapp(pt, qt, x, y, Equal.cong(Nat, Nat, n => predn(n), 1n+List.length(&2, U32, pt), 1n+List.length(&2, U32, qt), hl))) :
        {Bool.and(e, _) == Bool.and(Bool.and(e, D.list_eq(pt, qt)), String.eq(x, y)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(e, D.list_eq(pt, qt)), String.eq(x, y)), Bool.and(e, Bool.and(D.list_eq(pt, qt), String.eq(x, y))), LS.and_assoc(e, D.list_eq(pt, qt), String.eq(x, y)))

# REF written as Rec.rebuild writes it: equal to its text when all upper case.
def up_ref(+ys: List<&2, U32>, +hl: {Q.lets(ys) == True{} : Bool}) ->
  {String.eq(B.Allele.show(Q.BF(ys)), Norm.chars(ys)) == UPA(ys) : Bool}:
  %Equal.sym(String, B.Allele.show(Q.BF(ys)), Norm.chars(UPB(ys)), show_upb(ys)) : {String.eq(_, Norm.chars(ys)) == UPA(ys) : Bool}
  %Equal.sym(Bool, String.eq(Norm.chars(UPB(ys)), Norm.chars(ys)), D.list_eq(UPB(ys), ys), seq(UPB(ys), ys)) : {_ == UPA(ys) : Bool}
  upb_eq(ys, hl)
