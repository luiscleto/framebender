import Base
import ./types.bend as B
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import lawful-words@0.1.0.0/proof_nat.bend as N

# B.Gt.split on text: a genotype with no separator is one allele; one with a
# separator is its first allele, the separator, and the genotype after it.
# And what Got.cat gives. Every variable is reusable.

def GOK(+g: B.Got) -> Bool:
  match g:
    case B.Got{+s}:
      True{}
    case B.Refuse{+c}:
      False{}

def GSTR(+g: B.Got) -> String:
  match g:
    case B.Got{+s}:
      s
    case B.Refuse{+c}:
      ""

def TK(+r: B.Gp) -> String:
  match r:
    case B.Gp{+tk, +rs}:
      tk

def RS(+r: B.Gp) -> B.Got:
  match r:
    case B.Gp{+tk, +rs}:
      rs

# No separator ('/' or '|').
def NOSEP(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(B.Gt.is_sep(h)), NOSEP(t))

def gp_eta(+r: B.Gp) -> {r == B.Gp{TK(r), RS(r)} : B.Gp}:
  match r:
    case B.Gp{+tk, +rs}:
      {==}

def put_f(+sep: Bool, +h: Char, +r: B.Gp, +o: Bool, +n: Nat, +i: Nat, +hs: {sep == False{} : Bool}) ->
  {B.Gt.go.put(sep, h, r, o, n, i) == B.Gp{SCon{h, TK(r)}, RS(r)} : B.Gp}:
  match sep:
    case True{}:
      Empty.absurd({B.Gt.go.put(True{}, h, r, o, n, i) == B.Gp{SCon{h, TK(r)}, RS(r)} : B.Gp}, P.false_ne_true(Equal.sym(Bool, True{}, False{}, hs)))
    case False{}:
      match r:
        case B.Gp{+tk, +rs}:
          {==}

# us has no separator: the first allele of us ++ v starts with us.
law go_nosep:
  for +us: String
  for +v: String
  for +o: Bool
  for +n: Nat
  for +i: Nat
  for +h: {NOSEP(us) == True{} : Bool}
  {B.Gt.go(String.append(us, v), o, n, i) == B.Gp{String.append(us, TK(B.Gt.go(v, o, n, i))), RS(B.Gt.go(v, o, n, i))} : B.Gp}

def go_nosep(us, v, o, n, i, h):
  match us:
    case SNil{}:
      gp_eta(B.Gt.go(v, o, n, i))
    case SCon{+c, +t}:
      +hc = P.not_true(B.Gt.is_sep(c), N.and_true_l(Bool.not(B.Gt.is_sep(c)), NOSEP(t), h))
      +ht = N.and_true_r(Bool.not(B.Gt.is_sep(c)), NOSEP(t), h)
      %Equal.sym(B.Gp, B.Gt.go(String.append(t, v), o, n, i), B.Gp{String.append(t, TK(B.Gt.go(v, o, n, i))), RS(B.Gt.go(v, o, n, i))}, go_nosep(t, v, o, n, i, ht)) :
        {B.Gt.go.put(B.Gt.is_sep(c), c, _, o, n, i) == B.Gp{SCon{c, String.append(t, TK(B.Gt.go(v, o, n, i)))}, RS(B.Gt.go(v, o, n, i))} : B.Gp}
      put_f(B.Gt.is_sep(c), c, B.Gp{String.append(t, TK(B.Gt.go(v, o, n, i))), RS(B.Gt.go(v, o, n, i))}, o, n, i, hc)

def SPLIT(+o: Bool, +n: Nat, +i: Nat, +g: String) -> B.Got:
  B.Gt.split(o, n, i, g)

def ALLELE(+o: Bool, +n: Nat, +i: Nat, +g: String) -> B.Got:
  B.Gt.allele(o, n, i, g)

def CAT(+a: B.Got, +b: B.Got) -> B.Got:
  B.Got.cat(a, "", b)

# A genotype with no separator: its one allele.
law split_nosep:
  for +o: Bool
  for +n: Nat
  for +i: Nat
  for +us: String
  for +h: {NOSEP(us) == True{} : Bool}
  {SPLIT(o, n, i, us) == CAT(ALLELE(o, n, i, us), B.Got{""}) : B.Got}

def split_nosep(o, n, i, us, h):
  +e1 = go_nosep(us, "", o, n, i, h)
  +e2 = {%MN.str_nil(us) : {B.Gt.go(_, o, n, i) == B.Gp{us, B.Got{""}} : B.Gp};
    %MN.str_nil(us) : {B.Gt.go(String.append(us, ""), o, n, i) == B.Gp{_, B.Got{""}} : B.Gp};
    e1 : {B.Gt.go(us, o, n, i) == B.Gp{us, B.Got{""}} : B.Gp}}
  %Equal.sym(B.Gp, B.Gt.go(us, o, n, i), B.Gp{us, B.Got{""}}, e2) : {B.Gt.split.of(_, o, n, i) == CAT(ALLELE(o, n, i, us), B.Got{""}) : B.Got}
  {==}

def go_sep.k(+s: Char, +r: B.Gp, +o: Bool, +n: Nat, +i: Nat) ->
  {B.Gt.go.put(True{}, s, r, o, n, i) == B.Gp{"", CAT(CAT(B.Got{SCon{s, SNil{}}}, ALLELE(o, n, i, TK(r))), RS(r))} : B.Gp}:
  match r:
    case B.Gp{+tk, +rs}:
      {==}

def go_sep(+s: Char, +v: String, +o: Bool, +n: Nat, +i: Nat, +hs: {B.Gt.is_sep(s) == True{} : Bool}) ->
  {B.Gt.go(SCon{s, v}, o, n, i) == B.Gp{"", CAT(CAT(B.Got{SCon{s, SNil{}}}, ALLELE(o, n, i, TK(B.Gt.go(v, o, n, i)))), RS(B.Gt.go(v, o, n, i)))} : B.Gp}:
  %Equal.sym(Bool, B.Gt.is_sep(s), True{}, hs) : {B.Gt.go.put(_, s, B.Gt.go(v, o, n, i), o, n, i) == B.Gp{"", CAT(CAT(B.Got{SCon{s, SNil{}}}, ALLELE(o, n, i, TK(B.Gt.go(v, o, n, i)))), RS(B.Gt.go(v, o, n, i)))} : B.Gp}
  go_sep.k(s, B.Gt.go(v, o, n, i), o, n, i)

law cat_assoc:
  for +a: B.Got
  for +b: B.Got
  for +c: B.Got
  {CAT(CAT(a, b), c) == CAT(a, CAT(b, c)) : B.Got}

def cat_assoc(a, b, c):
  match a b c:
    case B.Refuse{+x} _ _:
      {==}
    case B.Got{+x} B.Refuse{+y} _:
      {==}
    case B.Got{+x} B.Got{+y} B.Refuse{+z}:
      {==}
    case B.Got{+x} B.Got{+y} B.Got{+z}:
      %Equal.sym(String, String.append(String.append(x, y), z), String.append(x, String.append(y, z)), MN.str_assoc(x, y, z)) : {B.Got{_} == B.Got{String.append(x, String.append(y, z))} : B.Got}
      {==}

def split_eta(+o: Bool, +n: Nat, +i: Nat, +v: String) -> {SPLIT(o, n, i, v) == CAT(ALLELE(o, n, i, TK(B.Gt.go(v, o, n, i))), RS(B.Gt.go(v, o, n, i))) : B.Got}:
  %Equal.sym(B.Gp, B.Gt.go(v, o, n, i), B.Gp{TK(B.Gt.go(v, o, n, i)), RS(B.Gt.go(v, o, n, i))}, gp_eta(B.Gt.go(v, o, n, i))) : {B.Gt.split.of(_, o, n, i) == CAT(ALLELE(o, n, i, TK(B.Gt.go(v, o, n, i))), RS(B.Gt.go(v, o, n, i))) : B.Got}
  {==}

# us, a separator s, v: the allele us, then s, then v's genotype.
law split_sep:
  for +o: Bool
  for +n: Nat
  for +i: Nat
  for +us: String
  for +s: Char
  for +v: String
  for +h: {NOSEP(us) == True{} : Bool}
  for +hs: {B.Gt.is_sep(s) == True{} : Bool}
  {SPLIT(o, n, i, String.append(us, SCon{s, v})) == CAT(ALLELE(o, n, i, us), CAT(B.Got{SCon{s, SNil{}}}, SPLIT(o, n, i, v))) : B.Got}

def split_sep(o, n, i, us, s, v, h, hs):
  +g = B.Gt.go(v, o, n, i)
  +A = ALLELE(o, n, i, TK(g))
  +R = CAT(CAT(B.Got{SCon{s, SNil{}}}, A), RS(g))
  +X = B.Gt.go(SCon{s, v}, o, n, i)
  +RHS = CAT(ALLELE(o, n, i, us), CAT(B.Got{SCon{s, SNil{}}}, SPLIT(o, n, i, v)))
  +eX = go_sep(s, v, o, n, i, hs)
  +eTK = Equal.cong(B.Gp, String, r => TK(r), X, B.Gp{"", R}, eX)
  +eRS = Equal.cong(B.Gp, B.Got, r => RS(r), X, B.Gp{"", R}, eX)
  %Equal.sym(B.Gp, B.Gt.go(String.append(us, SCon{s, v}), o, n, i), B.Gp{String.append(us, TK(X)), RS(X)}, go_nosep(us, SCon{s, v}, o, n, i, h)) :
    {B.Gt.split.of(_, o, n, i) == RHS : B.Got}
  %Equal.sym(String, TK(X), "", eTK) : {CAT(ALLELE(o, n, i, String.append(us, _)), RS(X)) == RHS : B.Got}
  %Equal.sym(B.Got, RS(X), R, eRS) : {CAT(ALLELE(o, n, i, String.append(us, "")), _) == RHS : B.Got}
  %Equal.sym(String, String.append(us, ""), us, MN.str_nil(us)) : {CAT(ALLELE(o, n, i, _), R) == RHS : B.Got}
  %Equal.sym(B.Got, SPLIT(o, n, i, v), CAT(A, RS(g)), split_eta(o, n, i, v)) :
    {CAT(ALLELE(o, n, i, us), R) == CAT(ALLELE(o, n, i, us), CAT(B.Got{SCon{s, SNil{}}}, _)) : B.Got}
  %Equal.sym(B.Got, CAT(CAT(B.Got{SCon{s, SNil{}}}, A), RS(g)), CAT(B.Got{SCon{s, SNil{}}}, CAT(A, RS(g))), cat_assoc(B.Got{SCon{s, SNil{}}}, A, RS(g))) :
    {CAT(ALLELE(o, n, i, us), _) == CAT(ALLELE(o, n, i, us), CAT(B.Got{SCon{s, SNil{}}}, CAT(A, RS(g)))) : B.Got}
  {==}

# ---------------------------------------------------------------------------
# Got.join: the texts with sep between them, when none is refused
# ---------------------------------------------------------------------------

def Gs() -> Data:
  List<&2, B.Got>

def PS(+first: Bool, +sep: String) -> String:
  match first:
    case True{}:
      ""
    case False{}:
      sep

def JT(gs: Gs(), +first: Bool, +sep: String) -> String:
  match gs:
    case Nil{}:
      ""
    case Con{+g, r}:
      String.append(PS(first, sep), String.append(GSTR(g), JT(r, False{}, sep)))

def JG(gs: Gs()) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{+g, r}:
      Bool.and(GOK(g), JG(r))

def jo.k(+g: B.Got, +r: Gs(), +sep: String, +hg: {GOK(g) == True{} : Bool},
  +ih: {B.Got.join(r, sep) == B.Got{JT(r, True{}, sep)} : B.Got}) ->
  {B.Got.join.put(g, r, sep, B.Got.join(r, sep)) == B.Got{JT(Con{g, r}, True{}, sep)} : B.Got}:
  match g r:
    case B.Got{+s} Nil{}:
      Equal.cong(String, B.Got, x => B.Got{x}, s, String.append(s, ""), Equal.sym(String, String.append(s, ""), s, MN.str_nil(s)))
    case B.Got{+s} Con{+r1, +r2}:
      %Equal.sym(B.Got, B.Got.join(Con{r1, r2}, sep), B.Got{JT(Con{r1, r2}, True{}, sep)}, ih) : {B.Got.cat(B.Got{s}, sep, _) == B.Got{JT(Con{B.Got{s}, Con{r1, r2}}, True{}, sep)} : B.Got}
      {==}
    case B.Refuse{+c} _:
      Empty.absurd({B.Got.join.put(B.Refuse{c}, r, sep, B.Got.join(r, sep)) == B.Got{JT(Con{B.Refuse{c}, r}, True{}, sep)} : B.Got}, P.false_ne_true(hg))

law join_t:
  for +gs: Gs()
  for +sep: String
  for +h: {JG(gs) == True{} : Bool}
  {B.Got.join(gs, sep) == B.Got{JT(gs, True{}, sep)} : B.Got}

def join_t(gs, sep, h):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      jo.k(g, r, sep, N.and_true_l(GOK(g), JG(r), h), join_t(r, sep, N.and_true_r(GOK(g), JG(r), h)))
