import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN

# Lemmas for the machine proof: the lines of a text cut into pieces
# (Norm.feed, Norm.feed_eof) are the lines of the whole text (B.Text.lines).

# The pieces of a split but the last, and the last.
def pinit.go(ps: List<&2, String>, p: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case q <> t:
      p <> pinit.go(t, q)

def plast.go(ps: List<&2, String>, p: String) -> String:
  match ps:
    case Nil{}:
      p
    case q <> t:
      plast.go(t, q)

def pinit(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      pinit.go(t, p)

def plast(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case p <> t:
      plast.go(t, p)

def lines_of(ps: List<&2, String>) -> List<&2, B.Line>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      B.Text.line(p) <> lines_of(t)

def split(s: String) -> List<&2, String>:
  String.split(s, '\n')

# The complete lines of x, and what is left after its last LF.
def FL(x: String) -> List<&2, B.Line>:
  lines_of(pinit(split(x)))

def FR(x: String) -> String:
  plast(split(x))

def is_cons(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      True{}

law fin_cons:
  for +h: Char
  for +cut: Bool
  for +r: List<&2, String>
  {is_cons(String.split.fin(h, r, cut)) == True{} : Bool}

def fin_cons(h, cut, r):
  match cut r:
    case True{} _:
      {==}
    case False{} Nil{}:
      {==}
    case False{} x <> t:
      {==}

law split_cons:
  for +s: String
  {is_cons(split(s)) == True{} : Bool}

def split_cons(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      fin_cons(h, Char.is_eq(h, '\n'), split(t))

# Splitting x ++ y: x's pieces but the last, then the split of its last
# piece followed by y.
def S1.rhs(+ps: List<&2, String>, y: String) -> List<&2, String>:
  List.append(&2, String, pinit(ps), split(String.append(plast(ps), y)))

law S1.k:
  for +h: Char
  for +cut: Bool
  for +ec: {Char.is_eq(h, '\n') == cut : Bool}
  for +ps: List<&2, String>
  for +hc: {is_cons(ps) == True{} : Bool}
  for +y: String
  {String.split.fin(h, S1.rhs(ps, y), cut) == S1.rhs(String.split.fin(h, ps, cut), y) : List<&2, String>}

def S1.k(h, cut, ec, ps, hc, y):
  match cut ps:
    case _ Nil{}:
      Empty.absurd({String.split.fin(h, S1.rhs(Nil{}, y), cut) == S1.rhs(String.split.fin(h, Nil{}, cut), y) : List<&2, String>},
        P.false_ne_true(hc))
    case True{} p <> t:
      {==}
    case False{} p <> Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, ec) :
        {String.split.push(h, split(String.append(p, y))) == String.split.fin(h, split(String.append(p, y)), _) : List<&2, String>}
      {==}
    case False{} p <> q <> t2:
      {==}

law S1:
  for +x: String
  for +y: String
  {split(String.append(x, y)) == S1.rhs(split(x), y) : List<&2, String>}

def S1(x, y):
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(List<&2, String>, split(String.append(t, y)), S1.rhs(split(t), y), S1(t, y)) :
        {String.split.fin(h, _, Char.is_eq(h, '\n')) == S1.rhs(String.split.fin(h, split(t), Char.is_eq(h, '\n')), y) : List<&2, String>}
      S1.k(h, Char.is_eq(h, '\n'), {==}, split(t), split_cons(t), y)

# feed reads the same pieces.
law A1:
  for +ps: List<&2, String>
  for +p: String
  {Norm.feed.go(ps, p) == Norm.Fed{lines_of(pinit.go(ps, p)), plast.go(ps, p)} : Norm.Fed}

def A1(ps, p):
  match ps:
    case Nil{}:
      {==}
    case q <> t:
      %Equal.sym(Norm.Fed, Norm.feed.go(t, q), Norm.Fed{lines_of(pinit.go(t, q)), plast.go(t, q)}, A1(t, q)) :
        {Norm.Fed.cons(B.Text.line(p), _) == Norm.Fed{lines_of(pinit.go(q <> t, p)), plast.go(q <> t, p)} : Norm.Fed}
      {==}

law L2.k:
  for +ps: List<&2, String>
  for +hc: {is_cons(ps) == True{} : Bool}
  {Norm.feed.start(ps) == Norm.Fed{lines_of(pinit(ps)), plast(ps)} : Norm.Fed}

def L2.k(ps, hc):
  match ps:
    case Nil{}:
      Empty.absurd({Norm.feed.start(Nil{}) == Norm.Fed{lines_of(pinit(Nil{})), plast(Nil{})} : Norm.Fed}, P.false_ne_true(hc))
    case p <> t:
      A1(t, p)

law L2:
  for +x: String
  {Norm.feed.start(split(x)) == Norm.Fed{FL(x), FR(x)} : Norm.Fed}

def L2(x):
  L2.k(split(x), split_cons(x))

law A3:
  for +xs: List<&2, String>
  for +x: String
  for +q: String
  for +t: List<&2, String>
  {B.Text.lines.go(List.append(&2, String, xs, q <> t), x) == B.Text.line(x) <> List.append(&2, B.Line, lines_of(xs), B.Text.lines.go(t, q)) : List<&2, B.Line>}

def A3(xs, x, q, t):
  match xs:
    case Nil{}:
      {==}
    case y <> ys:
      %Equal.sym(List<&2, B.Line>, B.Text.lines.go(List.append(&2, String, ys, q <> t), y),
        B.Text.line(y) <> List.append(&2, B.Line, lines_of(ys), B.Text.lines.go(t, q)), A3(ys, y, q, t)) :
        {B.Text.line(x) <> _ == B.Text.line(x) <> List.append(&2, B.Line, lines_of(y <> ys), B.Text.lines.go(t, q)) : List<&2, B.Line>}
      {==}

law A4:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +hc: {is_cons(ys) == True{} : Bool}
  {B.Text.lines.start(List.append(&2, String, xs, ys)) == List.append(&2, B.Line, lines_of(xs), B.Text.lines.start(ys)) : List<&2, B.Line>}

def A4(xs, ys, hc):
  match xs ys:
    case _ Nil{}:
      Empty.absurd({B.Text.lines.start(List.append(&2, String, xs, Nil{})) == List.append(&2, B.Line, lines_of(xs), B.Text.lines.start(Nil{})) : List<&2, B.Line>},
        P.false_ne_true(hc))
    case Nil{} q <> t:
      {==}
    case x <> xt q <> t:
      A3(xt, x, q, t)

# The lines of x ++ y: the complete lines of x, then the lines of what is left
# of x followed by y.
law L1:
  for +x: String
  for +y: String
  {B.Text.lines(String.append(x, y)) == List.append(&2, B.Line, FL(x), B.Text.lines(String.append(FR(x), y))) : List<&2, B.Line>}

def L1(x, y):
  %Equal.sym(List<&2, String>, split(String.append(x, y)), S1.rhs(split(x), y), S1(x, y)) :
    {B.Text.lines.start(_) == List.append(&2, B.Line, FL(x), B.Text.lines(String.append(FR(x), y))) : List<&2, B.Line>}
  A4(pinit(split(x)), split(String.append(FR(x), y)), split_cons(String.append(FR(x), y)))

# What is left after the last LF has no LF.
law S2.k:
  for +h: Char
  for +cut: Bool
  for +ec: {Char.is_eq(h, '\n') == cut : Bool}
  for +ps: List<&2, String>
  for +hc: {is_cons(ps) == True{} : Bool}
  for +ih: {split(plast(ps)) == [plast(ps)] : List<&2, String>}
  {split(plast(String.split.fin(h, ps, cut))) == [plast(String.split.fin(h, ps, cut))] : List<&2, String>}

def S2.k(h, cut, ec, ps, hc, ih):
  match cut ps:
    case _ Nil{}:
      Empty.absurd({split(plast(String.split.fin(h, Nil{}, cut))) == [plast(String.split.fin(h, Nil{}, cut))] : List<&2, String>},
        P.false_ne_true(hc))
    case True{} p <> t:
      ih
    case False{} p <> Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, ec) :
        {String.split.fin(h, split(p), _) == [SCon{h, p}] : List<&2, String>}
      %Equal.sym(List<&2, String>, split(p), [p], ih) :
        {String.split.push(h, _) == [SCon{h, p}] : List<&2, String>}
      {==}
    case False{} p <> q <> t2:
      ih

law S2:
  for +x: String
  {split(FR(x)) == [FR(x)] : List<&2, String>}

def S2(x):
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      S2.k(h, Char.is_eq(h, '\n'), {==}, split(t), split_cons(t), S2(t))

law L3:
  for +x: String
  {B.Text.lines(FR(x)) == B.Text.last(FR(x)) : List<&2, B.Line>}

def L3(x):
  %Equal.sym(List<&2, String>, split(FR(x)), [FR(x)], S2(x)) :
    {B.Text.lines.start(_) == B.Text.last(FR(x)) : List<&2, B.Line>}
  {==}

# A text has at most one line more than it has bytes.
law N1:
  for +ps: List<&2, String>
  for +p: String
  {Nat.is_le(List.length(&2, B.Line, B.Text.lines.go(ps, p)), 1n+List.length(&2, String, ps)) == True{} : Bool}

def N1(ps, p):
  match ps:
    case Nil{}:
      match p:
        case SNil{}:
          {==}
        case SCon{h, t}:
          {==}
    case q <> t:
      N1(t, q)

law N2.k:
  for +ps: List<&2, String>
  {Nat.is_le(List.length(&2, B.Line, B.Text.lines.start(ps)), List.length(&2, String, ps)) == True{} : Bool}

def N2.k(ps):
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      N1(t, p)

law N3.fin:
  for +h: Char
  for +cut: Bool
  for +r: List<&2, String>
  {Nat.is_le(List.length(&2, String, String.split.fin(h, r, cut)), 1n+List.length(&2, String, r)) == True{} : Bool}

def N3.fin(h, cut, r):
  match cut r:
    case True{} _:
      P.le_refl(1n+List.length(&2, String, r))
    case False{} Nil{}:
      {==}
    case False{} x <> t:
      PN.le_succ(List.length(&2, String, t))

law N3:
  for +s: String
  {Nat.is_le(List.length(&2, String, split(s)), 1n+String.length(s)) == True{} : Bool}

def N3(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      PN.le_trans(List.length(&2, String, String.split.fin(h, split(t), Char.is_eq(h, '\n'))),
        1n+List.length(&2, String, split(t)), 2n+String.length(t),
        N3.fin(h, Char.is_eq(h, '\n'), split(t)), N3(t))

law N2:
  for +s: String
  {Nat.is_le(List.length(&2, B.Line, B.Text.lines(s)), 1n+String.length(s)) == True{} : Bool}

def N2(s):
  PN.le_trans(List.length(&2, B.Line, B.Text.lines(s)), List.length(&2, String, split(s)), 1n+String.length(s),
    N2.k(split(s)), N3(s))
