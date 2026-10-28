import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ../lawful-bytes/defs.bend as D
import ../lawful-arrays/proof_base.bend as AB

# String facts for the lines area: B.Text.lines through String.split at LF,
# P.nolf, and the text of a byte list (NR.chars). Some are copied from
# proof_machine_lines.bend (S1, A3, A4, L1), which no longer checks.

def split(s: String) -> List<&2, String>:
  String.split(s, '\n')

def is_cons(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      True{}

def fin_cons(+h: Char, +cut: Bool, +r: List<&2, String>) ->
  {is_cons(String.split.fin(h, r, cut)) == True{} : Bool}:
  match cut r:
    case True{} _:
      {==}
    case False{} Nil{}:
      {==}
    case False{} x <> t:
      {==}

def split_cons(+s: String) ->
  {is_cons(split(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      fin_cons(h, Char.is_eq(h, '\n'), split(t))

# Strings
# =======

def sapp_nil(+s: String) ->
  {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.append(t, ""), t, sapp_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def sassoc(+a: String, +b: String, +c: String) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %sassoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(h))
    case False{}:
      {==}

# The first character of a text with no LF is not an LF; nor is the rest.
def nolf_h(+h: Char, +t: String, +hn: {P.nolf(SCon{h, t}) == True{} : Bool}) ->
  {Char.is_eq(h, '\n') == False{} : Bool}:
  not_true(Char.is_eq(h, '\n'), AB.and_true_l(Bool.not(Char.is_eq(h, '\n')), P.nolf(t), hn))

def nolf_t(+h: Char, +t: String, +hn: {P.nolf(SCon{h, t}) == True{} : Bool}) ->
  {P.nolf(t) == True{} : Bool}:
  AB.and_true_r(Bool.not(Char.is_eq(h, '\n')), P.nolf(t), hn)

def nolf_app(+a: String, +b: String, +ha: {P.nolf(a) == True{} : Bool}, +hb: {P.nolf(b) == True{} : Bool}) ->
  {P.nolf(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+h, +t}:
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, nolf_h(h, t, ha)) :
        {Bool.and(Bool.not(_), P.nolf(String.append(t, b))) == True{} : Bool}
      nolf_app(t, b, nolf_t(h, t, ha), hb)

# Splitting at LF
# ===============

# A text with no LF is one piece.
def split_nolf(+x: String, +hn: {P.nolf(x) == True{} : Bool}) ->
  {split(x) == [x] : List<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(List<&2, String>, split(t), [t], split_nolf(t, nolf_t(h, t, hn))) :
        {String.split.fin(h, _, Char.is_eq(h, '\n')) == [SCon{h, t}] : List<&2, String>}
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, nolf_h(h, t, hn)) :
        {String.split.fin(h, [t], _) == [SCon{h, t}] : List<&2, String>}
      {==}

# A text with no LF in front of z joins z's first piece.
def jf(+p: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [p]
    case q <> t:
      String.append(p, q) <> t

def jf_nil(+ps: List<&2, String>, +hc: {is_cons(ps) == True{} : Bool}) ->
  {ps == jf("", ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      Empty.absurd({Nil{} == jf("", Nil{}) : List<&2, String>}, AB.false_ne_true(hc))
    case q <> t:
      {==}

def push_jf(+h: Char, +t: String, +ps: List<&2, String>) ->
  {String.split.push(h, jf(t, ps)) == jf(SCon{h, t}, ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case q <> r:
      {==}

def split_jf(+p: String, +z: String, +hn: {P.nolf(p) == True{} : Bool}) ->
  {split(String.append(p, z)) == jf(p, split(z)) : List<&2, String>}:
  match p:
    case SNil{}:
      jf_nil(split(z), split_cons(z))
    case SCon{+h, +t}:
      %Equal.sym(List<&2, String>, split(String.append(t, z)), jf(t, split(z)), split_jf(t, z, nolf_t(h, t, hn))) :
        {String.split.fin(h, _, Char.is_eq(h, '\n')) == jf(SCon{h, t}, split(z)) : List<&2, String>}
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, nolf_h(h, t, hn)) :
        {String.split.fin(h, jf(t, split(z)), _) == jf(SCon{h, t}, split(z)) : List<&2, String>}
      push_jf(h, t, split(z))

def go_start(+ps: List<&2, String>, +p: String, +hc: {is_cons(ps) == True{} : Bool}) ->
  {B.Text.lines.go(ps, p) == B.Text.line(p) <> B.Text.lines.start(ps) : List<&2, B.Line>}:
  match ps:
    case Nil{}:
      Empty.absurd({B.Text.lines.go(Nil{}, p) == B.Text.line(p) <> B.Text.lines.start(Nil{}) : List<&2, B.Line>}, AB.false_ne_true(hc))
    case q <> t:
      {==}

# Lines
# =====

def lines_cons(+p: String, +y: String, +hn: {P.nolf(p) == True{} : Bool}) ->
  {B.Text.lines(String.append(p, String.append("\n", y))) == B.Text.line(p) <> B.Text.lines(y) : List<&2, B.Line>}:
  %Equal.sym(List<&2, String>, split(String.append(p, String.append("\n", y))), jf(p, split(String.append("\n", y))), split_jf(p, String.append("\n", y), hn)) :
    {B.Text.lines.start(_) == B.Text.line(p) <> B.Text.lines(y) : List<&2, B.Line>}
  %Equal.sym(String, String.append(p, ""), p, sapp_nil(p)) :
    {B.Text.lines.go(split(y), _) == B.Text.line(p) <> B.Text.lines(y) : List<&2, B.Line>}
  go_start(split(y), p, split_cons(y))

def lines_lf(+p: String, +hn: {P.nolf(p) == True{} : Bool}) ->
  {B.Text.lines(String.append(p, "\n")) == [B.Text.line(p)] : List<&2, B.Line>}:
  %Equal.sym(List<&2, String>, split(String.append(p, "\n")), jf(p, split("\n")), split_jf(p, "\n", hn)) :
    {B.Text.lines.start(_) == [B.Text.line(p)] : List<&2, B.Line>}
  %Equal.sym(String, String.append(p, ""), p, sapp_nil(p)) :
    {B.Text.lines.go([""], _) == [B.Text.line(p)] : List<&2, B.Line>}
  {==}

def lines_nolf(+x: String, +hn: {P.nolf(x) == True{} : Bool}) ->
  {B.Text.lines(x) == B.Text.last(x) : List<&2, B.Line>}:
  %Equal.sym(List<&2, String>, split(x), [x], split_nolf(x, hn)) :
    {B.Text.lines.start(_) == B.Text.last(x) : List<&2, B.Line>}
  {==}

def last_app(+u: String, +x: String, +hx: {String.is_empty(x) == False{} : Bool}) ->
  {B.Text.last(String.append(u, x)) == [B.Text.line(String.append(u, x))] : List<&2, B.Line>}:
  match u x:
    case SNil{} SNil{}:
      Empty.absurd({B.Text.last(SNil{}) == [B.Text.line(SNil{})] : List<&2, B.Line>}, AB.true_ne_false(hx))
    case SNil{} SCon{h, t}:
      {==}
    case SCon{a, b} _:
      {==}

# The pieces of a split but the last, and the last (proof_machine_lines.bend).
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

def FL(x: String) -> List<&2, B.Line>:
  lines_of(pinit(split(x)))

def FR(x: String) -> String:
  plast(split(x))

def S1.rhs(+ps: List<&2, String>, y: String) -> List<&2, String>:
  List.append(&2, String, pinit(ps), split(String.append(plast(ps), y)))

def S1.k(+h: Char, +cut: Bool, +ec: {Char.is_eq(h, '\n') == cut : Bool}, +ps: List<&2, String>,
  +hc: {is_cons(ps) == True{} : Bool}, +y: String) ->
  {String.split.fin(h, S1.rhs(ps, y), cut) == S1.rhs(String.split.fin(h, ps, cut), y) : List<&2, String>}:
  match cut ps:
    case _ Nil{}:
      Empty.absurd({String.split.fin(h, S1.rhs(Nil{}, y), cut) == S1.rhs(String.split.fin(h, Nil{}, cut), y) : List<&2, String>},
        AB.false_ne_true(hc))
    case True{} p <> t:
      {==}
    case False{} p <> Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, ec) :
        {String.split.push(h, split(String.append(p, y))) == String.split.fin(h, split(String.append(p, y)), _) : List<&2, String>}
      {==}
    case False{} p <> q <> t2:
      {==}

def S1(+x: String, +y: String) ->
  {split(String.append(x, y)) == S1.rhs(split(x), y) : List<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(List<&2, String>, split(String.append(t, y)), S1.rhs(split(t), y), S1(t, y)) :
        {String.split.fin(h, _, Char.is_eq(h, '\n')) == S1.rhs(String.split.fin(h, split(t), Char.is_eq(h, '\n')), y) : List<&2, String>}
      S1.k(h, Char.is_eq(h, '\n'), {==}, split(t), split_cons(t), y)

def A3(+xs: List<&2, String>, +x: String, +q: String, +t: List<&2, String>) ->
  {B.Text.lines.go(List.append(&2, String, xs, q <> t), x) == B.Text.line(x) <> List.append(&2, B.Line, lines_of(xs), B.Text.lines.go(t, q)) : List<&2, B.Line>}:
  match xs:
    case Nil{}:
      {==}
    case y <> ys:
      %Equal.sym(List<&2, B.Line>, B.Text.lines.go(List.append(&2, String, ys, q <> t), y),
        B.Text.line(y) <> List.append(&2, B.Line, lines_of(ys), B.Text.lines.go(t, q)), A3(ys, y, q, t)) :
        {B.Text.line(x) <> _ == B.Text.line(x) <> List.append(&2, B.Line, lines_of(y <> ys), B.Text.lines.go(t, q)) : List<&2, B.Line>}
      {==}

def A4(+xs: List<&2, String>, +ys: List<&2, String>, +hc: {is_cons(ys) == True{} : Bool}) ->
  {B.Text.lines.start(List.append(&2, String, xs, ys)) == List.append(&2, B.Line, lines_of(xs), B.Text.lines.start(ys)) : List<&2, B.Line>}:
  match xs ys:
    case _ Nil{}:
      Empty.absurd({B.Text.lines.start(List.append(&2, String, xs, Nil{})) == List.append(&2, B.Line, lines_of(xs), B.Text.lines.start(Nil{})) : List<&2, B.Line>},
        AB.false_ne_true(hc))
    case Nil{} q <> t:
      {==}
    case x <> xt q <> t:
      A3(xt, x, q, t)

# The lines of x ++ y: the complete lines of x, then the lines of what is left
# of x followed by y.
def L1(+x: String, +y: String) ->
  {B.Text.lines(String.append(x, y)) == List.append(&2, B.Line, FL(x), B.Text.lines(String.append(FR(x), y))) : List<&2, B.Line>}:
  %Equal.sym(List<&2, String>, split(String.append(x, y)), S1.rhs(split(x), y), S1(x, y)) :
    {B.Text.lines.start(_) == List.append(&2, B.Line, FL(x), B.Text.lines(String.append(FR(x), y))) : List<&2, B.Line>}
  A4(pinit(split(x)), split(String.append(FR(x), y)), split_cons(String.append(FR(x), y)))

# What is left after the last LF has no LF.
def F2.k(+h: Char, +cut: Bool, +ec: {Char.is_eq(h, '\n') == cut : Bool}, +ps: List<&2, String>,
  +hc: {is_cons(ps) == True{} : Bool}, +ih: {P.nolf(plast(ps)) == True{} : Bool}) ->
  {P.nolf(plast(String.split.fin(h, ps, cut))) == True{} : Bool}:
  match cut ps:
    case _ Nil{}:
      Empty.absurd({P.nolf(plast(String.split.fin(h, Nil{}, cut))) == True{} : Bool}, AB.false_ne_true(hc))
    case True{} p <> t:
      ih
    case False{} p <> Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\n'), False{}, ec) :
        {Bool.and(Bool.not(_), P.nolf(p)) == True{} : Bool}
      ih
    case False{} p <> q <> t2:
      ih

def fr_nolf(+x: String) ->
  {P.nolf(FR(x)) == True{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      F2.k(h, Char.is_eq(h, '\n'), {==}, split(t), split_cons(t), fr_nolf(t))

# Norm.line is B.Text.line (proof_machine_lines.bend).
def cr_if(+acc: String, +c: Bool) -> {String.starts_with.go.if(SNil{}, acc, c) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ends_cr.go(+t: String, +h: Char, +acc: String) ->
  {String.starts_with.go("\r", String.reverse.go(t, SCon{h, acc})) == Norm.ends_cr.go(t, h) : Bool}:
  match t:
    case SNil{}:
      cr_if(acc, Char.is_eq(h, '\r'))
    case SCon{+h2, +t2}:
      ends_cr.go(t2, h2, SCon{h, acc})

def ends_cr(+p: String) ->
  {Norm.ends_cr(p) == String.ends_with(p, "\r") : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.sym(Bool, String.starts_with.go("\r", String.reverse.go(t, SCon{h, SNil{}})), Norm.ends_cr.go(t, h), ends_cr.go(t, h, SNil{}))

def line_eq(+p: String) ->
  {Norm.line(p) == B.Text.line(p) : B.Line}:
  %Equal.sym(Bool, Norm.ends_cr(p), String.ends_with(p, "\r"), ends_cr(p)) : {B.Text.line.if(_, p) == B.Text.line(p) : B.Line}
  {==}

# The text of a byte list
# =======================

def chars_app(+xs: List<&2, U32>, +ys: List<&2, U32>) ->
  {NR.chars(List.append(&2, U32, xs, ys)) == String.append(NR.chars(xs), NR.chars(ys)) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %chars_app(t, ys) : {SCon{Chr{x}, NR.chars(List.append(&2, U32, t, ys))} == SCon{Chr{x}, _} : String}
      {==}

def chars_norm(+xs: List<&2, U32>) ->
  {Norm.chars(xs) == NR.chars(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %chars_norm(t) : {SCon{Chr{x}, Norm.chars(t)} == SCon{Chr{x}, _} : String}
      {==}

def chars_codes(+s: String) ->
  {NR.chars(E.codes(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      match c:
        case Chr{+x}:
          %chars_codes(t) : {SCon{Chr{x}, NR.chars(E.codes(t))} == SCon{Chr{x}, _} : String}
          {==}

def bytes_chars(+xs: List<&2, U32>) ->
  {E.is_bytes(NR.chars(xs)) == D.all_bytes(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %bytes_chars(t) : {Bool.and(U32.is_lt(x, 256), E.is_bytes(NR.chars(t))) == Bool.and(U32.is_lt(x, 256), _) : Bool}
      {==}

def bytes_app(+a: String, +b: String, +ha: {E.is_bytes(a) == True{} : Bool}, +hb: {E.is_bytes(b) == True{} : Bool}) ->
  {E.is_bytes(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +t}:
      %Equal.sym(Bool, U32.is_lt(Char.to_u32(c), 256), True{}, AB.and_true_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), ha)) :
        {Bool.and(_, E.is_bytes(String.append(t, b))) == True{} : Bool}
      bytes_app(t, b, AB.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), ha), hb)

def length_chars(+xs: List<&2, U32>) ->
  {String.length(NR.chars(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %length_chars(t) : {1n+String.length(NR.chars(t)) == 1n+_ : Nat}
      {==}

# A last line without an LF reads the same with one.
def lines_eof.go(+y: String, +x: String, +hn: {P.nolf(x) == True{} : Bool}, +hx: {String.is_empty(x) == False{} : Bool}) ->
  {B.Text.lines(String.append(y, String.append(x, "\n"))) == B.Text.lines(String.append(y, x)) : List<&2, B.Line>}:
  +u = FR(y)
  +ux = String.append(u, x)
  +hu = nolf_app(u, x, fr_nolf(y), hn)
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(y, String.append(x, "\n"))), List.append(&2, B.Line, FL(y), B.Text.lines(String.append(u, String.append(x, "\n")))), L1(y, String.append(x, "\n"))) :
    {_ == B.Text.lines(String.append(y, x)) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(y, x)), List.append(&2, B.Line, FL(y), B.Text.lines(ux)), L1(y, x)) :
    {List.append(&2, B.Line, FL(y), B.Text.lines(String.append(u, String.append(x, "\n")))) == _ : List<&2, B.Line>}
  %sassoc(u, x, "\n") :
    {List.append(&2, B.Line, FL(y), B.Text.lines(_)) == List.append(&2, B.Line, FL(y), B.Text.lines(ux)) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(ux, "\n")), [B.Text.line(ux)], lines_lf(ux, hu)) :
    {List.append(&2, B.Line, FL(y), _) == List.append(&2, B.Line, FL(y), B.Text.lines(ux)) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(ux), B.Text.last(ux), lines_nolf(ux, hu)) :
    {List.append(&2, B.Line, FL(y), [B.Text.line(ux)]) == List.append(&2, B.Line, FL(y), _) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.last(ux), [B.Text.line(ux)], last_app(u, x, hx)) :
    {List.append(&2, B.Line, FL(y), [B.Text.line(ux)]) == List.append(&2, B.Line, FL(y), _) : List<&2, B.Line>}
  {==}
