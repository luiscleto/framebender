import Base
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Splitting text at a separator (String.split), for any separator: the
# pieces hold no separator; a text with none is one piece; a text with none
# in front of a separator is the first piece. Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

# s holds no c.
def noc(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.not(Char.is_eq(h, c)) && noc(t, c)

# Every piece holds no c.
def allnoc(ps: Ss(), +c: Char) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      noc(p, c) && allnoc(t, c)

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(h))
    case False{}:
      {==}

def noc_h(+h: Char, +t: String, +c: Char, +hn: {noc(SCon{h, t}, c) == True{} : Bool}) -> {Char.is_eq(h, c) == False{} : Bool}:
  not_true(Char.is_eq(h, c), AB.and_true_l(Bool.not(Char.is_eq(h, c)), noc(t, c), hn))

def noc_t(+h: Char, +t: String, +c: Char, +hn: {noc(SCon{h, t}, c) == True{} : Bool}) -> {noc(t, c) == True{} : Bool}:
  AB.and_true_r(Bool.not(Char.is_eq(h, c)), noc(t, c), hn)

law noc_app:
  for +a: String
  for +b: String
  for +c: Char
  for +ha: {noc(a, c) == True{} : Bool}
  for +hb: {noc(b, c) == True{} : Bool}
  {noc(String.append(a, b), c) == True{} : Bool}

def noc_app(a, b, c, ha, hb):
  match a:
    case SNil{}:
      hb
    case SCon{+h, +t}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, noc_h(h, t, c, ha)) : {Bool.and(Bool.not(_), noc(String.append(t, b), c)) == True{} : Bool}
      noc_app(t, b, c, noc_t(h, t, c, ha), hb)

def is_cons(ps: Ss()) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      True{}

def fin_cons(+h: Char, +cut: Bool, +r: Ss()) -> {is_cons(String.split.fin(h, r, cut)) == True{} : Bool}:
  match cut r:
    case True{} _:
      {==}
    case False{} Nil{}:
      {==}
    case False{} x <> t:
      {==}

law split_cons:
  for +s: String
  for +c: Char
  {is_cons(String.split(s, c)) == True{} : Bool}

def split_cons(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      fin_cons(h, Char.is_eq(h, c), String.split(t, c))

# A text with no c is one piece.
law split_noc:
  for +x: String
  for +c: Char
  for +hn: {noc(x, c) == True{} : Bool}
  {String.split(x, c) == [x] : Ss()}

def split_noc(x, c, hn):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Ss(), String.split(t, c), [t], split_noc(t, c, noc_t(h, t, c, hn))) :
        {String.split.fin(h, _, Char.is_eq(h, c)) == [SCon{h, t}] : Ss()}
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, noc_h(h, t, c, hn)) :
        {String.split.fin(h, [t], _) == [SCon{h, t}] : Ss()}
      {==}

# p (no c) in front of z joins z's first piece.
def jf(+p: String, ps: Ss()) -> Ss():
  match ps:
    case Nil{}:
      [p]
    case q <> t:
      String.append(p, q) <> t

def jf_nil(+ps: Ss(), +hc: {is_cons(ps) == True{} : Bool}) -> {ps == jf("", ps) : Ss()}:
  match ps:
    case Nil{}:
      Empty.absurd({Nil{} == jf("", Nil{}) : Ss()}, AB.false_ne_true(hc))
    case q <> t:
      {==}

def push_jf(+h: Char, +t: String, +ps: Ss()) -> {String.split.push(h, jf(t, ps)) == jf(SCon{h, t}, ps) : Ss()}:
  match ps:
    case Nil{}:
      {==}
    case q <> r:
      {==}

law split_jf:
  for +p: String
  for +z: String
  for +c: Char
  for +hn: {noc(p, c) == True{} : Bool}
  {String.split(String.append(p, z), c) == jf(p, String.split(z, c)) : Ss()}

def split_jf(p, z, c, hn):
  match p:
    case SNil{}:
      jf_nil(String.split(z, c), split_cons(z, c))
    case SCon{+h, +t}:
      %Equal.sym(Ss(), String.split(String.append(t, z), c), jf(t, String.split(z, c)), split_jf(t, z, c, noc_t(h, t, c, hn))) :
        {String.split.fin(h, _, Char.is_eq(h, c)) == jf(SCon{h, t}, String.split(z, c)) : Ss()}
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, noc_h(h, t, c, hn)) :
        {String.split.fin(h, jf(t, String.split(z, c)), _) == jf(SCon{h, t}, String.split(z, c)) : Ss()}
      push_jf(h, t, String.split(z, c))

def sapp_nil(+s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.append(t, ""), t, sapp_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

# p (no tab) then a tab: the first field.
law split_tab:
  for +p: String
  for +y: String
  for +hn: {noc(p, '\t') == True{} : Bool}
  {String.split(String.append(p, SCon{'\t', y}), '\t') == p <> String.split(y, '\t') : Ss()}

def split_tab(p, y, hn):
  %Equal.sym(Ss(), String.split(String.append(p, SCon{'\t', y}), '\t'), jf(p, String.split(SCon{'\t', y}, '\t')), split_jf(p, SCon{'\t', y}, '\t', hn)) : {_ == p <> String.split(y, '\t') : Ss()}
  %Equal.sym(String, String.append(p, ""), p, sapp_nil(p)) : {_ <> String.split(y, '\t') == p <> String.split(y, '\t') : Ss()}
  {==}

# The pieces hold no separator.
def push_noc(+h: Char, +c: Char, +r: Ss(), +he: {Char.is_eq(h, c) == False{} : Bool}, +hr: {allnoc(r, c) == True{} : Bool}) ->
  {allnoc(String.split.push(h, r), c) == True{} : Bool}:
  match r:
    case Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, he) : {Bool.and(Bool.and(Bool.not(_), True{}), True{}) == True{} : Bool}
      {==}
    case Con{+q, +t}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, he) : {Bool.and(Bool.and(Bool.not(_), noc(q, c)), allnoc(t, c)) == True{} : Bool}
      hr

def fin_noc(+h: Char, +c: Char, +r: Ss(), +b: Bool, +e: {Char.is_eq(h, c) == b : Bool}, +hr: {allnoc(r, c) == True{} : Bool}) ->
  {allnoc(String.split.fin(h, r, b), c) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      push_noc(h, c, r, e, hr)

law split_all:
  for +s: String
  for +c: Char
  {allnoc(String.split(s, c), c) == True{} : Bool}

def split_all(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      fin_noc(h, c, String.split(t, c), Char.is_eq(h, c), {==}, split_all(t, c))

# The pieces of a text with no d hold no d.
def push_nod(+h: Char, +d: Char, +r: Ss(), +he: {Char.is_eq(h, d) == False{} : Bool}, +hr: {allnoc(r, d) == True{} : Bool}) ->
  {allnoc(String.split.push(h, r), d) == True{} : Bool}:
  push_noc(h, d, r, he, hr)

def fin_nod(+h: Char, +d: Char, +r: Ss(), +b: Bool, +he: {Char.is_eq(h, d) == False{} : Bool}, +hr: {allnoc(r, d) == True{} : Bool}) ->
  {allnoc(String.split.fin(h, r, b), d) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      push_nod(h, d, r, he, hr)

law split_nod:
  for +s: String
  for +c: Char
  for +d: Char
  for +hs: {noc(s, d) == True{} : Bool}
  {allnoc(String.split(s, c), d) == True{} : Bool}

def split_nod(s, c, d, hs):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      fin_nod(h, d, String.split(t, c), Char.is_eq(h, c), noc_h(h, t, d, hs), split_nod(t, c, d, noc_t(h, t, d, hs)))

# A piece picked out of pieces that hold no d holds no d.
law get_noc:
  for +ps: Ss()
  for +k: Nat
  for +d: Char
  for +hp: {allnoc(ps, d) == True{} : Bool}
  {noc(Maybe.default(&2, String, List.get(&2, String, ps, k), ""), d) == True{} : Bool}

def get_noc(ps, k, d, hp):
  match ps k:
    case Nil{} _:
      {==}
    case Con{+p, +t} 0n:
      AB.and_true_l(noc(p, d), allnoc(t, d), hp)
    case Con{+p, +t} 1n+j:
      get_noc(t, j, d, AB.and_true_r(noc(p, d), allnoc(t, d), hp))
