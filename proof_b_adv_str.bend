import Base
import ./types.bend as B
import ./proof_b_defs.bend as P
import ./proof_b_simdefs.bend as S
import ./proof_b_lines_str.bend as LS
import ./proof_b_adv_wf.bend as W

# Text facts for adv_ok: S.ends_lf (empty, or ending with an LF) through
# String.append; a text with no LF that ends_lf is empty. String.ends_with
# goes through String.reverse; ends_nl computes it without reversing (as
# proof_b_lines_str.bend does for CR). Every variable is reusable.

def ends_nl.go(s: String, +h: Char) -> Bool:
  match s:
    case SNil{}:
      Char.is_eq(h, '\n')
    case SCon{h2, t}:
      ends_nl.go(t, h2)

def ends_nl(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      ends_nl.go(t, h)

def nl_if(+acc: String, +c: Bool) -> {String.starts_with.go.if(SNil{}, acc, c) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def en.go(+t: String, +h: Char, +acc: String) ->
  {String.starts_with.go("\n", String.reverse.go(t, SCon{h, acc})) == ends_nl.go(t, h) : Bool}:
  match t:
    case SNil{}:
      nl_if(acc, Char.is_eq(h, '\n'))
    case SCon{+h2, +t2}:
      en.go(t2, h2, SCon{h, acc})

law en_eq:
  for +s: String
  {ends_nl(s) == String.ends_with(s, "\n") : Bool}

def en_eq(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.sym(Bool, String.starts_with.go("\n", String.reverse.go(t, SCon{h, SNil{}})), ends_nl.go(t, h), en.go(t, h, SNil{}))

law lf_eq:
  for +s: String
  {S.ends_lf(s) == Bool.or(String.is_empty(s), ends_nl(s)) : Bool}

def lf_eq(s):
  %en_eq(s) : {Bool.or(String.is_empty(s), _) == Bool.or(String.is_empty(s), ends_nl(s)) : Bool}
  {==}

law go_ne:
  for +z: String
  for +h: Char
  for +hz: {String.is_empty(z) == False{} : Bool}
  {ends_nl.go(z, h) == ends_nl(z) : Bool}

def go_ne(z, h, hz):
  match z:
    case SNil{}:
      Empty.absurd({ends_nl.go(SNil{}, h) == ends_nl(SNil{}) : Bool}, W.ft(Equal.sym(Bool, True{}, False{}, hz)))
    case SCon{+h2, +t2}:
      {==}

law app_ne:
  for +x: String
  for +y: String
  for +hy: {String.is_empty(y) == False{} : Bool}
  {String.is_empty(String.append(x, y)) == False{} : Bool}

def app_ne(x, y, hy):
  match x:
    case SNil{}:
      hy
    case SCon{+h, +t}:
      {==}

law nl_app:
  for +x: String
  for +y: String
  for +hy: {String.is_empty(y) == False{} : Bool}
  {ends_nl(String.append(x, y)) == ends_nl(y) : Bool}

def nl_app(x, y, hy):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, ends_nl.go(String.append(t, y), h), ends_nl(String.append(t, y)), go_ne(String.append(t, y), h, app_ne(t, y, hy))) : {_ == ends_nl(y) : Bool}
      nl_app(t, y, hy)

def lf_suf.k(+x: String, +y: String, +h: {S.ends_lf(String.append(x, y)) == True{} : Bool}) -> {S.ends_lf(y) == True{} : Bool}:
  match y:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +y2 = {SCon{c, t} : String}
      +h2 = {%lf_eq(String.append(x, y2)) : {_ == True{} : Bool}; h : {Bool.or(String.is_empty(String.append(x, y2)), ends_nl(String.append(x, y2))) == True{} : Bool}}
      +h3 = {%app_ne(x, y2, {==}) : {Bool.or(_, ends_nl(String.append(x, y2))) == True{} : Bool}; h2 : {Bool.or(False{}, ends_nl(String.append(x, y2))) == True{} : Bool}}
      %Equal.sym(Bool, S.ends_lf(y2), Bool.or(String.is_empty(y2), ends_nl(y2)), lf_eq(y2)) : {_ == True{} : Bool}
      %nl_app(x, y2, {==}) : {Bool.or(False{}, _) == True{} : Bool}
      h3

# A text that ends with an LF (or is empty) after any prefix still does.
law lf_suf:
  for +x: String
  for +y: String
  for +h: {S.ends_lf(String.append(x, y)) == True{} : Bool}
  {S.ends_lf(y) == True{} : Bool}

def lf_suf(x, y, h):
  lf_suf.k(x, y, h)

law nl_nolf:
  for +s: String
  for +hn: {P.nolf(s) == True{} : Bool}
  {ends_nl(s) == False{} : Bool}

def nl_nolf(s, hn):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, SNil{}}:
      LS.nolf_h(h, SNil{}, hn)
    case SCon{+h, SCon{+h2, +t2}}:
      nl_nolf(SCon{h2, t2}, LS.nolf_t(h, SCon{h2, t2}, hn))

def nolf_lf.k(+e: Bool, +s: String, +ee: {String.is_empty(s) == e : Bool}, +hn: {ends_nl(s) == False{} : Bool}, +h: {Bool.or(String.is_empty(s), ends_nl(s)) == True{} : Bool}) -> {e == True{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      +h3 = {%ee : {Bool.or(_, ends_nl(s)) == True{} : Bool}; h : {Bool.or(False{}, ends_nl(s)) == True{} : Bool}}
      Empty.absurd({False{} == True{} : Bool}, W.ft(Equal.trans(Bool, False{}, ends_nl(s), True{}, Equal.sym(Bool, ends_nl(s), False{}, hn), h3)))

# A text with no LF that ends_lf is empty.
law nolf_lf:
  for +s: String
  for +hn: {P.nolf(s) == True{} : Bool}
  for +hl: {S.ends_lf(s) == True{} : Bool}
  {String.is_empty(s) == True{} : Bool}

def nolf_lf(s, hn, hl):
  +h2 = {%lf_eq(s) : {_ == True{} : Bool}; hl : {Bool.or(String.is_empty(s), ends_nl(s)) == True{} : Bool}}
  nolf_lf.k(String.is_empty(s), s, {==}, nl_nolf(s, hn), h2)
