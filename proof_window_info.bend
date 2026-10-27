import Base
import ./types.bend as B
import ./norm_line.bend as J
import ./proof_base.bend as P

# framebender: J.end_ok (norm_line.bend) computes B.Info.end_ok. The code
# scans INFO once, character by character, instead of splitting it into its
# entries (speed); this is the bridge the window proof uses.

def f0(ps: List<&2, String>) -> String:
  B.Rec.field(ps, 0n)

def tl(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      t

def semi(s: String) -> List<&2, String>:
  String.split(s, ';')

law field0_push:
  for +c: Char
  for +ps: List<&2, String>
  {B.Rec.field(String.split.push(c, ps), 0n) == SCon{c, B.Rec.field(ps, 0n)} : String}

def field0_push(c, ps):
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      {==}

law tl_push:
  for +c: Char
  for +ps: List<&2, String>
  {tl(String.split.push(c, ps)) == tl(ps) : List<&2, String>}

def tl_push(c, ps):
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      {==}

# piece is the first entry.
def piece_eq.go(+h: Char, +t: String, +c: Bool,
  ih: {J.piece(t) == f0(semi(t)) : String}) ->
  {J.piece.go(SCon{h, t}, Bool.not(c)) == f0(String.split.fin(h, semi(t), c)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, f0(String.split.push(h, semi(t))), SCon{h, f0(semi(t))}, field0_push(h, semi(t))) :
        {J.piece.go(SCon{h, t}, True{}) == _ : String}
      %ih : {SCon{h, J.piece(t)} == SCon{h, _} : String}
      {==}

law piece_eq:
  for +s: String
  {J.piece(s) == f0(semi(s)) : String}

def piece_eq(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      piece_eq.go(h, t, Char.is_eq(h, ';'), piece_eq(t))

# ikey is the key of the first entry.
def ikey_eq.go(+h: Char, +t: String, +c1: Bool, +c2: Bool, +e2: {Char.is_eq(h, '=') == c2 : Bool},
  ih: {J.ikey(t) == B.Info.key(f0(semi(t))) : String}) ->
  {J.ikey.go(SCon{h, t}, J.ikey.ok2(c1, c2)) == B.Info.key(f0(String.split.fin(h, semi(t), c1))) : String}:
  match c1 c2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      +P = f0(semi(t))
      %Equal.sym(String, f0(String.split.push(h, semi(t))), SCon{h, P}, field0_push(h, semi(t))) :
        {SNil{} == B.Info.key(_) : String}
      %Equal.sym(Bool, Char.is_eq(h, '='), True{}, e2) :
        {SNil{} == f0(String.split.fin(h, String.split(P, '='), _)) : String}
      {==}
    case False{} False{}:
      +P = f0(semi(t))
      %Equal.sym(String, f0(String.split.push(h, semi(t))), SCon{h, P}, field0_push(h, semi(t))) :
        {SCon{h, J.ikey(t)} == B.Info.key(_) : String}
      %Equal.sym(Bool, Char.is_eq(h, '='), False{}, e2) :
        {SCon{h, J.ikey(t)} == f0(String.split.fin(h, String.split(P, '='), _)) : String}
      %Equal.sym(String, f0(String.split.push(h, String.split(P, '='))), SCon{h, f0(String.split(P, '='))}, field0_push(h, String.split(P, '='))) :
        {SCon{h, J.ikey(t)} == _ : String}
      %ih : {SCon{h, J.ikey(t)} == SCon{h, _} : String}
      {==}

law ikey_eq:
  for +s: String
  {J.ikey(s) == B.Info.key(f0(semi(s))) : String}

def ikey_eq(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      ikey_eq.go(h, t, Char.is_eq(h, ';'), Char.is_eq(h, '='), {==}, ikey_eq(t))

law put_end_val:
  for +b: Bool
  for +s: String
  for +rest: List<&2, Maybe<&2, Nat>>
  {J.scan.put(J.end_val(b, s), rest) == B.Info.ends.put(b, f0(semi(s)), rest) : List<&2, Maybe<&2, Nat>>}

def put_end_val(b, s, rest):
  match b:
    case True{}:
      %piece_eq(s) :
        {B.Pos.read(String.drop(J.piece(s), 4n)) <> rest == B.Pos.read(String.drop(_, 4n)) <> rest : List<&2, Maybe<&2, Nat>>}
      {==}
    case False{}:
      {==}

# split never gives the empty list, so its ends are its first entry's, then
# the rest's.
def ends_head.go(+ps: List<&2, String>, ne: {Bool.not(List.is_empty(&2, String, ps)) == True{} : Bool}) ->
  {B.Info.ends.go(ps) == B.Info.ends.put(String.eq(B.Info.key(f0(ps)), "END"), f0(ps), B.Info.ends.go(tl(ps))) : List<&2, Maybe<&2, Nat>>}:
  match ps:
    case Nil{}:
      Empty.absurd({B.Info.ends.go(Nil{}) == B.Info.ends.put(String.eq(B.Info.key(f0(Nil{})), "END"), f0(Nil{}), B.Info.ends.go(tl(Nil{}))) : List<&2, Maybe<&2, Nat>>}, P.false_ne_true(ne))
    case +p <> +t:
      {==}

def split_ne.push(+c: Char, +ps: List<&2, String>) -> {Bool.not(List.is_empty(&2, String, String.split.push(c, ps))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      {==}

def split_ne.fin(+c: Char, +ps: List<&2, String>, +x: Bool) -> {Bool.not(List.is_empty(&2, String, String.split.fin(c, ps, x))) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      split_ne.push(c, ps)

law split_ne:
  for +s: String
  {Bool.not(List.is_empty(&2, String, semi(s))) == True{} : Bool}

def split_ne(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_ne.fin(h, semi(t), Char.is_eq(h, ';'))

# What scan(s, start) computes.
def R(+s: String, b: Bool) -> List<&2, Maybe<&2, Nat>>:
  match b:
    case True{}:
      B.Info.ends.go(semi(s))
    case False{}:
      B.Info.ends.go(tl(semi(s)))

def scan_skip(+h: Char, +t: String, +c: Bool, ih: {J.scan(t, c) == R(t, c) : List<&2, Maybe<&2, Nat>>}) ->
  {J.scan(t, c) == B.Info.ends.go(tl(String.split.fin(h, semi(t), c))) : List<&2, Maybe<&2, Nat>>}:
  match c:
    case True{}:
      ih
    case False{}:
      %Equal.sym(List<&2, String>, tl(String.split.push(h, semi(t))), tl(semi(t)), tl_push(h, semi(t))) :
        {J.scan(t, False{}) == B.Info.ends.go(_) : List<&2, Maybe<&2, Nat>>}
      ih

law scan_eq:
  for +s: String
  for +b: Bool
  {J.scan(s, b) == R(s, b) : List<&2, Maybe<&2, Nat>>}

def scan_eq(s, b):
  match s b:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+h, +t} True{}:
      +s1 = {SCon{h, t} : String}
      +c = Char.is_eq(h, ';')
      +rest = B.Info.ends.go(tl(semi(s1)))
      +k = Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(t, c), rest, scan_skip(h, t, c, scan_eq(t, c)))
      %k : {J.scan.put(J.end_val(String.eq(J.ikey(s1), "END"), s1), _) == B.Info.ends.go(semi(s1)) : List<&2, Maybe<&2, Nat>>}
      %Equal.sym(String, J.ikey(s1), B.Info.key(f0(semi(s1))), ikey_eq(s1)) :
        {J.scan.put(J.end_val(String.eq(_, "END"), s1), rest) == B.Info.ends.go(semi(s1)) : List<&2, Maybe<&2, Nat>>}
      +eb = String.eq(B.Info.key(f0(semi(s1))), "END")
      %Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan.put(J.end_val(eb, s1), rest), B.Info.ends.put(eb, f0(semi(s1)), rest), put_end_val(eb, s1, rest)) :
        {_ == B.Info.ends.go(semi(s1)) : List<&2, Maybe<&2, Nat>>}
      Equal.sym(List<&2, Maybe<&2, Nat>>, B.Info.ends.go(semi(s1)), B.Info.ends.put(eb, f0(semi(s1)), rest), ends_head.go(semi(s1), split_ne(s1)))
    case SCon{+h, +t} False{}:
      scan_skip(h, t, Char.is_eq(h, ';'), scan_eq(t, Char.is_eq(h, ';')))

law end_ok_eq:
  for +info: String
  for +e: Nat
  {J.end_ok(info, e) == B.Info.end_ok(info, e) : Bool}

def end_ok_eq(info, e):
  %Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(info, True{}), R(info, True{}), scan_eq(info, True{})) :
    {B.Info.end_ok.go(_, e) == B.Info.end_ok(info, e) : Bool}
  {==}
