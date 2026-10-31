import Base
import ./types.bend as B
import ./proof_s_cr.bend as CR
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Characters through the INFO and FORMAT splitters (types.bend's Vals, Info,
# Gt, Fmt): what they write is made of pieces of what they read, the
# separators they put, '.', and digits. So any property of characters the
# input, the separators, '.' and the digits have, the output has too (no tab,
# bytes, ...). Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

# The properties of characters used: not the character d; a byte.
type Cls is Data:
  NoC{d: Char}
  Byt{}

def pc(+k: Cls, +c: Char) -> Bool:
  match k:
    case NoC{+d}:
      Bool.not(Char.is_eq(c, d))
    case Byt{}:
      U32.is_lt(Char.to_u32(c), 256)

# Every character of s has p.
def ALLC(+p: Cls, s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      pc(p, h) && ALLC(p, t)

def ALLS(+p: Cls, xs: Ss()) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      ALLC(p, x) && ALLS(p, t)

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Appending.
law allc_app:
  for +p: Cls
  for +a: String
  for +b: String
  for +ha: {ALLC(p, a) == True{} : Bool}
  for +hb: {ALLC(p, b) == True{} : Bool}
  {ALLC(p, String.append(a, b)) == True{} : Bool}

def allc_app(p, a, b, ha, hb):
  match a:
    case SNil{}:
      hb
    case SCon{+h, +t}:
      and_tt(pc(p, h), ALLC(p, String.append(t, b)), AB.and_true_l(pc(p, h), ALLC(p, t), ha), allc_app(p, t, b, AB.and_true_r(pc(p, h), ALLC(p, t), ha), hb))

# Dropping a prefix.
law allc_drop:
  for +p: Cls
  for +s: String
  for +k: Nat
  for +h: {ALLC(p, s) == True{} : Bool}
  {ALLC(p, String.drop(s, k)) == True{} : Bool}

def allc_drop(p, s, k, h):
  match s k:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      h
    case SCon{+c, +t} 1n+j:
      allc_drop(p, t, j, AB.and_true_r(pc(p, c), ALLC(p, t), h))

# Splitting: every piece has p.
def push_all(+p: Cls, +h: Char, +r: Ss(), +hh: {pc(p, h) == True{} : Bool}, +hr: {ALLS(p, r) == True{} : Bool}) ->
  {ALLS(p, String.split.push(h, r)) == True{} : Bool}:
  match r:
    case Nil{}:
      %Equal.sym(Bool, pc(p, h), True{}, hh) : {Bool.and(Bool.and(_, True{}), True{}) == True{} : Bool}
      {==}
    case Con{+q, +t}:
      and_tt(Bool.and(pc(p, h), ALLC(p, q)), ALLS(p, t), and_tt(pc(p, h), ALLC(p, q), hh, AB.and_true_l(ALLC(p, q), ALLS(p, t), hr)), AB.and_true_r(ALLC(p, q), ALLS(p, t), hr))

def fin_all(+p: Cls, +h: Char, +r: Ss(), +b: Bool, +hh: {pc(p, h) == True{} : Bool}, +hr: {ALLS(p, r) == True{} : Bool}) ->
  {ALLS(p, String.split.fin(h, r, b)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      push_all(p, h, r, hh, hr)

law split_all:
  for +p: Cls
  for +s: String
  for +c: Char
  for +h: {ALLC(p, s) == True{} : Bool}
  {ALLS(p, String.split(s, c)) == True{} : Bool}

def split_all(p, s, c, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      fin_all(p, x, String.split(t, c), Char.is_eq(x, c), AB.and_true_l(pc(p, x), ALLC(p, t), h), split_all(p, t, c, AB.and_true_r(pc(p, x), ALLC(p, t), h)))

# Picking one.
law get_all:
  for +p: Cls
  for +xs: Ss()
  for +k: Nat
  for +x: String
  for +h: {ALLS(p, xs) == True{} : Bool}
  for +hg: {List.get(&2, String, xs, k) == Some{x} : Maybe<&2, String>}
  {ALLC(p, x) == True{} : Bool}

def unsome(m: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, m, "")

def is_some(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def get_all(p, xs, k, x, h, hg):
  match xs k:
    case Nil{} _:
      Empty.absurd({ALLC(p, x) == True{} : Bool}, AB.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, is_some, None{}, Some{x}, hg)))
    case Con{+y, +t} 0n:
      %Equal.sym(String, x, y, Equal.sym(String, y, x, Equal.cong(Maybe<&2, String>, String, unsome, Some{y}, Some{x}, hg))) : {ALLC(p, _) == True{} : Bool}
      AB.and_true_l(ALLC(p, y), ALLS(p, t), h)
    case Con{+y, +t} 1n+j:
      get_all(p, t, j, x, AB.and_true_r(ALLC(p, y), ALLS(p, t), h), hg)

# Joining with a separator that has p.
law join_go:
  for +p: Cls
  for +xs: Ss()
  for +x0: String
  for +sep: String
  for +h0: {ALLC(p, x0) == True{} : Bool}
  for +h: {ALLS(p, xs) == True{} : Bool}
  for +hs: {ALLC(p, sep) == True{} : Bool}
  {ALLC(p, String.join.go(xs, x0, sep)) == True{} : Bool}

def join_go(p, xs, x0, sep, h0, h, hs):
  match xs:
    case Nil{}:
      h0
    case Con{+y, +t}:
      allc_app(p, x0, String.append(sep, String.join.go(t, y, sep)), h0,
        allc_app(p, sep, String.join.go(t, y, sep), hs,
          join_go(p, t, y, sep, AB.and_true_l(ALLC(p, y), ALLS(p, t), h), AB.and_true_r(ALLC(p, y), ALLS(p, t), h), hs)))

law join_all:
  for +p: Cls
  for +xs: Ss()
  for +sep: String
  for +h: {ALLS(p, xs) == True{} : Bool}
  for +hs: {ALLC(p, sep) == True{} : Bool}
  {ALLC(p, String.join(xs, sep)) == True{} : Bool}

def join_all(p, xs, sep, h, hs):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      join_go(p, t, y, sep, AB.and_true_l(ALLC(p, y), ALLS(p, t), h), AB.and_true_r(ALLC(p, y), ALLS(p, t), h), hs)

# Digits.
def DIG(+p: Cls) -> Bool:
  pc(p, '0') && pc(p, '1') && pc(p, '2') && pc(p, '3') && pc(p, '4') && pc(p, '5') && pc(p, '6') && pc(p, '7') && pc(p, '8') && pc(p, '9')

def DC(+r: Nat) -> Char:
  Chr{U32.from_nat(Nat.add(48n, r))}

def dig.k(+p: Cls, +r: Nat, +hr: {Nat.is_lt(r, 10n) == True{} : Bool},
  +e0: {pc(p, '0') == True{} : Bool}, +e1: {pc(p, '1') == True{} : Bool}, +e2: {pc(p, '2') == True{} : Bool}, +e3: {pc(p, '3') == True{} : Bool}, +e4: {pc(p, '4') == True{} : Bool},
  +e5: {pc(p, '5') == True{} : Bool}, +e6: {pc(p, '6') == True{} : Bool}, +e7: {pc(p, '7') == True{} : Bool}, +e8: {pc(p, '8') == True{} : Bool}, +e9: {pc(p, '9') == True{} : Bool}) ->
  {pc(p, DC(r)) == True{} : Bool}:
  match r:
    case 0n:
      e0
    case 1n:
      e1
    case 2n:
      e2
    case 3n:
      e3
    case 4n:
      e4
    case 5n:
      e5
    case 6n:
      e6
    case 7n:
      e7
    case 8n:
      e8
    case 9n:
      e9
    case 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q:
      Empty.absurd({pc(p, DC(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q)) == True{} : Bool}, AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q, 10n), True{}, Equal.sym(Bool, Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q, 10n), False{}, N.le_not_lt(10n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q, N.le_zero_l(q))), hr)))

def dig(+p: Cls, +r: Nat, +hr: {Nat.is_lt(r, 10n) == True{} : Bool}, +hd: {DIG(p) == True{} : Bool}) -> {pc(p, DC(r)) == True{} : Bool}:
  +d0 = pc(p, '0')
  +d1 = pc(p, '1')
  +d2 = pc(p, '2')
  +d3 = pc(p, '3')
  +d4 = pc(p, '4')
  +d5 = pc(p, '5')
  +d6 = pc(p, '6')
  +d7 = pc(p, '7')
  +d8 = pc(p, '8')
  +d9 = pc(p, '9')
  +h8 = AB.and_true_l(d0 && d1 && d2 && d3 && d4 && d5 && d6 && d7 && d8, d9, hd)
  +h7 = AB.and_true_l(d0 && d1 && d2 && d3 && d4 && d5 && d6 && d7, d8, h8)
  +h6 = AB.and_true_l(d0 && d1 && d2 && d3 && d4 && d5 && d6, d7, h7)
  +h5 = AB.and_true_l(d0 && d1 && d2 && d3 && d4 && d5, d6, h6)
  +h4 = AB.and_true_l(d0 && d1 && d2 && d3 && d4, d5, h5)
  +h3 = AB.and_true_l(d0 && d1 && d2 && d3, d4, h4)
  +h2 = AB.and_true_l(d0 && d1 && d2, d3, h3)
  +h1 = AB.and_true_l(d0 && d1, d2, h2)
  dig.k(p, r, hr, AB.and_true_l(d0, d1, h1), AB.and_true_r(d0, d1, h1), AB.and_true_r(d0 && d1, d2, h2), AB.and_true_r(d0 && d1 && d2, d3, h3),
    AB.and_true_r(d0 && d1 && d2 && d3, d4, h4), AB.and_true_r(d0 && d1 && d2 && d3 && d4, d5, h5), AB.and_true_r(d0 && d1 && d2 && d3 && d4 && d5, d6, h6),
    AB.and_true_r(d0 && d1 && d2 && d3 && d4 && d5 && d6, d7, h7), AB.and_true_r(d0 && d1 && d2 && d3 && d4 && d5 && d6 && d7, d8, h8),
    AB.and_true_r(d0 && d1 && d2 && d3 && d4 && d5 && d6 && d7 && d8, d9, hd))

# Writing a number: digits.
def DM() -> Type:
  Nat & Nat

def sh.fin(+p: Cls, +g: Nat, +acc: String, +d: Char, q: Nat,
  +hd: {pc(p, d) == True{} : Bool}, +ha: {ALLC(p, acc) == True{} : Bool},
  ih: @+n2: Nat -> @+acc2: String -> {ALLC(p, acc2) == True{} : Bool} -> {ALLC(p, Nat.show.go(g, n2, acc2)) == True{} : Bool}) ->
  {ALLC(p, Nat.show.fin(g, acc, (d, q))) == True{} : Bool}:
  match q:
    case 0n:
      and_tt(pc(p, d), ALLC(p, acc), hd, ha)
    case 1n+k:
      ih(1n+k, SCon{d, acc}, and_tt(pc(p, d), ALLC(p, acc), hd, ha))

def sh.dm(+p: Cls, +g: Nat, +acc: String, +n: Nat, dm: DM(), +e: {Nat.divmod(n, 10n) == dm : DM()},
  +hdg: {DIG(p) == True{} : Bool}, +ha: {ALLC(p, acc) == True{} : Bool},
  ih: @+n2: Nat -> @+acc2: String -> {ALLC(p, acc2) == True{} : Bool} -> {ALLC(p, Nat.show.go(g, n2, acc2)) == True{} : Bool}) ->
  {ALLC(p, Nat.show.fin(g, acc, Nat.show.put(dm))) == True{} : Bool}:
  match dm:
    case (+q, +r):
      +hr = {%Equal.cong(DM(), Nat, z => Pair.snd(Nat, Nat, z), Nat.divmod(n, 10n), (q, r), e) : {Nat.is_lt(_, 10n) == True{} : Bool};
        N.mod_lt(n, 10n, {==}) : {Nat.is_lt(r, 10n) == True{} : Bool}}
      sh.fin(p, g, acc, DC(r), q, dig(p, r, hr, hdg), ha, ih)

law show_go:
  for +p: Cls
  for +f: Nat
  for +n: Nat
  for +acc: String
  for +hdg: {DIG(p) == True{} : Bool}
  for +ha: {ALLC(p, acc) == True{} : Bool}
  {ALLC(p, Nat.show.go(f, n, acc)) == True{} : Bool}

def show_go(p, f, n, acc, hdg, ha):
  match f:
    case 0n:
      ha
    case 1n+g:
      sh.dm(p, g, acc, n, Nat.divmod(n, 10n), {==}, hdg, ha, +n2 => +acc2 => h2 => show_go(p, g, n2, acc2, hdg, h2))

law show_all:
  for +p: Cls
  for +n: Nat
  for +hdg: {DIG(p) == True{} : Bool}
  {ALLC(p, Nat.show(n)) == True{} : Bool}

def show_all(p, n, hdg):
  sh.dm(p, n, SNil{}, n, Nat.divmod(n, 10n), {==}, hdg, {==}, +n2 => +acc2 => h2 => show_go(p, n, n2, acc2, hdg, h2))

# ---------------------------------------------------------------------------
# Got, Maybe, the values
# ---------------------------------------------------------------------------

def GOK(+p: Cls, g: B.Got) -> Bool:
  match g:
    case B.Got{s}:
      ALLC(p, s)
    case B.Refuse{c}:
      True{}

def GOKS(+p: Cls, gs: List<&2, B.Got>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> t:
      GOK(p, g) && GOKS(p, t)

def MOK(+p: Cls, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      ALLC(p, x)

def MLOK(+p: Cls, m: Maybe<&2, Ss()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{xs}:
      ALLS(p, xs)

# The separators the splitters put, '.', and the digits.
def SEPS(+p: Cls) -> Bool:
  pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.') && DIG(p)

def s_comma(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {ALLC(p, ",") == True{} : Bool}:
  and_tt(pc(p, ','), True{}, AB.and_true_l(pc(p, ','), pc(p, '='), AB.and_true_l(pc(p, ',') && pc(p, '='), pc(p, ';'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';'), pc(p, ':'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':'), pc(p, '.'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h))))), {==})

def s_eq(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {ALLC(p, "=") == True{} : Bool}:
  and_tt(pc(p, '='), True{}, AB.and_true_r(pc(p, ','), pc(p, '='), AB.and_true_l(pc(p, ',') && pc(p, '='), pc(p, ';'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';'), pc(p, ':'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':'), pc(p, '.'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h))))), {==})

def s_semi(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {ALLC(p, ";") == True{} : Bool}:
  and_tt(pc(p, ';'), True{}, AB.and_true_r(pc(p, ',') && pc(p, '='), pc(p, ';'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';'), pc(p, ':'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':'), pc(p, '.'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h)))), {==})

def s_colon(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {ALLC(p, ":") == True{} : Bool}:
  and_tt(pc(p, ':'), True{}, AB.and_true_r(pc(p, ',') && pc(p, '=') && pc(p, ';'), pc(p, ':'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':'), pc(p, '.'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h))), {==})

def s_dot(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {ALLC(p, ".") == True{} : Bool}:
  and_tt(pc(p, '.'), True{}, AB.and_true_r(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':'), pc(p, '.'), AB.and_true_l(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h)), {==})

def s_dig(+p: Cls, +h: {SEPS(p) == True{} : Bool}) -> {DIG(p) == True{} : Bool}:
  AB.and_true_r(pc(p, ',') && pc(p, '=') && pc(p, ';') && pc(p, ':') && pc(p, '.'), DIG(p), h)

def got_cat(+p: Cls, +a: B.Got, +sep: String, +b: B.Got, +ha: {GOK(p, a) == True{} : Bool}, +hs: {ALLC(p, sep) == True{} : Bool}, +hb: {GOK(p, b) == True{} : Bool}) ->
  {GOK(p, B.Got.cat(a, sep, b)) == True{} : Bool}:
  match a b:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+x} B.Refuse{+c}:
      {==}
    case B.Got{+x} B.Got{+y}:
      allc_app(p, x, String.append(sep, y), ha, allc_app(p, sep, y, hs, hb))

law got_join:
  for +p: Cls
  for +gs: List<&2, B.Got>
  for +sep: String
  for +h: {GOKS(p, gs) == True{} : Bool}
  for +hs: {ALLC(p, sep) == True{} : Bool}
  {GOK(p, B.Got.join(gs, sep)) == True{} : Bool}

def got_put(+p: Cls, +g: B.Got, +t: List<&2, B.Got>, +sep: String, +r: B.Got, +hg: {GOK(p, g) == True{} : Bool}, +hs: {ALLC(p, sep) == True{} : Bool}, +hr: {GOK(p, r) == True{} : Bool}) ->
  {GOK(p, B.Got.join.put(g, t, sep, r)) == True{} : Bool}:
  match t:
    case Nil{}:
      hg
    case Con{+x, +u}:
      got_cat(p, g, sep, r, hg, hs, hr)

def got_join(p, gs, sep, h, hs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      got_put(p, g, t, sep, B.Got.join(t, sep), AB.and_true_l(GOK(p, g), GOKS(p, t), h), hs, got_join(p, t, sep, AB.and_true_r(GOK(p, g), GOKS(p, t), h), hs))

def got_of(+p: Cls, +m: Maybe<&2, String>, +c: B.Code, +h: {MOK(p, m) == True{} : Bool}) -> {GOK(p, B.Got.of(m, c)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      h

law get_mok:
  for +p: Cls
  for +vs: Ss()
  for +k: Nat
  for +h: {ALLS(p, vs) == True{} : Bool}
  {MOK(p, List.get(&2, String, vs, k)) == True{} : Bool}

def get_mok(p, vs, k, h):
  match vs k:
    case Nil{} _:
      {==}
    case Con{+y, +t} 0n:
      AB.and_true_l(ALLC(p, y), ALLS(p, t), h)
    case Con{+y, +t} 1n+j:
      get_mok(p, t, j, AB.and_true_r(ALLC(p, y), ALLS(p, t), h))

def pcons(+p: Cls, +m: Maybe<&2, String>, +r: Maybe<&2, Ss()>, +hm: {MOK(p, m) == True{} : Bool}, +hr: {MLOK(p, r) == True{} : Bool}) ->
  {MLOK(p, B.Vals.pick.cons(m, r)) == True{} : Bool}:
  match m r:
    case Some{+x} Some{+xs}:
      and_tt(ALLC(p, x), ALLS(p, xs), hm, hr)
    case None{} _:
      {==}
    case Some{+x} None{}:
      {==}

law pick_ok:
  for +p: Cls
  for +vs: Ss()
  for +ks: List<&2, Nat>
  for +h: {ALLS(p, vs) == True{} : Bool}
  {MLOK(p, B.Vals.pick(vs, ks)) == True{} : Bool}

def pick_ok(p, vs, ks, h):
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      pcons(p, List.get(&2, String, vs, k), B.Vals.pick(vs, t), get_mok(p, vs, k, h), pick_ok(p, vs, t, h))

def vjoin(+p: Cls, +m: Maybe<&2, Ss()>, +h: {MLOK(p, m) == True{} : Bool}, +hc: {ALLC(p, ",") == True{} : Bool}) -> {MOK(p, B.Vals.join(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+xs}:
      join_all(p, xs, ",", h, hc)

def vkeep.k(+p: Cls, +c: Bool, +m: Maybe<&2, String>, +h: {MOK(p, m) == True{} : Bool}) -> {MOK(p, Bool.pick(Maybe<&2, String>, c, m, None{})) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

def vkeep(+p: Cls, +num: B.Num, +n: Nat, +q: Nat, +i: Nat, +vs: Ss(), +h: {ALLS(p, vs) == True{} : Bool}, +hc: {ALLC(p, ",") == True{} : Bool}) ->
  {MOK(p, B.Vals.keep(num, n, q, i, vs)) == True{} : Bool}:
  vkeep.k(p, B.Vals.fits(B.Vals.expected_count(num, n, q), List.length(&2, String, vs)), B.Vals.join(B.Vals.pick(vs, B.Vals.idx(num, q, i))),
    vjoin(p, B.Vals.pick(vs, B.Vals.idx(num, q, i)), pick_ok(p, vs, B.Vals.idx(num, q, i), h), hc))

def vsplit.if(+p: Cls, +miss: Bool, +num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +v: String,
  +h: {ALLC(p, v) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) -> {MOK(p, B.Vals.split.if(miss, num, n, cp, i, v)) == True{} : Bool}:
  match miss:
    case True{}:
      s_dot(p, hs)
    case False{}:
      +vs = String.split(v, ',')
      vkeep(p, num, n, B.Vals.copies(cp, n, List.length(&2, String, vs)), i, vs, split_all(p, v, ',', h), s_comma(p, hs))

# A per-allele value, split: its characters come from the value, ',' and '.'.
law vsplit:
  for +p: Cls
  for +num: B.Num
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +v: String
  for +h: {ALLC(p, v) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {MOK(p, B.Vals.split(num, n, cp, i, v)) == True{} : Bool}

def vsplit(p, num, n, cp, i, v, h, hs):
  vsplit.if(p, String.eq(v, "."), num, n, cp, i, v, h, hs)

# ---------------------------------------------------------------------------
# INFO
# ---------------------------------------------------------------------------

def mok_def(+p: Cls, +m: Maybe<&2, String>, +h: {MOK(p, m) == True{} : Bool}) -> {ALLC(p, Maybe.default(&2, String, m, "")) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      h

def field_all(+p: Cls, +xs: Ss(), +j: Nat, +h: {ALLS(p, xs) == True{} : Bool}) -> {ALLC(p, B.Rec.field(xs, j)) == True{} : Bool}:
  mok_def(p, List.get(&2, String, xs, j), get_mok(p, xs, j, h))

def key_all(+p: Cls, +e: String, +h: {ALLC(p, e) == True{} : Bool}) -> {ALLC(p, B.Info.key(e)) == True{} : Bool}:
  field_all(p, String.split(e, '='), 0n, split_all(p, e, '=', h))

def ieq.num(+p: Cls, +num: B.Num, +k: String, +e: String, +n: Nat, +i: Nat,
  +hk: {ALLC(p, k) == True{} : Bool}, +he: {ALLC(p, e) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Info.split.eq(Some{num}, k, e, n, i)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      he
    case B.NumA{}:
      got_cat(p, B.Got{k}, "=", B.Got.of(B.Vals.split(B.NumA{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}), hk, s_eq(p, hs),
        got_of(p, B.Vals.split(B.NumA{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}, vsplit(p, B.NumA{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n)), allc_drop(p, e, Nat.add(String.length(k), 1n), he), hs)))
    case B.NumR{}:
      got_cat(p, B.Got{k}, "=", B.Got.of(B.Vals.split(B.NumR{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}), hk, s_eq(p, hs),
        got_of(p, B.Vals.split(B.NumR{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}, vsplit(p, B.NumR{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n)), allc_drop(p, e, Nat.add(String.length(k), 1n), he), hs)))
    case B.NumG{}:
      got_cat(p, B.Got{k}, "=", B.Got.of(B.Vals.split(B.NumG{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}), hk, s_eq(p, hs),
        got_of(p, B.Vals.split(B.NumG{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}, vsplit(p, B.NumG{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n)), allc_drop(p, e, Nat.add(String.length(k), 1n), he), hs)))

def ieq(+p: Cls, +m: Maybe<&2, B.Num>, +k: String, +e: String, +n: Nat, +i: Nat,
  +hk: {ALLC(p, k) == True{} : Bool}, +he: {ALLC(p, e) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Info.split.eq(m, k, e, n, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      ieq.num(p, num, k, e, n, i, hk, he, hs)

def pick_got(+p: Cls, +c: Bool, +a: B.Got, +b: B.Got, +ha: {GOK(p, a) == True{} : Bool}, +hb: {GOK(p, b) == True{} : Bool}) -> {GOK(p, Bool.pick(B.Got, c, a, b)) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

def inum(+p: Cls, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +he: {ALLC(p, e) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Info.split.num(m, e, n, i)) == True{} : Bool}:
  +k = B.Info.key(e)
  pick_got(p, String.eq(k, e), Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, k, e, n, i),
    pick_got(p, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}, {==}, he),
    ieq(p, m, k, e, n, i, key_all(p, e, he), he, hs))

law igo:
  for +p: Cls
  for +es: Ss()
  for +info: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +h: {ALLS(p, es) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GOKS(p, B.Info.split.go(es, info, n, i)) == True{} : Bool}

def igo(p, es, info, n, i, h, hs):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      and_tt(GOK(p, B.Info.split.num(B.Tags.find(info, B.Info.key(e)), e, n, i)), GOKS(p, B.Info.split.go(t, info, n, i)),
        inum(p, B.Tags.find(info, B.Info.key(e)), e, n, i, AB.and_true_l(ALLC(p, e), ALLS(p, t), h), hs),
        igo(p, t, info, n, i, AB.and_true_r(ALLC(p, e), ALLS(p, t), h), hs))

# INFO in a record: its characters come from INFO, ';', ',', '=' and '.'.
law info_all:
  for +p: Cls
  for +info: String
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +h: {ALLC(p, info) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GOK(p, B.Info.split(info, tags, n, i)) == True{} : Bool}

def info_all(p, info, tags, n, i, h, hs):
  got_join(p, B.Info.split.go(String.split(info, ';'), tags, n, i), ";", igo(p, String.split(info, ';'), tags, n, i, split_all(p, info, ';', h), hs), s_semi(p, hs))

# ---------------------------------------------------------------------------
# GT and FORMAT
# ---------------------------------------------------------------------------

def gshow(+p: Cls, +a: Maybe<&2, Nat>, +hs: {SEPS(p) == True{} : Bool}) -> {ALLC(p, B.Gt.show(a)) == True{} : Bool}:
  match a:
    case None{}:
      s_dot(p, hs)
    case Some{+x}:
      show_all(p, x, s_dig(p, hs))

def gnum(+p: Cls, +m: Maybe<&2, Nat>, +over0: Bool, +n: Nat, +i: Nat, +hs: {SEPS(p) == True{} : Bool}) -> {GOK(p, B.Gt.num(m, over0, n, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+a}:
      pick_got(p, Nat.is_le(a, n), B.Got{B.Gt.show(B.Gt.rule(over0, i, Some{a}))}, B.Refuse{B.BadGt{}}, gshow(p, B.Gt.rule(over0, i, Some{a}), hs), {==})

def gallele(+p: Cls, +over0: Bool, +n: Nat, +i: Nat, +a: String, +hs: {SEPS(p) == True{} : Bool}) -> {GOK(p, B.Gt.allele(over0, n, i, a)) == True{} : Bool}:
  pick_got(p, String.eq(a, "."), B.Got{"."}, Bool.pick(B.Got, B.Gt.canon(a), B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}}), s_dot(p, hs),
    pick_got(p, B.Gt.canon(a), B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}}, gnum(p, B.Pos.read(a), over0, n, i, hs), {==}))

def GPOK(+p: Cls, r: B.Gp) -> Bool:
  match r:
    case B.Gp{tk, rs}:
      ALLC(p, tk) && GOK(p, rs)

def gput(+p: Cls, +sep: Bool, +h: Char, +r: B.Gp, +over0: Bool, +n: Nat, +i: Nat,
  +hh: {pc(p, h) == True{} : Bool}, +hr: {GPOK(p, r) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GPOK(p, B.Gt.go.put(sep, h, r, over0, n, i)) == True{} : Bool}:
  match sep r:
    case True{} B.Gp{+tk, +rs}:
      +hc = got_cat(p, B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk), and_tt(pc(p, h), True{}, hh, {==}), {==}, gallele(p, over0, n, i, tk, hs))
      and_tt(True{}, GOK(p, B.Got.cat(B.Got.cat(B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk)), "", rs)), {==},
        got_cat(p, B.Got.cat(B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk)), "", rs, hc, {==}, AB.and_true_r(ALLC(p, tk), GOK(p, rs), hr)))
    case False{} B.Gp{+tk, +rs}:
      and_tt(Bool.and(pc(p, h), ALLC(p, tk)), GOK(p, rs), and_tt(pc(p, h), ALLC(p, tk), hh, AB.and_true_l(ALLC(p, tk), GOK(p, rs), hr)), AB.and_true_r(ALLC(p, tk), GOK(p, rs), hr))

law ggo:
  for +p: Cls
  for +s: String
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +h: {ALLC(p, s) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GPOK(p, B.Gt.go(s, over0, n, i)) == True{} : Bool}

def ggo(p, s, over0, n, i, h, hs):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      gput(p, B.Gt.is_sep(c), c, B.Gt.go(t, over0, n, i), over0, n, i, AB.and_true_l(pc(p, c), ALLC(p, t), h), ggo(p, t, over0, n, i, AB.and_true_r(pc(p, c), ALLC(p, t), h), hs), hs)

def gof(+p: Cls, +r: B.Gp, +over0: Bool, +n: Nat, +i: Nat, +hr: {GPOK(p, r) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Gt.split.of(r, over0, n, i)) == True{} : Bool}:
  match r:
    case B.Gp{+tk, +rs}:
      got_cat(p, B.Gt.allele(over0, n, i, tk), "", rs, gallele(p, over0, n, i, tk, hs), {==}, AB.and_true_r(ALLC(p, tk), GOK(p, rs), hr))

def gsplit(+p: Cls, +over0: Bool, +n: Nat, +i: Nat, +g: String, +h: {ALLC(p, g) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Gt.split(over0, n, i, g)) == True{} : Bool}:
  gof(p, B.Gt.go(g, over0, n, i), over0, n, i, ggo(p, g, over0, n, i, h, hs), hs)

def fnum.k(+p: Cls, +num: B.Num, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {ALLC(p, v) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Fmt.split.num(Some{num}, k, v, n, cp, i)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      hv
    case B.NumA{}:
      got_of(p, B.Vals.split(B.NumA{}, n, cp, i, v), B.BadCount{}, vsplit(p, B.NumA{}, n, cp, i, v, hv, hs))
    case B.NumR{}:
      got_of(p, B.Vals.split(B.NumR{}, n, cp, i, v), B.BadCount{}, vsplit(p, B.NumR{}, n, cp, i, v, hv, hs))
    case B.NumG{}:
      got_of(p, B.Vals.split(B.NumG{}, n, cp, i, v), B.BadCount{}, vsplit(p, B.NumG{}, n, cp, i, v, hv, hs))

def fnum(+p: Cls, +m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {ALLC(p, v) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Fmt.split.num(m, k, v, n, cp, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      fnum.k(p, num, k, v, n, cp, i, hv, hs)

def fone(+p: Cls, +k: String, +v: String, +fmt: List<&2, B.Tag>, +over0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {ALLC(p, v) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Fmt.split.one(k, v, fmt, over0, n, cp, i)) == True{} : Bool}:
  pick_got(p, String.eq(k, "GT"), B.Gt.split(over0, n, i, v), B.Fmt.split.num(B.Tags.find(fmt, k), k, v, n, cp, i), gsplit(p, over0, n, i, v, hv, hs), fnum(p, B.Tags.find(fmt, k), k, v, n, cp, i, hv, hs))

law fgo:
  for +p: Cls
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +over0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +h: {ALLS(p, vs) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GOKS(p, B.Fmt.split.go(ks, vs, fmt, over0, n, cp, i)) == True{} : Bool}

def fgo(p, ks, vs, fmt, over0, n, cp, i, h, hs):
  match ks vs:
    case _ Nil{}:
      {==}
    case Nil{} Con{+v, +t}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      and_tt(GOK(p, B.Fmt.split.one(k, v, fmt, over0, n, cp, i)), GOKS(p, B.Fmt.split.go(kt, vt, fmt, over0, n, cp, i)),
        fone(p, k, v, fmt, over0, n, cp, i, AB.and_true_l(ALLC(p, v), ALLS(p, vt), h), hs),
        fgo(p, kt, vt, fmt, over0, n, cp, i, AB.and_true_r(ALLC(p, v), ALLS(p, vt), h), hs))

# A sample column in a record: its characters come from the column, ':', ',', '.' and digits.
law fmt_all:
  for +p: Cls
  for +ks: Ss()
  for +col: String
  for +fmt: List<&2, B.Tag>
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +h: {ALLC(p, col) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GOK(p, B.Fmt.split(ks, col, fmt, over0, n, i)) == True{} : Bool}

def fmt_all(p, ks, col, fmt, over0, n, i, h, hs):
  +vs = String.split(col, ':')
  got_join(p, B.Fmt.split.go(ks, vs, fmt, over0, n, B.Gt.copies(B.Fmt.gt(ks, vs)), i), ":",
    fgo(p, ks, vs, fmt, over0, n, B.Gt.copies(B.Fmt.gt(ks, vs)), i, split_all(p, col, ':', h), hs), s_colon(p, hs))

# ---------------------------------------------------------------------------
# Records
# ---------------------------------------------------------------------------

def pfield(+p: Cls, +j: Nat, +f: String, +a: String, +defs: B.Defs, +ks: Ss(), +over0: Bool, +n: Nat, +i: Nat,
  +hf: {ALLC(p, f) == True{} : Bool}, +ha: {ALLC(p, a) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}) ->
  {GOK(p, B.Rec.piece.field(j, f, a, defs, ks, over0, n, i)) == True{} : Bool}:
  pick_got(p, Nat.is_eq(j, 4n), B.Got{a}, Bool.pick(B.Got, Nat.is_eq(j, 7n), B.Info.split(f, B.Defs.info(defs), n, i), Bool.pick(B.Got, Nat.is_le(9n, j), B.Fmt.split(ks, f, B.Defs.fmt(defs), over0, n, i), B.Got{f})), ha,
    pick_got(p, Nat.is_eq(j, 7n), B.Info.split(f, B.Defs.info(defs), n, i), Bool.pick(B.Got, Nat.is_le(9n, j), B.Fmt.split(ks, f, B.Defs.fmt(defs), over0, n, i), B.Got{f}), info_all(p, f, B.Defs.info(defs), n, i, hf, hs),
      pick_got(p, Nat.is_le(9n, j), B.Fmt.split(ks, f, B.Defs.fmt(defs), over0, n, i), B.Got{f}, fmt_all(p, ks, f, B.Defs.fmt(defs), over0, n, i, hf, hs), hf)))

law pgo:
  for +p: Cls
  for +fs: Ss()
  for +j: Nat
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +h: {ALLS(p, fs) == True{} : Bool}
  for +ha: {ALLC(p, a) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  {GOKS(p, B.Rec.piece.go(fs, j, a, defs, ks, over0, n, i)) == True{} : Bool}

def pgo(p, fs, j, a, defs, ks, over0, n, i, h, ha, hs):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      and_tt(GOK(p, B.Rec.piece.field(j, f, a, defs, ks, over0, n, i)), GOKS(p, B.Rec.piece.go(t, 1n+j, a, defs, ks, over0, n, i)),
        pfield(p, j, f, a, defs, ks, over0, n, i, AB.and_true_l(ALLC(p, f), ALLS(p, t), h), ha, hs),
        pgo(p, t, 1n+j, a, defs, ks, over0, n, i, AB.and_true_r(ALLC(p, f), ALLS(p, t), h), ha, hs))

# The record for one ALT (fields joined by tabs, which must have p).
def piece_all(+p: Cls, +fs: Ss(), +a: String, +defs: B.Defs, +over0: Bool, +n: Nat, +i: Nat,
  +h: {ALLS(p, fs) == True{} : Bool}, +ha: {ALLC(p, a) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}, +ht: {ALLC(p, "\t") == True{} : Bool}) ->
  {GOK(p, B.Rec.piece(fs, a, defs, over0, n, i)) == True{} : Bool}:
  +ks = String.split(B.Rec.field(fs, 8n), ':')
  got_join(p, B.Rec.piece.go(fs, 0n, a, defs, ks, over0, n, i), "\t", pgo(p, fs, 0n, a, defs, ks, over0, n, i, h, ha, hs), ht)

law pieces_go:
  for +p: Cls
  for +alts: Ss()
  for +fs: Ss()
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +h: {ALLS(p, fs) == True{} : Bool}
  for +ha: {ALLS(p, alts) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  for +ht: {ALLC(p, "\t") == True{} : Bool}
  {GOKS(p, B.Rec.pieces.go(alts, fs, defs, over0, n, i)) == True{} : Bool}

def pieces_go(p, alts, fs, defs, over0, n, i, h, ha, hs, ht):
  match alts:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_tt(GOK(p, B.Rec.piece(fs, a, defs, over0, n, i)), GOKS(p, B.Rec.pieces.go(t, fs, defs, over0, n, 1n+i)),
        piece_all(p, fs, a, defs, over0, n, i, h, AB.and_true_l(ALLC(p, a), ALLS(p, t), ha), hs, ht),
        pieces_go(p, t, fs, defs, over0, n, 1n+i, h, AB.and_true_r(ALLC(p, a), ALLS(p, t), ha), hs, ht))

# Parts.of giving Pieces: the pieces' texts.
def is_pieces(pt: B.Parts) -> Bool:
  match pt:
    case B.Pieces{ps}:
      True{}
    case _:
      False{}

def pieces_of(pt: B.Parts) -> Ss():
  match pt:
    case B.Pieces{ps}:
      ps
    case _:
      Nil{}

def gtext(g: B.Got) -> String:
  match g:
    case B.Got{s}:
      s
    case B.Refuse{c}:
      ""

def pcons_k(+p: Cls, +x: String, +r: B.Parts, +ps: Ss(), +h: {B.Parts.cons(B.Got{x}, r) == B.Pieces{ps} : B.Parts},
  +hx: {ALLC(p, x) == True{} : Bool},
  ih: @+qs: Ss() -> {r == B.Pieces{qs} : B.Parts} -> {ALLS(p, qs) == True{} : Bool}) -> {ALLS(p, ps) == True{} : Bool}:
  match r:
    case B.Pieces{+qs}:
      %Equal.sym(Ss(), ps, x <> qs, Equal.sym(Ss(), x <> qs, ps, Equal.cong(B.Parts, Ss(), pieces_of, B.Pieces{x <> qs}, B.Pieces{ps}, h))) : {ALLS(p, _) == True{} : Bool}
      and_tt(ALLC(p, x), ALLS(p, qs), hx, ih(qs, {==}))
    case B.Whole{}:
      Empty.absurd({ALLS(p, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h)))
    case B.Unsplit{+c}:
      Empty.absurd({ALLS(p, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

def pcons_g(+p: Cls, +g: B.Got, +r: B.Parts, +ps: Ss(), +h: {B.Parts.cons(g, r) == B.Pieces{ps} : B.Parts},
  +hg: {GOK(p, g) == True{} : Bool},
  ih: @+qs: Ss() -> {r == B.Pieces{qs} : B.Parts} -> {ALLS(p, qs) == True{} : Bool}) -> {ALLS(p, ps) == True{} : Bool}:
  match g:
    case B.Got{+x}:
      pcons_k(p, x, r, ps, h, hg, ih)
    case B.Refuse{+c}:
      Empty.absurd({ALLS(p, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

law of_all:
  for +p: Cls
  for +gs: List<&2, B.Got>
  for +ps: Ss()
  for +h: {B.Parts.of(gs) == B.Pieces{ps} : B.Parts}
  for +hg: {GOKS(p, gs) == True{} : Bool}
  {ALLS(p, ps) == True{} : Bool}

def of_all(p, gs, ps, h, hg):
  match gs:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {ALLS(p, _) == True{} : Bool}
      {==}
    case Con{+g, +t}:
      pcons_g(p, g, B.Parts.of(t), ps, h, AB.and_true_l(GOK(p, g), GOKS(p, t), hg),
        +qs => hq => of_all(p, t, qs, hq, AB.and_true_r(GOK(p, g), GOKS(p, t), hg)))

def COND(+sp: Bool, +fs: Ss()) -> Bool:
  Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))))

def pa_split(+p: Cls, +d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hb: {ALLC(p, body) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}, +ht: {ALLC(p, "\t") == True{} : Bool}) ->
  {ALLS(p, ps) == True{} : Bool}:
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({ALLS(p, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%ed : {B.Rec.parts.split(_, al, fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, al, fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      +hfs = split_all(p, body, '\t', hb)
      of_all(p, B.Rec.pieces.go(al, fs, defs, o0, List.length(&2, String, al), 1n), ps, h2,
        pieces_go(p, al, fs, defs, o0, List.length(&2, String, al), 1n, hfs, split_all(p, B.Rec.field(fs, 4n), ',', field_all(p, fs, 4n, hfs)), hs, ht))

def pa_if(+p: Cls, +c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts},
  +hb: {ALLC(p, body) == True{} : Bool}, +hs: {SEPS(p) == True{} : Bool}, +ht: {ALLC(p, "\t") == True{} : Bool}) ->
  {ALLS(p, ps) == True{} : Bool}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({ALLS(p, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      pa_split(p, B.Alts.distinct(B.Rec.alts(fs)), defs, o0, body, ps, {==}, h2, hb, hs, ht)

# The records of a split line: any property of characters the line, the tab,
# the separators, '.' and the digits have, every record has.
law parts_chars:
  for +p: Cls
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +hb: {ALLC(p, body) == True{} : Bool}
  for +hs: {SEPS(p) == True{} : Bool}
  for +ht: {ALLC(p, "\t") == True{} : Bool}
  {ALLS(p, ps) == True{} : Bool}

def parts_chars(p, defs, o, body, ps, h, hb, hs, ht):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      pa_if(p, COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h), hb, hs, ht)
