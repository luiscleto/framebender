import Base
import ./types.bend as B
import ./proof_base.bend as P
import ./proof_run_base.bend as Q

# Decimal numbers: B.Pos.read(Nat.show(n)) == Some{n}, and Nat.show writes
# only digits.

def fst(p: Nat & Nat) -> Nat:
  Pair.fst(Nat, Nat, p)

def snd(p: Nat & Nat) -> Nat:
  Pair.snd(Nat, Nat, p)

# divmod by 10
# ============

def DMP(+n: Nat, +d: Nat, +r: Nat, p: Nat & Nat) -> Type:
  {Nat.add(snd(p), Nat.mul(fst(p), 10n)) == Nat.add(n, Nat.add(r, Nat.mul(d, 10n))) : Nat} & {Nat.is_le(snd(p), 9n) == True{} : Bool}

def dm_go.fix(+np: Nat, +d: Nat, +r: Nat, +er: {r == 9n : Nat},
  ih: DMP(np, 1n+d, 0n, Nat.divmod.go(np, r, 1n+d, 0n))) -> DMP(1n+np, d, r, Nat.divmod.go(np, r, 1n+d, 0n)):
  match ih:
    case (e1, e2):
      -p = Nat.divmod.go(np, r, 1n+d, 0n)
      %Equal.sym(Nat, r, 9n, er) : {Nat.add(snd(p), Nat.mul(fst(p), 10n)) == Nat.add(1n+np, Nat.add(_, Nat.mul(d, 10n))) : Nat} & {Nat.is_le(snd(p), 9n) == True{} : Bool}
      (Equal.trans(Nat, Nat.add(snd(p), Nat.mul(fst(p), 10n)), Nat.add(np, Nat.add(0n, Nat.mul(1n+d, 10n))),
        1n+Nat.add(np, Nat.add(9n, Nat.mul(d, 10n))), e1, P.add_succ(np, Nat.add(9n, Nat.mul(d, 10n)))), e2)

def dm_go.inc(+np: Nat, +mp: Nat, +d: Nat, +r: Nat,
  ih: DMP(np, d, 1n+r, Nat.divmod.go(np, mp, d, 1n+r))) -> DMP(1n+np, d, r, Nat.divmod.go(np, mp, d, 1n+r)):
  match ih:
    case (e1, e2):
      -p = Nat.divmod.go(np, mp, d, 1n+r)
      (Equal.trans(Nat, Nat.add(snd(p), Nat.mul(fst(p), 10n)), Nat.add(np, Nat.add(1n+r, Nat.mul(d, 10n))),
        1n+Nat.add(np, Nat.add(r, Nat.mul(d, 10n))), e1, P.add_succ(np, Nat.add(r, Nat.mul(d, 10n)))), e2)

# divmod.go counts r up to 9 (m down to 0), then starts the next ten.
law dm_go:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +h: {Nat.add(m, r) == 9n : Nat}
  DMP(n, d, r, Nat.divmod.go(n, m, d, r))

def dm_go(n, m, d, r, h):
  match n:
    case 0n:
      +le = {(%h : {Nat.is_le(r, _) == True{} : Bool}; Q.le_add_l(m, r)) : {Nat.is_le(r, 9n) == True{} : Bool}}
      ({==}, le)
    case 1n+np:
      match m:
        case 0n:
          dm_go.fix(np, d, r, h, dm_go(np, r, 1n+d, 0n,
            (%Equal.sym(Nat, r, 9n, h) : {Nat.add(_, 0n) == 9n : Nat}; {==})))
        case 1n+mp:
          dm_go.inc(np, mp, d, r, dm_go(np, mp, d, 1n+r,
            Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), 9n, P.add_succ(mp, r), h)))

def dm_pair(+n: Nat, r: DMP(n, 0n, 0n, Nat.divmod(n, 10n))) ->
  {Nat.add(snd(Nat.divmod(n, 10n)), Nat.mul(fst(Nat.divmod(n, 10n)), 10n)) == n : Nat} & {Nat.is_le(snd(Nat.divmod(n, 10n)), 9n) == True{} : Bool}:
  match r:
    case (e1, e2):
      (Equal.trans(Nat, Nat.add(snd(Nat.divmod(n, 10n)), Nat.mul(fst(Nat.divmod(n, 10n)), 10n)), Nat.add(n, 0n), n, e1, P.add_zero(n)), e2)

# n == r + 10 q with r <= 9, for (q, r) = divmod(n, 10).
law dm10:
  for +n: Nat
  {Nat.add(snd(Nat.divmod(n, 10n)), Nat.mul(fst(Nat.divmod(n, 10n)), 10n)) == n : Nat} & {Nat.is_le(snd(Nat.divmod(n, 10n)), 9n) == True{} : Bool}

def dm10(n):
  dm_pair(n, dm_go(n, 9n, 0n, 0n, {==}))

# Nat.show
# ========

law pair_eta:
  for p: Nat & Nat
  {p == (fst(p), snd(p)) : Nat & Nat}

def pair_eta(p):
  match p:
    case (a, b):
      {==}

def fin_acc(+g: Nat, +acc: String, dq: Char & Nat,
  ih1: @n: Nat -> @a: String -> {Nat.show.go(g, n, a) == Nat.show.go(g, n, "") ++ a : String},
  ih2: @n: Nat -> @a: String -> {Nat.show.go(g, n, a) == Nat.show.go(g, n, "") ++ a : String}) ->
  {Nat.show.fin(g, acc, dq) == Nat.show.fin(g, "", dq) ++ acc : String}:
  match dq:
    case (+d, q):
      match q:
        case 0n:
          {==}
        case 1n+(+p):
          +x = Nat.show.go(g, 1n+p, "")
          %Equal.sym(String, Nat.show.go(g, 1n+p, SCon{d, acc}), x ++ SCon{d, acc}, ih1(1n+p, SCon{d, acc})) : {_ == Nat.show.go(g, 1n+p, SCon{d, ""}) ++ acc : String}
          %Equal.sym(String, Nat.show.go(g, 1n+p, SCon{d, ""}), x ++ SCon{d, ""}, ih2(1n+p, SCon{d, ""})) : {x ++ SCon{d, acc} == _ ++ acc : String}
          Equal.sym(String, (x ++ SCon{d, ""}) ++ acc, x ++ SCon{d, acc}, Q.s_append_assoc(x, SCon{d, ""}, acc))

# Nat.show.go writes its digits before its accumulator.
law go_acc:
  for +f: Nat
  for +n: Nat
  for +acc: String
  {Nat.show.go(f, n, acc) == Nat.show.go(f, n, "") ++ acc : String}

def go_acc(f, n, acc):
  match f:
    case 0n:
      {==}
    case 1n+g:
      fin_acc(g, acc, Nat.show.put(Nat.divmod(n, 10n)), n2 => a2 => go_acc(g, n2, a2), n2 => a2 => go_acc(g, n2, a2))

law read_snoc:
  for +s: String
  for +c: Char
  for acc: Maybe<&2, Nat>
  {B.Pos.read.go(s ++ SCon{c, ""}, acc) == B.Pos.read.push(B.Pos.read.go(s, acc), B.Pos.digit(c)) : Maybe<&2, Nat>}

def read_snoc(s, c, acc):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      read_snoc(t, c, B.Pos.read.push(acc, B.Pos.digit(h)))

law digit_ok:
  for +r: Nat
  for h: {Nat.is_le(r, 9n) == True{} : Bool}
  {B.Pos.digit(Chr{U32.from_nat(Nat.add(48n, r))}) == Some{r} : Maybe<&2, Nat>}

def digit_ok(r, h):
  match r:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+k:
      Empty.absurd({B.Pos.digit(Chr{U32.from_nat(Nat.add(48n, 10n+k))}) == Some{10n+k} : Maybe<&2, Nat>}, P.false_ne_true(h))

law le_mul10:
  for +p: Nat
  {Nat.is_le(p, Nat.mul(p, 10n)) == True{} : Bool}

def le_mul10(p):
  match p:
    case 0n:
      {==}
    case 1n+k:
      Q.le_trans(k, Nat.mul(k, 10n), 9n+Nat.mul(k, 10n), le_mul10(k), Q.le_add_l(9n, Nat.mul(k, 10n)))

def SHT(+g: Nat, +m: Nat) -> Type:
  {B.Pos.read.go(Nat.show.fin(g, "", Nat.show.put(Nat.divmod(m, 10n))), Some{0n}) == Some{m} : Maybe<&2, Nat>}

def sh.go(q: Nat, g: Nat, +m: Nat, +r: Nat,
  +dm: {Nat.add(r, Nat.mul(q, 10n)) == m : Nat}, +hr: {Nat.is_le(r, 9n) == True{} : Bool},
  +hm: {Nat.is_le(m, g) == True{} : Bool},
  ih: @g2: Nat -> @m2: Nat -> {g == 1n+g2 : Nat} -> {Nat.is_le(m2, g2) == True{} : Bool} -> SHT(g2, m2)) ->
  {B.Pos.read.go(Nat.show.fin(g, "", (Chr{U32.from_nat(Nat.add(48n, r))}, q)), Some{0n}) == Some{m} : Maybe<&2, Nat>}:
  match q g:
    case 0n _:
      +dch = {Chr{U32.from_nat(Nat.add(48n, r))} : Char}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.digit(dch), Some{r}, digit_ok(r, hr)) : {B.Pos.read.push(Some{0n}, _) == Some{m} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, r, m,
        Equal.trans(Nat, r, Nat.add(r, 0n), m, Equal.sym(Nat, Nat.add(r, 0n), r, P.add_zero(r)), dm))
    case 1n+p 0n:
      +dch = {Chr{U32.from_nat(Nat.add(48n, r))} : Char}
      +x = Nat.mul(1n+p, 10n)
      Empty.absurd({B.Pos.read.go(Nat.show.fin(0n, "", (dch, 1n+p)), Some{0n}) == Some{m} : Maybe<&2, Nat>},
        P.false_ne_true(Q.le_trans(x, m, 0n, (%dm : {Nat.is_le(x, _) == True{} : Bool}; Q.le_add_l(r, x)), hm)))
    case 1n+(+p) 1n+(+g2):
      +dch = {Chr{U32.from_nat(Nat.add(48n, r))} : Char}
      +q = {1n+p : Nat}
      +X = Nat.show.go(1n+g2, q, "")
      +x = Nat.mul(q, 10n)
      +hq0 = {(%dm : {Nat.is_le(1n+q, _) == True{} : Bool}; Q.le_trans(1n+q, x, Nat.add(r, x), Q.le_trans(p, Nat.mul(p, 10n), 8n+Nat.mul(p, 10n), le_mul10(p), Q.le_add_l(8n, Nat.mul(p, 10n))), Q.le_add_l(r, x))) :
        {Nat.is_le(1n+q, m) == True{} : Bool}}
      +hq = {Q.le_trans(1n+q, m, 1n+g2, hq0, hm) : {Nat.is_le(q, g2) == True{} : Bool}}
      %Equal.sym(String, Nat.show.go(1n+g2, q, SCon{dch, ""}), X ++ SCon{dch, ""}, go_acc(1n+g2, q, SCon{dch, ""})) :
        {B.Pos.read.go(_, Some{0n}) == Some{m} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(X ++ SCon{dch, ""}, Some{0n}), B.Pos.read.push(B.Pos.read.go(X, Some{0n}), B.Pos.digit(dch)),
        read_snoc(X, dch, Some{0n})) : {_ == Some{m} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(X, Some{0n}), Some{q}, ih(g2, q, {==}, hq)) :
        {B.Pos.read.push(_, B.Pos.digit(dch)) == Some{m} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.digit(dch), Some{r}, digit_ok(r, hr)) : {B.Pos.read.push(Some{q}, _) == Some{m} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, Nat.add(x, r), m,
        Equal.trans(Nat, Nat.add(x, r), Nat.add(r, x), m, P.add_comm(x, r), dm))

def sh_main.go(+g: Nat, +m: Nat, r: {Nat.add(snd(Nat.divmod(m, 10n)), Nat.mul(fst(Nat.divmod(m, 10n)), 10n)) == m : Nat} & {Nat.is_le(snd(Nat.divmod(m, 10n)), 9n) == True{} : Bool},
  +hm: {Nat.is_le(m, g) == True{} : Bool},
  ih: @g2: Nat -> @m2: Nat -> {g == 1n+g2 : Nat} -> {Nat.is_le(m2, g2) == True{} : Bool} -> SHT(g2, m2)) -> SHT(g, m):
  match r:
    case (dm, hr):
      %Equal.sym(Nat & Nat, Nat.divmod(m, 10n), (fst(Nat.divmod(m, 10n)), snd(Nat.divmod(m, 10n))), pair_eta(Nat.divmod(m, 10n))) :
        {B.Pos.read.go(Nat.show.fin(g, "", Nat.show.put(_)), Some{0n}) == Some{m} : Maybe<&2, Nat>}
      sh.go(fst(Nat.divmod(m, 10n)), g, m, snd(Nat.divmod(m, 10n)), dm, hr, hm, ih)

law sh_main:
  for +g: Nat
  for +m: Nat
  for +hm: {Nat.is_le(m, g) == True{} : Bool}
  SHT(g, m)

def sh_main(g, m, hm):
  match g:
    case 0n:
      sh_main.go(0n, m, dm10(m), hm, g2 => m2 => eg => h2 => Empty.absurd(SHT(g2, m2), P.succ_ne_zero(g2, Equal.sym(Nat, 0n, 1n+g2, eg))))
    case 1n+(+k):
      sh_main.go(1n+k, m, dm10(m), hm, g2 => m2 => eg => h2 =>
        +e = P.succ_inj(k, g2, eg)
        %e : SHT(_, m2)
        sh_main(k, m2, (%Equal.sym(Nat, k, g2, e) : {Nat.is_le(m2, _) == True{} : Bool}; h2)))

def read_ne(+X: String, +d: Char) -> {B.Pos.read(X ++ SCon{d, ""}) == B.Pos.read.go(X ++ SCon{d, ""}, Some{0n}) : Maybe<&2, Nat>}:
  match X:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      {==}

def read_top(+g: Nat, dq: Char & Nat, +m: Nat, e: {B.Pos.read.go(Nat.show.fin(g, "", dq), Some{0n}) == Some{m} : Maybe<&2, Nat>}) ->
  {B.Pos.read(Nat.show.fin(g, "", dq)) == Some{m} : Maybe<&2, Nat>}:
  match dq:
    case (+d, q):
      match q:
        case 0n:
          e
        case 1n+(+p):
          +X = Nat.show.go(g, 1n+p, "")
          %Equal.sym(String, Nat.show.go(g, 1n+p, SCon{d, ""}), X ++ SCon{d, ""}, go_acc(g, 1n+p, SCon{d, ""})) :
            {B.Pos.read(_) == Some{m} : Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, B.Pos.read(X ++ SCon{d, ""}), B.Pos.read.go(X ++ SCon{d, ""}, Some{0n}), read_ne(X, d)) :
            {_ == Some{m} : Maybe<&2, Nat>}
          %go_acc(g, 1n+p, SCon{d, ""}) : {B.Pos.read.go(_, Some{0n}) == Some{m} : Maybe<&2, Nat>}
          e

# Reading back a number written in decimal.
law show_read:
  for +n: Nat
  {B.Pos.read(Nat.show(n)) == Some{n} : Maybe<&2, Nat>}

def show_read(n):
  read_top(n, Nat.show.put(Nat.divmod(n, 10n)), n, sh_main(n, n, P.le_refl(n)))

# Only digits
# ===========

def all_dig(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Maybe.is_some(&2, Nat, B.Pos.digit(h)) && all_dig(t)

law read_go_none:
  for +s: String
  {B.Pos.read.go(s, None{}) == None{} : Maybe<&2, Nat>}

def read_go_none(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      read_go_none(t)

def push_none(acc: Maybe<&2, Nat>) -> {B.Pos.read.push(acc, None{}) == None{} : Maybe<&2, Nat>}:
  match acc:
    case None{}:
      {==}
    case Some{a}:
      {==}

def mdisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_ne_some(-n: Nat, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> Empty:
  %e : mdisc(_)
  Unit{}

def read_digits.go(+h: Char, +t: String, acc: Maybe<&2, Nat>, -n: Nat, x: Maybe<&2, Nat>, ex: {B.Pos.digit(h) == x : Maybe<&2, Nat>},
  e: {B.Pos.read.go(t, B.Pos.read.push(acc, x)) == Some{n} : Maybe<&2, Nat>},
  ih: @a: Maybe<&2, Nat> -> {B.Pos.read.go(t, a) == Some{n} : Maybe<&2, Nat>} -> {all_dig(t) == True{} : Bool}) ->
  {all_dig(SCon{h, t}) == True{} : Bool}:
  match x:
    case None{}:
      Empty.absurd({all_dig(SCon{h, t}) == True{} : Bool},
        none_ne_some(n, Equal.trans(Maybe<&2, Nat>, None{}, B.Pos.read.go(t, B.Pos.read.push(acc, None{})), Some{n},
          (%Equal.sym(Maybe<&2, Nat>, B.Pos.read.push(acc, None{}), None{}, push_none(acc)) : {None{} == B.Pos.read.go(t, _) : Maybe<&2, Nat>}; Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(t, None{}), None{}, read_go_none(t))), e)))
    case Some{k}:
      %Equal.sym(Maybe<&2, Nat>, B.Pos.digit(h), Some{k}, ex) : {Bool.and(Maybe.is_some(&2, Nat, _), all_dig(t)) == True{} : Bool}
      ih(B.Pos.read.push(acc, Some{k}), e)

# A text read as a number has only digits.
law read_digits:
  for +s: String
  for acc: Maybe<&2, Nat>
  for -n: Nat
  for e: {B.Pos.read.go(s, acc) == Some{n} : Maybe<&2, Nat>}
  {all_dig(s) == True{} : Bool}

def read_digits(s, acc, n, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      read_digits.go(h, t, acc, n, B.Pos.digit(h), {==}, e, a => ea => read_digits(t, a, n, ea))

law show_digits:
  for +n: Nat
  {all_dig(Nat.show(n)) == True{} : Bool}

def show_digits(n):
  read_digits(Nat.show(n), Some{0n}, n, sh_main(n, n, P.le_refl(n)))
