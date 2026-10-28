import Base
import ./norm.bend as Norm
import ./norm_line.bend as J
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_ne.bend as E
import ./proof_b_cut_str.bend as S
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_find.bend as PF
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-bytes/proof_shift.bend as PSh

# INFO's END test: the bytes loop (M.NE, the mirror of NF.noend) passing
# means J.noend passes on INFO's text.

def HENDC(+xs: List<&2, U32>, +to: Nat, +b: Nat) -> Type:
  {(Bool.not(Nat.is_lt(to, b)) || D.has(xs, to, 9)) == True{} : Bool}

def hend_k(+xs: List<&2, U32>, +to: Nat, +b: Nat, +hc: {(Bool.not(Nat.is_lt(to, b)) || D.has(xs, to, 9)) == True{} : Bool},
  +h: {Nat.is_lt(to, b) == True{} : Bool}) -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>}:
  Z.some_of(List.get(&2, U32, xs, to), 9, AB.subst(Bool, z => {(Bool.not(z) || D.has(xs, to, 9)) == True{} : Bool}, Nat.is_lt(to, b), True{}, h, hc))

def hend_of(+xs: List<&2, U32>, +to: Nat, +b: Nat, +hc: {(Bool.not(Nat.is_lt(to, b)) || D.has(xs, to, 9)) == True{} : Bool}) -> E.HEND(xs, to, b):
  h => hend_k(xs, to, b, hc, h)

def ng_ff(+f: Nat, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +y: U32) ->
  {M.NG2(f, len, t, from, to, y, False{}, False{}) == False{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def lt_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +k: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hk: {Nat.is_lt(k, Z.n(len)) == True{} : Bool}) -> {Nat.is_lt(k, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, Z.n(len), List.length(&2, U32, Z.X(len, t)), Equal.sym(Nat, List.length(&2, U32, Z.X(len, t)), Z.n(len), Z.vlen(len, t, d, hok)), hk)

def at_xv(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Z.n(j) == k : Nat}, +hk: {Nat.is_lt(k, Z.n(len)) == True{} : Bool}) -> {C.AT(len, t, j) == E.XV(Z.X(len, t), k) : U32}:
  +xs = Z.X(len, t)
  +g1 = PF.step_get(len, t, d, j, hok, AB.subst(Nat, z => {Nat.is_lt(z, Z.n(len)) == True{} : Bool}, k, Z.n(j), Equal.sym(Nat, Z.n(j), k, hj), hk))
  +g2 = E.get_xv(xs, k, lt_len(len, t, d, k, hok, hk))
  S.some_eq(C.AT(len, t, j), E.XV(xs, k), Equal.trans(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, xs, k), Some{E.XV(xs, k)},
    Equal.sym(Maybe<&2, U32>, List.get(&2, U32, xs, k), Some{C.AT(len, t, j)}, AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{C.AT(len, t, j)} : Maybe<&2, U32>}, Z.n(j), k, hj, g1)), g2))

def START(+len: U32, +t: AT.Tree<U32>, +from: U32, +j: U32) -> Bool:
  U32.is_eq(j, from) || U32.is_eq(C.AT(len, t, (j - 1 : U32)), 59)

def KEYG(+a: Bool, +b: Bool, +c: Bool, +x3: U32) -> Bool:
  a && b && (c || U32.is_eq(x3, 61) || U32.is_eq(x3, 59))

def KEY(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> Bool:
  KEYG(U32.is_eq(C.AT(len, t, (j + 1 : U32)), 78), U32.is_eq(C.AT(len, t, (j + 2 : U32)), 68), U32.is_eq((j + 3 : U32), to), C.AT(len, t, (j + 3 : U32)))

def end_sk(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) -> {M.END(len, t, from, to, j) == (START(len, t, from, j) && KEY(len, t, to, j)) : Bool}:
  {==}

def and_true_l_id(+b: Bool) -> {Bool.and(True{}, b) == b : Bool}:
  {==}

def e_k2(+k: Nat) -> {Nat.add(Nat.add(k, 1n), 1n) == Nat.add(k, 2n) : Nat}:
  N.add_assoc(k, 1n, 1n)

def e_k3(+k: Nat) -> {Nat.add(Nat.add(Nat.add(k, 1n), 1n), 1n) == Nat.add(k, 3n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(k, 1n), 1n), 1n), Nat.add(Nat.add(k, 2n), 1n), Nat.add(k, 3n),
    Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(Nat.add(k, 1n), 1n), Nat.add(k, 2n), e_k2(k)), N.add_assoc(k, 2n, 1n))

# Word j + i is byte k + i, for k + i inside the buffer.
def pj(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +i: U32, +k: Nat, +ki: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Z.n(j) == k : Nat}, +hki: {Nat.add(k, Z.n(i)) == ki : Nat}, +hlt: {Nat.is_lt(ki, Z.n(len)) == True{} : Bool}) ->
  {Z.n((j + i : U32)) == ki : Nat}:
  +h4 = N.lt_to_le(ki, Nat.mul(4n, Nat.pow(2n, d)), N.lt_le_trans(ki, Z.n(len), Nat.mul(4n, Nat.pow(2n, d)), hlt, C.ok_len(len, t, d, hok)))
  +hs = Equal.trans(Nat, Nat.add(Z.n(j), Z.n(i)), Nat.add(k, Z.n(i)), ki, Equal.cong(Nat, Nat, z => Nat.add(z, Z.n(i)), Z.n(j), k, hj), hki)
  Equal.trans(Nat, Z.n((j + i : U32)), Nat.add(Z.n(j), Z.n(i)), ki,
    C.add_fits(j, i, d, C.ok_d(len, t, d, hok), AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}, ki, Nat.add(Z.n(j), Z.n(i)), Equal.sym(Nat, Nat.add(Z.n(j), Z.n(i)), ki, hs), h4)),
    hs)

# A failed key test, in list terms.
def key_kf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +k: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Z.n(j) == k : Nat}, +h2lt: {Nat.is_lt(Nat.add(Nat.add(k, 1n), 1n), Z.n(to)) == True{} : Bool},
  +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +hkey: {KEY(len, t, to, j) == False{} : Bool},
  +h1: {U32.is_eq(E.XV(Z.X(len, t), Nat.add(k, 1n)), 78) == True{} : Bool},
  +h2: {U32.is_eq(E.XV(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n)), 68) == True{} : Bool}) ->
  E.KF(Z.X(len, t), Nat.add(Nat.add(Nat.add(k, 1n), 1n), 1n), Z.n(to)):
  +xs = Z.X(len, t)
  +k1 = Nat.add(k, 1n)
  +k2 = Nat.add(k1, 1n)
  +k3 = Nat.add(k2, 1n)
  +hk3 = C.succ_le(k2, Z.n(to), h2lt)
  +l3 = N.le_lt_trans(k3, Z.n(to), Z.n(len), hk3, hlt)
  +l2 = N.lt_trans(k2, Z.n(to), Z.n(len), h2lt, hlt)
  +l1 = N.lt_trans(k1, k2, Z.n(len), PF.lt_add_succ(k1, 0n), l2)
  +p1 = pj(len, t, d, j, 1, k, k1, hok, hj, {==}, l1)
  +p2 = pj(len, t, d, j, 2, k, k2, hok, hj, Equal.sym(Nat, k2, Nat.add(k, 2n), e_k2(k)), l2)
  +p3 = pj(len, t, d, j, 3, k, k3, hok, hj, Equal.sym(Nat, k3, Nat.add(k, 3n), e_k3(k)), l3)
  +a1 = at_xv(len, t, d, (j + 1 : U32), k1, hok, p1, l1)
  +a2 = at_xv(len, t, d, (j + 2 : U32), k2, hok, p2, l2)
  +a3 = at_xv(len, t, d, (j + 3 : U32), k3, hok, p3, l3)
  +ea = Equal.trans(Bool, U32.is_eq(C.AT(len, t, (j + 1 : U32)), 78), U32.is_eq(E.XV(xs, k1), 78), True{}, Equal.cong(U32, Bool, z => U32.is_eq(z, 78), C.AT(len, t, (j + 1 : U32)), E.XV(xs, k1), a1), h1)
  +eb = Equal.trans(Bool, U32.is_eq(C.AT(len, t, (j + 2 : U32)), 68), U32.is_eq(E.XV(xs, k2), 68), True{}, Equal.cong(U32, Bool, z => U32.is_eq(z, 68), C.AT(len, t, (j + 2 : U32)), E.XV(xs, k2), a2), h2)
  +ec = Equal.trans(Bool, U32.is_eq((j + 3 : U32), to), Nat.is_eq(Z.n((j + 3 : U32)), Z.n(to)), Nat.is_eq(k3, Z.n(to)), U.is_eq_to_nat((j + 3 : U32), to),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, Z.n(to)), Z.n((j + 3 : U32)), k3, p3))
  +c0 = U32.is_eq((j + 3 : U32), to)
  +x0 = C.AT(len, t, (j + 3 : U32))
  +s1 = AB.subst(Bool, z => {KEYG(z, U32.is_eq(C.AT(len, t, (j + 2 : U32)), 68), c0, x0) == False{} : Bool}, U32.is_eq(C.AT(len, t, (j + 1 : U32)), 78), True{}, ea, hkey)
  +s2 = AB.subst(Bool, z => {KEYG(True{}, z, c0, x0) == False{} : Bool}, U32.is_eq(C.AT(len, t, (j + 2 : U32)), 68), True{}, eb, s1)
  +s3 = AB.subst(Bool, z => {KEYG(True{}, True{}, z, x0) == False{} : Bool}, c0, Nat.is_eq(k3, Z.n(to)), ec, s2)
  AB.subst(U32, z => {KEYG(True{}, True{}, Nat.is_eq(k3, Z.n(to)), z) == False{} : Bool}, x0, E.XV(xs, k3), a3, s3)

def st.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +j: U32, +k: Nat, +c: Bool, +hc: {Nat.is_eq(k, Z.n(from)) == c : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hj: {Z.n(j) == k : Nat}, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool},
  +hk: {Nat.is_lt(k, Z.n(len)) == True{} : Bool}, +hsb: {E.SB(Z.X(len, t), Z.n(from), k) == True{} : Bool}) ->
  {START(len, t, from, j) == True{} : Bool}:
  match c:
    case True{}:
      +ej = Equal.trans(Bool, U32.is_eq(j, from), Nat.is_eq(Z.n(j), Z.n(from)), True{}, U.is_eq_to_nat(j, from),
        Equal.trans(Bool, Nat.is_eq(Z.n(j), Z.n(from)), Nat.is_eq(k, Z.n(from)), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, Z.n(from)), Z.n(j), k, hj), hc))
      %Equal.sym(Bool, U32.is_eq(j, from), True{}, ej) : {Bool.or(_, U32.is_eq(C.AT(len, t, (j - 1 : U32)), 59)) == True{} : Bool}
      {==}
    case False{}:
      +xs = Z.X(len, t)
      +k0 = Nat.sub(k, 1n)
      +hhas = AB.subst(Bool, z => {Bool.or(z, D.has(xs, k0, 59)) == True{} : Bool}, Nat.is_eq(k, Z.n(from)), False{}, hc, hsb)
      +hne = Equal.trans(Bool, Nat.is_eq(Z.n(from), k), Nat.is_eq(k, Z.n(from)), False{}, N.eq_comm(Z.n(from), k), hc)
      +h1k = N.le_trans(1n, Nat.add(Z.n(from), 1n), k, N.le_add_l(1n, Z.n(from)), C.succ_le(Z.n(from), k, Z.le_ne_lt(Z.n(from), k, hfk, hne)))
      +h1j = Z.nle(1, j, AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, k, Z.n(j), Equal.sym(Nat, Z.n(j), k, hj), h1k))
      +pm = Equal.trans(Nat, Z.n((j - 1 : U32)), Nat.sub(Z.n(j), 1n), k0, U.to_nat_sub_le(j, 1, h1j), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Z.n(j), k, hj))
      +hk0 = N.le_lt_trans(k0, k, Z.n(len), PSh.sub_le(k, 1n), hk)
      +g = PF.step_get(len, t, d, (j - 1 : U32), hok, AB.subst(Nat, z => {Nat.is_lt(z, Z.n(len)) == True{} : Bool}, k0, Z.n((j - 1 : U32)), Equal.sym(Nat, Z.n((j - 1 : U32)), k0, pm), hk0))
      +g2 = AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{C.AT(len, t, (j - 1 : U32))} : Maybe<&2, U32>}, Z.n((j - 1 : U32)), k0, pm, g)
      +hp = AB.subst(Maybe<&2, U32>, m => {D.is_some(m, 59) == True{} : Bool}, List.get(&2, U32, xs, k0), Some{C.AT(len, t, (j - 1 : U32))}, g2, hhas)
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (j - 1 : U32)), 59), True{}, hp) : {Bool.or(U32.is_eq(j, from), _) == True{} : Bool}
      E.or_true_r(U32.is_eq(j, from))

def start_true(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +j: U32, +k: Nat,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hj: {Z.n(j) == k : Nat}, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool},
  +hk: {Nat.is_lt(k, Z.n(len)) == True{} : Bool}, +hsb: {E.SB(Z.X(len, t), Z.n(from), k) == True{} : Bool}) ->
  {START(len, t, from, j) == True{} : Bool}:
  st.k(len, t, d, from, j, k, Nat.is_eq(k, Z.n(from)), {==}, hok, hj, hfk, hk, hsb)

# ---------------------------------------------------------------------------
# The scan: J.noend.go at each position of INFO, against the bytes loop
# ---------------------------------------------------------------------------

def NEG(+len: U32, +t: AT.Tree<U32>, +b: Nat, +k: Nat, +st: Bool) -> Type:
  {J.noend.go(S.fld(Z.X(len, t), Nat.add(k, 1n), b), Chr{E.XV(Z.X(len, t), k)}, U32.is_eq(E.XV(Z.X(len, t), k), 9), st) == True{} : Bool}

def IHT(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +b: Nat, +k1: Nat) -> Type:
  @st: Bool -> @y: U32 -> @fuel: Nat -> {st == E.SB(Z.X(len, t), Z.n(from), k1) : Bool} -> {Nat.is_le(Z.n(y), k1) == True{} : Bool}
    -> {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k1, Z.n(to), 69) : Nat}
    -> {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool} -> {Nat.is_lt(k1, b) == True{} : Bool} -> NEG(len, t, b, k1, st)

def fin_nil(+x: U32, +st: Bool, +hik: {String.eq(J.ikeyT(SCon{Chr{x}, SNil{}}), "END") == False{} : Bool}) ->
  {J.noend.go(SNil{}, Chr{x}, False{}, st) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, String.eq(J.ikeyT(SCon{Chr{x}, SNil{}}), "END"), False{}, hik) : {Bool.not(_) == True{} : Bool}
      {==}
    case False{}:
      {==}

def fin_cons(+h: Char, +h2: Char, +t2: String, +st: Bool,
  hik: {st == True{} : Bool} -> {String.eq(J.ikeyT(SCon{h, SCon{h2, t2}}), "END") == False{} : Bool},
  +hrec: {J.noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';')) == True{} : Bool}) ->
  {J.noend.go(SCon{h2, t2}, h, False{}, st) == True{} : Bool}:
  match st:
    case True{}:
      %Equal.sym(Bool, String.eq(J.ikeyT(SCon{h, SCon{h2, t2}}), "END"), False{}, hik({==})) :
        {(Bool.not(_) && J.noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'))) == True{} : Bool}
      %Equal.sym(Bool, J.noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';')), True{}, hrec) : {(Bool.not(False{}) && _) == True{} : Bool}
      {==}
    case False{}:
      hrec

def lt_ne(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({False{} == False{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q:
      lt_ne(p, q, h)

def hnt_k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k3: Nat, +hfk3: {Nat.is_le(Z.n(from), k3) == True{} : Bool}, +h: {Nat.is_lt(k3, Z.n(to)) == True{} : Bool}) ->
  {U32.is_eq(E.XV(Z.X(len, t), k3), 9) == False{} : Bool}:
  +k3L = N.lt_trans(k3, Z.n(to), Z.n(len), h, hlt)
  AB.subst(Maybe<&2, U32>, m => {D.is_some(m, 9) == False{} : Bool}, List.get(&2, U32, Z.X(len, t), k3), Some{E.XV(Z.X(len, t), k3)},
    E.get_xv(Z.X(len, t), k3, lt_len(len, t, d, k3, hok, k3L)), Z.no9(Z.X(len, t), Z.n(from), Z.n(len), Z.n(to), k3, hff, hfk3, h))

def hx9_of(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}) ->
  {U32.is_eq(E.XV(Z.X(len, t), k), 9) == False{} : Bool}:
  hnt_k(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, hfk, hk)

def ne_hik(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hk1b: {Nat.is_lt(Nat.add(k, 1n), b) == True{} : Bool}, +j: U32, +hjk: {Z.n(j) == k : Nat}, +hx69: {E.XV(Z.X(len, t), k) == 69 : U32},
  +hee: {M.END(len, t, from, to, j) == False{} : Bool}, +hs: {st == True{} : Bool}) ->
  {String.eq(J.ikeyT(SCon{Chr{E.XV(Z.X(len, t), k)}, SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}}), "END") == False{} : Bool}:
  +kL = N.lt_trans(k, Z.n(to), Z.n(len), hk, hlt)
  +hgk = E.get_xv(Z.X(len, t), k, lt_len(len, t, d, k, hok, kL))
  +hsb1 = E.sb_next(Z.X(len, t), Z.n(from), k, hfk, hgk)
  +sbt = Equal.trans(Bool, E.SB(Z.X(len, t), Z.n(from), k), st, True{}, Equal.sym(Bool, st, E.SB(Z.X(len, t), Z.n(from), k), hst), hs)
  +hstart = start_true(len, t, d, from, j, k, hok, hjk, hfk, kL, sbt)
  +hkey = AB.subst(Bool, z => {Bool.and(z, KEY(len, t, to, j)) == False{} : Bool}, START(len, t, from, j), True{}, hstart,
    Equal.trans(Bool, Bool.and(START(len, t, from, j), KEY(len, t, to, j)), M.END(len, t, from, to, j), False{}, Equal.sym(Bool, M.END(len, t, from, to, j), Bool.and(START(len, t, from, j), KEY(len, t, to, j)), end_sk(len, t, from, to, j)), hee))
  +k3 = Nat.add(Nat.add(Nat.add(k, 1n), 1n), 1n)
  +hfk3 = N.le_trans(Z.n(from), k, k3, hfk, AB.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, Nat.add(k, 3n), k3, Equal.sym(Nat, k3, Nat.add(k, 3n), e_k3(k)), N.le_add_r(k, 3n)))
  +e0 = E.e_ne(Z.X(len, t), k, Z.n(to), b, hk, htb, hb, hend_of(Z.X(len, t), Z.n(to), b, hendc),
    h1 => h2 => h3 => key_kf(len, t, d, to, j, k, hok, hjk, h3, hlt, hkey, h1, h2),
    h => hnt_k(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k3, hfk3, h))
  +e1 = AB.subst(String, z => {String.eq(J.ikeyT(SCon{Chr{69}, z}), "END") == False{} : Bool}, S.fld(Z.X(len, t), Nat.add(k, 1n), b), SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, E.fld_cons(Z.X(len, t), Nat.add(k, 1n), b, hk1b, hb), e0)
  AB.subst(U32, z => {String.eq(J.ikeyT(SCon{Chr{z}, SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}}), "END") == False{} : Bool}, 69, E.XV(Z.X(len, t), k), Equal.sym(U32, E.XV(Z.X(len, t), k), 69, hx69), e1)

def ne_end(+endb: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hk1b: {Nat.is_lt(Nat.add(k, 1n), b) == True{} : Bool}, +f: Nat, +j: U32, +hjk: {Z.n(j) == k : Nat}, +hx69: {E.XV(Z.X(len, t), k) == 69 : U32},
  +hee: {M.END(len, t, from, to, j) == endb : Bool},
  +hng1: {M.NG2(f, len, t, from, to, (j + 1 : U32), Bool.not(endb), Bool.not(endb)) == True{} : Bool}, ih: IHT(len, t, from, to, b, Nat.add(k, 1n))) -> {J.noend.go(SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}:
  match endb:
    case True{}:
      Empty.absurd({J.noend.go(SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}, Z.ne_tf(M.NG2(f, len, t, from, to, (j + 1 : U32), False{}, False{}), hng1, ng_ff(f, len, t, from, to, (j + 1 : U32))))
    case False{}:
      +kL = N.lt_trans(k, Z.n(to), Z.n(len), hk, hlt)
      +hgk = E.get_xv(Z.X(len, t), k, lt_len(len, t, d, k, hok, kL))
      +hsb1 = E.sb_next(Z.X(len, t), Z.n(from), k, hfk, hgk)
      +k1L = N.le_lt_trans(Nat.add(k, 1n), Z.n(to), Z.n(len), C.succ_le(k, Z.n(to), hk), hlt)
      +pj1 = pj(len, t, d, j, 1, k, Nat.add(k, 1n), hok, hjk, {==}, k1L)
      +hy2 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(k, 1n)) == True{} : Bool}, Nat.add(k, 1n), Z.n((j + 1 : U32)), Equal.sym(Nat, Z.n((j + 1 : U32)), Nat.add(k, 1n), pj1), N.le_refl(Nat.add(k, 1n)))
      +hP2 = Equal.cong(Nat, Nat, z => D.first(Z.X(len, t), z, Z.n(to), 69), Z.n((j + 1 : U32)), Nat.add(k, 1n), pj1)
      fin_cons(Chr{E.XV(Z.X(len, t), k)}, Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b), st, hs => ne_hik(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, hk1b, j, hjk, hx69, hee, hs),
        ih(U32.is_eq(E.XV(Z.X(len, t), k), 59), (j + 1 : U32), f, hsb1, hy2, hP2, hng1, hk1b))

def ne_e69(+fuel: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hk1b: {Nat.is_lt(Nat.add(k, 1n), b) == True{} : Bool}, +hng: {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool},
  +hx69: {E.XV(Z.X(len, t), k) == 69 : U32}, ih: IHT(len, t, from, to, b, Nat.add(k, 1n))) -> {J.noend.go(SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}:
  match fuel:
    case 0n:
      Empty.absurd({J.noend.go(SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}, N.false_ne_true(hng))
    case 1n+f:
      +kL = N.lt_trans(k, Z.n(to), Z.n(len), hk, hlt)
      +hgk = E.get_xv(Z.X(len, t), k, lt_len(len, t, d, k, hok, kL))
      +hsb1 = E.sb_next(Z.X(len, t), Z.n(from), k, hfk, hgk)
      +j = M.F1(len, t, y, to, 69)
      +hyt = Z.nle(y, to, N.le_trans(Z.n(y), k, Z.n(to), hy, N.lt_to_le(k, Z.n(to), hk)))
      +hjv = M.f1_view(len, t, d, y, to, 69, hok, hyt, N.lt_to_le(Z.n(to), Z.n(len), hlt), {==})
      +hg69 = AB.subst(U32, z => {List.get(&2, U32, Z.X(len, t), k) == Some{z} : Maybe<&2, U32>}, E.XV(Z.X(len, t), k), 69, hx69, hgk)
      +hjk = Equal.trans(Nat, Z.n(j), D.first(Z.X(len, t), Z.n(y), Z.n(to), 69), k, hjv,
        Equal.trans(Nat, D.first(Z.X(len, t), Z.n(y), Z.n(to), 69), D.first(Z.X(len, t), k, Z.n(to), 69), k, hP, E.step_hit(Z.X(len, t), k, Z.n(to), hg69, hk)))
      +hnone = Equal.trans(Bool, U32.is_eq(j, to), Nat.is_eq(Z.n(j), Z.n(to)), False{}, U.is_eq_to_nat(j, to),
        Equal.trans(Bool, Nat.is_eq(Z.n(j), Z.n(to)), Nat.is_eq(k, Z.n(to)), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, Z.n(to)), Z.n(j), k, hjk), lt_ne(k, Z.n(to), hk)))
      +hng1 = AB.subst(Bool, z => {M.NG2(f, len, t, from, to, M.NEy(z, j), M.NEo(z, len, t, from, to, j), M.NEm(z, len, t, from, to, j)) == True{} : Bool},
        U32.is_eq(j, to), False{}, hnone, hng)
      ne_end(M.END(len, t, from, to, j), len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, hk1b, f, j, hjk, hx69, {==}, hng1, ih)

def ne_e(+e: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hk1b: {Nat.is_lt(Nat.add(k, 1n), b) == True{} : Bool}, +he: {U32.is_eq(E.XV(Z.X(len, t), k), 69) == e : Bool}, +fuel: Nat,
  +hng: {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool}, ih: IHT(len, t, from, to, b, Nat.add(k, 1n))) -> {J.noend.go(SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}:
  match e:
    case False{}:
      +kL = N.lt_trans(k, Z.n(to), Z.n(len), hk, hlt)
      +hgk = E.get_xv(Z.X(len, t), k, lt_len(len, t, d, k, hok, kL))
      +hsb1 = E.sb_next(Z.X(len, t), Z.n(from), k, hfk, hgk)
      +hP2 = Equal.trans(Nat, D.first(Z.X(len, t), Z.n(y), Z.n(to), 69), D.first(Z.X(len, t), k, Z.n(to), 69), D.first(Z.X(len, t), Nat.add(k, 1n), Z.n(to), 69), hP, E.step_miss(Z.X(len, t), k, Z.n(to), 69, E.XV(Z.X(len, t), k), hgk, he, hk))
      +hy2 = N.le_trans(Z.n(y), k, Nat.add(k, 1n), hy, N.le_add_r(k, 1n))
      fin_cons(Chr{E.XV(Z.X(len, t), k)}, Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b), st, hs => E.first_ne(E.XV(Z.X(len, t), k), SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, he),
        ih(U32.is_eq(E.XV(Z.X(len, t), k), 59), y, fuel, hsb1, hy2, hP2, hng, hk1b))
    case True{}:
      ne_e69(fuel, len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, hk1b, hng, U.is_eq_true(E.XV(Z.X(len, t), k), 69, he), ih)

def ne_cons(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hk1b: {Nat.is_lt(Nat.add(k, 1n), b) == True{} : Bool}, +fuel: Nat, +hng: {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool}, ih: IHT(len, t, from, to, b, Nat.add(k, 1n))) ->
  NEG(len, t, b, k, st):
  %Equal.sym(Bool, U32.is_eq(E.XV(Z.X(len, t), k), 9), False{}, hx9_of(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, hfk, hk)) : {J.noend.go(S.fld(Z.X(len, t), Nat.add(k, 1n), b), Chr{E.XV(Z.X(len, t), k)}, _, st) == True{} : Bool}
  %Equal.sym(String, S.fld(Z.X(len, t), Nat.add(k, 1n), b), SCon{Chr{E.XV(Z.X(len, t), Nat.add(k, 1n))}, S.fld(Z.X(len, t), Nat.add(Nat.add(k, 1n), 1n), b)}, E.fld_cons(Z.X(len, t), Nat.add(k, 1n), b, hk1b, hb)) : {J.noend.go(_, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}
  ne_e(U32.is_eq(E.XV(Z.X(len, t), k), 69), len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, hk1b, {==}, fuel, hng, ih)

def ne_c(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool}, +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat}, +hk: {Nat.is_lt(k, Z.n(to)) == True{} : Bool}, +hc: {Nat.is_lt(Nat.add(k, 1n), b) == c : Bool},
  +hkb: {Nat.is_lt(k, b) == True{} : Bool}, +fuel: Nat, +hng: {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool}, ih: IHT(len, t, from, to, b, Nat.add(k, 1n))) ->
  NEG(len, t, b, k, st):
  match c:
    case False{}:
      +e = E.le_eq(Nat.add(k, 1n), b, C.succ_le(k, b, hkb), hc)
      %Equal.sym(Bool, U32.is_eq(E.XV(Z.X(len, t), k), 9), False{}, hx9_of(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, hfk, hk)) : {J.noend.go(S.fld(Z.X(len, t), Nat.add(k, 1n), b), Chr{E.XV(Z.X(len, t), k)}, _, st) == True{} : Bool}
      %Equal.sym(String, S.fld(Z.X(len, t), Nat.add(k, 1n), b), SNil{}, AB.subst(Nat, z => {S.fld(Z.X(len, t), z, b) == SNil{} : String}, b, Nat.add(k, 1n), Equal.sym(Nat, Nat.add(k, 1n), b, e), E.fld_end(Z.X(len, t), b))) :
        {J.noend.go(_, Chr{E.XV(Z.X(len, t), k)}, False{}, st) == True{} : Bool}
      fin_nil(E.XV(Z.X(len, t), k), st, E.one_ne(E.XV(Z.X(len, t), k)))
    case True{}:
      ne_cons(len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, hc, fuel, hng, ih)

def ne_ind(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +k: Nat, +st: Bool, +y: U32, +fuel: Nat, +hm: {Nat.add(k, m) == Z.n(to) : Nat},
  +hkb: {Nat.is_lt(k, b) == True{} : Bool}, +hfk: {Nat.is_le(Z.n(from), k) == True{} : Bool}, +hst: {st == E.SB(Z.X(len, t), Z.n(from), k) : Bool},
  +hy: {Nat.is_le(Z.n(y), k) == True{} : Bool}, +hP: {D.first(Z.X(len, t), Z.n(y), Z.n(to), 69) == D.first(Z.X(len, t), k, Z.n(to), 69) : Nat},
  +hng: {M.NG2(fuel, len, t, from, to, y, True{}, True{}) == True{} : Bool}) -> NEG(len, t, b, k, st):
  match m:
    case 0n:
      +e = Equal.trans(Nat, k, Nat.add(k, 0n), Z.n(to), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k)), hm)
      +kL = AB.subst(Nat, z => {Nat.is_lt(z, Z.n(len)) == True{} : Bool}, Z.n(to), k, Equal.sym(Nat, k, Z.n(to), e), hlt)
      +g9 = hend_k(Z.X(len, t), Z.n(to), b, hendc, AB.subst(Nat, z => {Nat.is_lt(z, b) == True{} : Bool}, k, Z.n(to), e, hkb))
      +x9 = S.some_eq(E.XV(Z.X(len, t), k), 9, Equal.trans(Maybe<&2, U32>, Some{E.XV(Z.X(len, t), k)}, List.get(&2, U32, Z.X(len, t), k), Some{9},
        Equal.sym(Maybe<&2, U32>, List.get(&2, U32, Z.X(len, t), k), Some{E.XV(Z.X(len, t), k)}, E.get_xv(Z.X(len, t), k, lt_len(len, t, d, k, hok, kL))),
        AB.subst(Nat, z => {List.get(&2, U32, Z.X(len, t), z) == Some{9} : Maybe<&2, U32>}, Z.n(to), k, Equal.sym(Nat, k, Z.n(to), e), g9)))
      %Equal.sym(Bool, U32.is_eq(E.XV(Z.X(len, t), k), 9), U32.is_eq(9, 9), Equal.cong(U32, Bool, z => U32.is_eq(z, 9), E.XV(Z.X(len, t), k), 9, x9)) :
        {J.noend.go(S.fld(Z.X(len, t), Nat.add(k, 1n), b), Chr{E.XV(Z.X(len, t), k)}, _, st) == True{} : Bool}
      E.tab_true(S.fld(Z.X(len, t), Nat.add(k, 1n), b), Chr{E.XV(Z.X(len, t), k)}, st)
    case 1n+m2:
      +hk = AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, Nat.add(k, 1n+m2), Z.n(to), hm, PF.lt_add_succ(k, m2))
      +hm2 = Equal.trans(Nat, Nat.add(Nat.add(k, 1n), m2), Nat.add(k, Nat.add(1n, m2)), Z.n(to), N.add_assoc(k, 1n, m2), hm)
      +hfk2 = N.le_trans(Z.n(from), k, Nat.add(k, 1n), hfk, N.le_add_r(k, 1n))
      ne_c(Nat.is_lt(Nat.add(k, 1n), b), len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, k, st, y, hfk, hst, hy, hP, hk, {==}, hkb, fuel, hng,
        +st2 => +y2 => +f2 => +h1 => +h2 => +h3 => +h4 => +h5 => ne_ind(m2, len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, Nat.add(k, 1n), st2, y2, f2, hm2, h5, hfk2, h1, h2, h3, h4))

def no_k(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +hc: {Nat.is_lt(Z.n(from), b) == c : Bool}, +hft: {Nat.is_le(Z.n(from), Z.n(to)) == True{} : Bool},
  +hne: {M.NE(len, t, from, to) == True{} : Bool}) -> {J.noend(S.fld(Z.X(len, t), Z.n(from), b)) == True{} : Bool}:
  match c:
    case False{}:
      +e = E.le_eq(Z.n(from), b, N.le_trans(Z.n(from), Z.n(to), b, hft, htb), hc)
      %Equal.sym(String, S.fld(Z.X(len, t), Z.n(from), b), SNil{}, AB.subst(Nat, z => {S.fld(Z.X(len, t), z, b) == SNil{} : String}, b, Z.n(from), Equal.sym(Nat, Z.n(from), b, e), E.fld_end(Z.X(len, t), b))) :
        {J.noend(_) == True{} : Bool}
      {==}
    case True{}:
      +hsb = AB.subst(Bool, z => {Bool.or(z, D.has(Z.X(len, t), Nat.sub(Z.n(from), 1n), 59)) == True{} : Bool}, True{}, Nat.is_eq(Z.n(from), Z.n(from)), Equal.sym(Bool, Nat.is_eq(Z.n(from), Z.n(from)), True{}, N.eq_refl(Z.n(from))), {==})
      %Equal.sym(String, S.fld(Z.X(len, t), Z.n(from), b), SCon{Chr{E.XV(Z.X(len, t), Z.n(from))}, S.fld(Z.X(len, t), Nat.add(Z.n(from), 1n), b)}, E.fld_cons(Z.X(len, t), Z.n(from), b, hc, hb)) :
        {J.noend(_) == True{} : Bool}
      ne_ind(Nat.sub(Z.n(to), Z.n(from)), len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, Z.n(from), True{}, from, U32.to_nat((to - from + 2 : U32)), N.le_sub_add(Z.n(from), Z.n(to), hft), hc, N.le_refl(Z.n(from)),
        Equal.sym(Bool, E.SB(Z.X(len, t), Z.n(from), Z.n(from)), True{}, hsb), N.le_refl(Z.n(from)), {==}, hne)

# INFO from .. to-1, followed by a tab or the end of the text (b): J.noend
# passes on the text from INFO's start when the bytes loop passed.
def noend_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +b: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hff: {D.first2(Z.X(len, t), Z.n(from), Z.n(len), 9, 10) == Z.n(to) : Nat}, +hlt: {Nat.is_lt(Z.n(to), Z.n(len)) == True{} : Bool}, +htb: {Nat.is_le(Z.n(to), b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, Z.X(len, t))) == True{} : Bool}, +hendc: {(Bool.not(Nat.is_lt(Z.n(to), b)) || D.has(Z.X(len, t), Z.n(to), 9)) == True{} : Bool}, +hft: {Nat.is_le(Z.n(from), Z.n(to)) == True{} : Bool}, +hne: {M.NE(len, t, from, to) == True{} : Bool}) ->
  {J.noend(S.fld(Z.X(len, t), Z.n(from), b)) == True{} : Bool}:
  no_k(Nat.is_lt(Z.n(from), b), len, t, d, from, to, b, hok, hff, hlt, htb, hb, hendc, {==}, hft, hne)
