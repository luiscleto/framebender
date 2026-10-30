import Base
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./proof_b_cut_str.bend as S
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_append.bend as PA
import lawful-bytes@0.1.0.0/proof_shift.bend as PSh
import lawful-bytes@0.1.0.0/proof_seq.bend as PSq
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-bytes@0.1.0.0/proof_core.bend as C

# INFO's END test in place (J.noend) on the text of bytes, list level.

# Byte p (0 past the end).
def XV(+xs: List<&2, U32>, +p: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, p), 0)

def get_xv(+xs: List<&2, U32>, +p: Nat, +h: {Nat.is_lt(p, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.get(&2, U32, xs, p) == Some{XV(xs, p)} : Maybe<&2, U32>}:
  match xs p:
    case Nil{} _:
      Empty.absurd({List.get(&2, U32, Nil{}, p) == Some{XV(Nil{}, p)} : Maybe<&2, U32>},
        N.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(p, 0n), False{}, Equal.sym(Bool, Nat.is_lt(p, 0n), True{}, h), N.lt_zero(p))))
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+q:
      get_xv(t, q, h)

def ord_ne(+a: String, +b: String, +c: Cmp, +hc: {Cmp.is_eq(c) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(a, b, c)) == False{} : Bool}:
  match a b c:
    case SNil{} SNil{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(hc))
    case SNil{} SNil{} LT{}:
      {==}
    case SNil{} SNil{} GT{}:
      {==}
    case SNil{} SCon{h, t} EQ{}:
      Empty.absurd({False{} == False{} : Bool}, N.true_ne_false(hc))
    case SNil{} SCon{h, t} LT{}:
      {==}
    case SNil{} SCon{h, t} GT{}:
      {==}
    case SCon{h, t} SNil{} EQ{}:
      Empty.absurd({False{} == False{} : Bool}, N.true_ne_false(hc))
    case SCon{h, t} SNil{} LT{}:
      {==}
    case SCon{h, t} SNil{} GT{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} EQ{}:
      Empty.absurd({Cmp.is_eq(String.order.go(t1, t2, U32.cmp(x, y))) == False{} : Bool}, N.true_ne_false(hc))
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} LT{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} GT{}:
      {==}

def ord_nil(+c: Cmp, +t: String) -> {Cmp.is_eq(String.order.go(SNil{}, SCon{Chr{78}, t}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ik_ne(+x: U32, +t: String, +ok: Bool, +hx: {U32.is_eq(x, 69) == False{} : Bool}) ->
  {String.eq(J.ikeyT.go(SCon{Chr{x}, t}, ok), "END") == False{} : Bool}:
  match ok:
    case True{}:
      ord_ne(J.ikeyT.go(t, J.ikeyT.ok(t)), "ND", U32.cmp(x, 69), hx)
    case False{}:
      {==}

# An entry that does not start with E is not an END entry.
def first_ne(+x: U32, +t: String, +hx: {U32.is_eq(x, 69) == False{} : Bool}) ->
  {String.eq(J.ikeyT(SCon{Chr{x}, t}), "END") == False{} : Bool}:
  ik_ne(x, t, J.ikeyT.ok(SCon{Chr{x}, t}), hx)

def ik_one(+x: U32, +ok: Bool) -> {String.eq(J.ikeyT.go(SCon{Chr{x}, SNil{}}, ok), "END") == False{} : Bool}:
  match ok:
    case True{}:
      ord_nil(U32.cmp(x, 69), "D")
    case False{}:
      {==}

# Nor is a one-character entry.
def one_ne(+x: U32) -> {String.eq(J.ikeyT(SCon{Chr{x}, SNil{}}), "END") == False{} : Bool}:
  ik_one(x, J.ikeyT.ok(SCon{Chr{x}, SNil{}}))

def tab_true(+t: String, +h: Char, +st: Bool) -> {J.noend.go(t, h, True{}, st) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{h2, t2}:
      {==}

# ---------------------------------------------------------------------------
# The text of p .. B-1, one character at a time
# ---------------------------------------------------------------------------

def subsucc(+p: Nat, +b: Nat, +h: {Nat.is_lt(p, b) == True{} : Bool}) -> {Nat.sub(b, p) == 1n+Nat.sub(b, Nat.add(p, 1n)) : Nat}:
  match p b:
    case 0n 0n:
      Empty.absurd({0n == 1n+Nat.sub(0n, 1n) : Nat}, N.false_ne_true(h))
    case 0n 1n+q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, N.sub_zero(q)) : {1n+q == 1n+_ : Nat}
      {==}
    case 1n+r 0n:
      Empty.absurd({0n == 1n+Nat.sub(0n, Nat.add(1n+r, 1n)) : Nat}, N.false_ne_true(h))
    case 1n+r 1n+q:
      subsucc(r, q, h)

def fld_cons(+xs: List<&2, U32>, +p: Nat, +b: Nat, +hp: {Nat.is_lt(p, b) == True{} : Bool},
  +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {S.fld(xs, p, b) == SCon{Chr{XV(xs, p)}, S.fld(xs, Nat.add(p, 1n), b)} : String}:
  +m = Nat.sub(b, Nat.add(p, 1n))
  %Equal.sym(Nat, Nat.sub(b, p), 1n+m, subsucc(p, b, hp)) : {Norm.chars(D.slice(xs, p, _)) == SCon{Chr{XV(xs, p)}, S.fld(xs, Nat.add(p, 1n), b)} : String}
  %Equal.sym(List<&2, U32>, D.slice(xs, p, 1n+m), XV(xs, p) <> D.slice(xs, Nat.add(p, 1n), m),
    PA.slice_cons(xs, p, m, XV(xs, p), get_xv(xs, p, N.lt_le_trans(p, b, List.length(&2, U32, xs), hp, hb)))) :
    {Norm.chars(_) == SCon{Chr{XV(xs, p)}, S.fld(xs, Nat.add(p, 1n), b)} : String}
  {==}

def fld_end(+xs: List<&2, U32>, +b: Nat) -> {S.fld(xs, b, b) == SNil{} : String}:
  %Equal.sym(Nat, Nat.sub(b, b), 0n, PSh.sub_self(b)) : {Norm.chars(D.slice(xs, b, _)) == SNil{} : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, xs, b), 0n), Nil{}, PSq.take_zero(List.drop(&2, U32, xs, b))) : {Norm.chars(_) == SNil{} : String}
  {==}

def le_eq(+a: Nat, +b: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_lt(a, b) == False{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, N.true_ne_false(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(h1))
    case 1n+p 1n+q:
      %le_eq(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

def IK(+xs: List<&2, U32>, +p: Nat, +b: Nat) -> String:
  J.ikeyT.go(S.fld(xs, p, b), J.ikeyT.ok(S.fld(xs, p, b)))

def stop.k(+xs: List<&2, U32>, +to: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(to, b) == c : Bool},
  +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>}) ->
  {IK(xs, to, b) == SNil{} : String}:
  match c:
    case True{}:
      +x9 = S.some_eq(XV(xs, to), 9, Equal.trans(Maybe<&2, U32>, Some{XV(xs, to)}, List.get(&2, U32, xs, to), Some{9},
        Equal.sym(Maybe<&2, U32>, List.get(&2, U32, xs, to), Some{XV(xs, to)}, get_xv(xs, to, N.lt_le_trans(to, b, List.length(&2, U32, xs), hc, hb))), hend(hc)))
      %Equal.sym(String, S.fld(xs, to, b), SCon{Chr{XV(xs, to)}, S.fld(xs, Nat.add(to, 1n), b)}, fld_cons(xs, to, b, hc, hb)) :
        {J.ikeyT.go(_, J.ikeyT.ok(_)) == SNil{} : String}
      %Equal.sym(U32, XV(xs, to), 9, x9) : {J.ikeyT.go(SCon{Chr{_}, S.fld(xs, Nat.add(to, 1n), b)}, J.ikeyT.ok(SCon{Chr{_}, S.fld(xs, Nat.add(to, 1n), b)})) == SNil{} : String}
      {==}
    case False{}:
      %le_eq(to, b, htb, hc) : {J.ikeyT.go(S.fld(xs, to, _), J.ikeyT.ok(S.fld(xs, to, _))) == SNil{} : String}
      %Equal.sym(String, S.fld(xs, to, to), SNil{}, fld_end(xs, to)) : {J.ikeyT.go(_, J.ikeyT.ok(_)) == SNil{} : String}
      {==}

# INFO's key stops at its end: the tab after it, or the end of the text.
def stop(+xs: List<&2, U32>, +to: Nat, +b: Nat, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>}) ->
  {IK(xs, to, b) == SNil{} : String}:
  stop.k(xs, to, b, Nat.is_lt(to, b), {==}, htb, hb, hend)

# ---------------------------------------------------------------------------
# An E that does not start an END entry (bytes: key false) does not in the
# text either: "E" then the key's next characters
# ---------------------------------------------------------------------------

def KF(+xs: List<&2, U32>, +k3: Nat, +to: Nat) -> Type:
  {(Nat.is_eq(k3, to) || U32.is_eq(XV(xs, k3), 61) || U32.is_eq(XV(xs, k3), 59)) == False{} : Bool}

def or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def e3.m(+x3: U32, +r4: String, +a: Bool, +bb: Bool, +cc: Bool, +k3: Nat, +to: Nat,
  +ha: {U32.is_eq(x3, 59) == a : Bool}, +hbb: {U32.is_eq(x3, 61) == bb : Bool}, +hcc: {U32.is_eq(x3, 9) == cc : Bool},
  +hkf: {(Nat.is_eq(k3, to) || U32.is_eq(x3, 61) || U32.is_eq(x3, 59)) == False{} : Bool},
  +hnt: {U32.is_eq(x3, 9) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{x3}, r4}, J.ikeyT.ok3(a, bb, cc)), SNil{}, EQ{})) == False{} : Bool}:
  match a bb cc:
    case False{} False{} False{}:
      {==}
    case True{} _ _:
      +h = AB.subst(Bool, z => {(Nat.is_eq(k3, to) || U32.is_eq(x3, 61) || z) == False{} : Bool}, U32.is_eq(x3, 59), True{}, ha, hkf)
      Empty.absurd({Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{x3}, r4}, J.ikeyT.ok3(True{}, bb, cc)), SNil{}, EQ{})) == False{} : Bool},
        N.true_ne_false(Equal.trans(Bool, True{}, Bool.or(Nat.is_eq(k3, to) || U32.is_eq(x3, 61), True{}), False{},
          Equal.sym(Bool, Bool.or(Nat.is_eq(k3, to) || U32.is_eq(x3, 61), True{}), True{}, or_true_r(Nat.is_eq(k3, to) || U32.is_eq(x3, 61))), h)))
    case False{} True{} _:
      +h = AB.subst(Bool, z => {(Nat.is_eq(k3, to) || z || U32.is_eq(x3, 59)) == False{} : Bool}, U32.is_eq(x3, 61), True{}, hbb, hkf)
      +h2 = AB.subst(Bool, z => {Bool.or(z, U32.is_eq(x3, 59)) == False{} : Bool}, Bool.or(Nat.is_eq(k3, to), True{}), True{}, or_true_r(Nat.is_eq(k3, to)), h)
      Empty.absurd({Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{x3}, r4}, J.ikeyT.ok3(False{}, True{}, cc)), SNil{}, EQ{})) == False{} : Bool}, N.true_ne_false(h2))
    case False{} False{} True{}:
      Empty.absurd({Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{x3}, r4}, J.ikeyT.ok3(False{}, False{}, True{})), SNil{}, EQ{})) == False{} : Bool},
        N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(x3, 9), False{}, Equal.sym(Bool, U32.is_eq(x3, 9), True{}, hcc), hnt)))

def e3.k(+xs: List<&2, U32>, +k3: Nat, +to: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(k3, to) == c : Bool},
  +h3: {Nat.is_le(k3, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>},
  hkf: KF(xs, k3, to),
  hnt: {Nat.is_lt(k3, to) == True{} : Bool} -> {U32.is_eq(XV(xs, k3), 9) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(IK(xs, k3, b), SNil{}, EQ{})) == False{} : Bool}:
  match c:
    case False{}:
      +e = le_eq(k3, to, h3, hc)
      +hq = AB.subst(Nat, z => {Nat.is_eq(k3, z) == True{} : Bool}, k3, to, e, N.eq_refl(k3))
      +h = AB.subst(Bool, z => {(z || U32.is_eq(XV(xs, k3), 61) || U32.is_eq(XV(xs, k3), 59)) == False{} : Bool}, Nat.is_eq(k3, to), True{}, hq, hkf)
      Empty.absurd({Cmp.is_eq(String.order.go(IK(xs, k3, b), SNil{}, EQ{})) == False{} : Bool}, N.true_ne_false(h))
    case True{}:
      +x3 = XV(xs, k3)
      +r4 = S.fld(xs, Nat.add(k3, 1n), b)
      %Equal.sym(String, S.fld(xs, k3, b), SCon{Chr{x3}, r4}, fld_cons(xs, k3, b, N.lt_le_trans(k3, to, b, hc, htb), hb)) :
        {Cmp.is_eq(String.order.go(J.ikeyT.go(_, J.ikeyT.ok(_)), SNil{}, EQ{})) == False{} : Bool}
      e3.m(x3, r4, U32.is_eq(x3, 59), U32.is_eq(x3, 61), U32.is_eq(x3, 9), k3, to, {==}, {==}, {==}, hkf, hnt(hc))

def e2.c(+xs: List<&2, U32>, +k2: Nat, +to: Nat, +b: Nat, +d: Bool, +hd: {U32.is_eq(XV(xs, k2), 68) == d : Bool},
  +hlt: {Nat.is_lt(k2, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>},
  hk2: {U32.is_eq(XV(xs, k2), 68) == True{} : Bool} -> {Nat.is_lt(k2, to) == True{} : Bool} -> KF(xs, Nat.add(k2, 1n), to),
  hnt: {Nat.is_lt(Nat.add(k2, 1n), to) == True{} : Bool} -> {U32.is_eq(XV(xs, Nat.add(k2, 1n)), 9) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(IK(xs, Nat.add(k2, 1n), b), SNil{}, U32.cmp(XV(xs, k2), 68))) == False{} : Bool}:
  match d:
    case False{}:
      ord_ne(IK(xs, Nat.add(k2, 1n), b), SNil{}, U32.cmp(XV(xs, k2), 68), hd)
    case True{}:
      +k3 = Nat.add(k2, 1n)
      %Equal.sym(U32, XV(xs, k2), 68, U.is_eq_true(XV(xs, k2), 68, hd)) : {Cmp.is_eq(String.order.go(IK(xs, k3, b), SNil{}, U32.cmp(_, 68))) == False{} : Bool}
      e3.k(xs, k3, to, b, Nat.is_lt(k3, to), {==}, C.succ_le(k2, to, hlt), htb, hb, hend, hk2(hd, hlt), hnt)

def e2.m(+xs: List<&2, U32>, +k2: Nat, +to: Nat, +b: Nat, +ok: Bool,
  +hlt: {Nat.is_lt(k2, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>},
  hk2: {U32.is_eq(XV(xs, k2), 68) == True{} : Bool} -> {Nat.is_lt(k2, to) == True{} : Bool} -> KF(xs, Nat.add(k2, 1n), to),
  hnt: {Nat.is_lt(Nat.add(k2, 1n), to) == True{} : Bool} -> {U32.is_eq(XV(xs, Nat.add(k2, 1n)), 9) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{XV(xs, k2)}, S.fld(xs, Nat.add(k2, 1n), b)}, ok), "D", EQ{})) == False{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      e2.c(xs, k2, to, b, U32.is_eq(XV(xs, k2), 68), {==}, hlt, htb, hb, hend, hk2, hnt)

def e2.k(+xs: List<&2, U32>, +k2: Nat, +to: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(k2, to) == c : Bool},
  +h2: {Nat.is_le(k2, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>},
  hk2: {U32.is_eq(XV(xs, k2), 68) == True{} : Bool} -> {Nat.is_lt(k2, to) == True{} : Bool} -> KF(xs, Nat.add(k2, 1n), to),
  hnt: {Nat.is_lt(Nat.add(k2, 1n), to) == True{} : Bool} -> {U32.is_eq(XV(xs, Nat.add(k2, 1n)), 9) == False{} : Bool}) ->
  {Cmp.is_eq(String.order.go(IK(xs, k2, b), "D", EQ{})) == False{} : Bool}:
  match c:
    case False{}:
      +e = le_eq(k2, to, h2, hc)
      %Equal.sym(String, IK(xs, k2, b), SNil{}, AB.subst(Nat, z => {IK(xs, z, b) == SNil{} : String}, to, k2, Equal.sym(Nat, k2, to, e), stop(xs, to, b, htb, hb, hend))) :
        {Cmp.is_eq(String.order.go(_, "D", EQ{})) == False{} : Bool}
      {==}
    case True{}:
      %Equal.sym(String, S.fld(xs, k2, b), SCon{Chr{XV(xs, k2)}, S.fld(xs, Nat.add(k2, 1n), b)}, fld_cons(xs, k2, b, N.lt_le_trans(k2, to, b, hc, htb), hb)) :
        {Cmp.is_eq(String.order.go(J.ikeyT.go(_, J.ikeyT.ok(_)), "D", EQ{})) == False{} : Bool}
      e2.m(xs, k2, to, b, J.ikeyT.ok(SCon{Chr{XV(xs, k2)}, S.fld(xs, Nat.add(k2, 1n), b)}), hc, htb, hb, hend, hk2, hnt)

def HK1(+xs: List<&2, U32>, +k1: Nat, +to: Nat) -> Type:
  {U32.is_eq(XV(xs, k1), 78) == True{} : Bool} -> {U32.is_eq(XV(xs, Nat.add(k1, 1n)), 68) == True{} : Bool} -> {Nat.is_lt(Nat.add(k1, 1n), to) == True{} : Bool} -> KF(xs, Nat.add(Nat.add(k1, 1n), 1n), to)

def HNT(+xs: List<&2, U32>, +k3: Nat, +to: Nat) -> Type:
  {Nat.is_lt(k3, to) == True{} : Bool} -> {U32.is_eq(XV(xs, k3), 9) == False{} : Bool}

def HEND(+xs: List<&2, U32>, +to: Nat, +b: Nat) -> Type:
  {Nat.is_lt(to, b) == True{} : Bool} -> {List.get(&2, U32, xs, to) == Some{9} : Maybe<&2, U32>}

def e1.c(+xs: List<&2, U32>, +k1: Nat, +to: Nat, +b: Nat, +d: Bool, +hd: {U32.is_eq(XV(xs, k1), 78) == d : Bool},
  +hlt: {Nat.is_lt(k1, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: HEND(xs, to, b), hk1: HK1(xs, k1, to), hnt: HNT(xs, Nat.add(Nat.add(k1, 1n), 1n), to)) ->
  {Cmp.is_eq(String.order.go(IK(xs, Nat.add(k1, 1n), b), "D", U32.cmp(XV(xs, k1), 78))) == False{} : Bool}:
  match d:
    case False{}:
      ord_ne(IK(xs, Nat.add(k1, 1n), b), "D", U32.cmp(XV(xs, k1), 78), hd)
    case True{}:
      +k2 = Nat.add(k1, 1n)
      %Equal.sym(U32, XV(xs, k1), 78, U.is_eq_true(XV(xs, k1), 78, hd)) : {Cmp.is_eq(String.order.go(IK(xs, k2, b), "D", U32.cmp(_, 78))) == False{} : Bool}
      e2.k(xs, k2, to, b, Nat.is_lt(k2, to), {==}, C.succ_le(k1, to, hlt), htb, hb, hend, hk1(hd), hnt)

def e1.m(+xs: List<&2, U32>, +k1: Nat, +to: Nat, +b: Nat, +ok: Bool,
  +hlt: {Nat.is_lt(k1, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: HEND(xs, to, b), hk1: HK1(xs, k1, to), hnt: HNT(xs, Nat.add(Nat.add(k1, 1n), 1n), to)) ->
  {Cmp.is_eq(String.order.go(J.ikeyT.go(SCon{Chr{XV(xs, k1)}, S.fld(xs, Nat.add(k1, 1n), b)}, ok), "ND", EQ{})) == False{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      e1.c(xs, k1, to, b, U32.is_eq(XV(xs, k1), 78), {==}, hlt, htb, hb, hend, hk1, hnt)

def e1.k(+xs: List<&2, U32>, +k1: Nat, +to: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(k1, to) == c : Bool},
  +h1: {Nat.is_le(k1, to) == True{} : Bool}, +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: HEND(xs, to, b), hk1: HK1(xs, k1, to), hnt: HNT(xs, Nat.add(Nat.add(k1, 1n), 1n), to)) ->
  {Cmp.is_eq(String.order.go(IK(xs, k1, b), "ND", EQ{})) == False{} : Bool}:
  match c:
    case False{}:
      +e = le_eq(k1, to, h1, hc)
      %Equal.sym(String, IK(xs, k1, b), SNil{}, AB.subst(Nat, z => {IK(xs, z, b) == SNil{} : String}, to, k1, Equal.sym(Nat, k1, to, e), stop(xs, to, b, htb, hb, hend))) :
        {Cmp.is_eq(String.order.go(_, "ND", EQ{})) == False{} : Bool}
      {==}
    case True{}:
      %Equal.sym(String, S.fld(xs, k1, b), SCon{Chr{XV(xs, k1)}, S.fld(xs, Nat.add(k1, 1n), b)}, fld_cons(xs, k1, b, N.lt_le_trans(k1, to, b, hc, htb), hb)) :
        {Cmp.is_eq(String.order.go(J.ikeyT.go(_, J.ikeyT.ok(_)), "ND", EQ{})) == False{} : Bool}
      e1.m(xs, k1, to, b, J.ikeyT.ok(SCon{Chr{XV(xs, k1)}, S.fld(xs, Nat.add(k1, 1n), b)}), hc, htb, hb, hend, hk1, hnt)

# The E at k (inside INFO, k < to) starts no END entry when the key test on
# its bytes failed.
def e_ne(+xs: List<&2, U32>, +k: Nat, +to: Nat, +b: Nat, +hk: {Nat.is_lt(k, to) == True{} : Bool},
  +htb: {Nat.is_le(to, b) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  hend: HEND(xs, to, b), hk1: HK1(xs, Nat.add(k, 1n), to), hnt: HNT(xs, Nat.add(Nat.add(Nat.add(k, 1n), 1n), 1n), to)) ->
  {String.eq(J.ikeyT(SCon{Chr{69}, S.fld(xs, Nat.add(k, 1n), b)}), "END") == False{} : Bool}:
  +k1 = Nat.add(k, 1n)
  e1.k(xs, k1, to, b, Nat.is_lt(k1, to), {==}, C.succ_le(k, to, hk), htb, hb, hend, hk1, hnt)

# ---------------------------------------------------------------------------
# The first c from k: one step
# ---------------------------------------------------------------------------

def step_miss(+xs: List<&2, U32>, +k: Nat, +to: Nat, +c: U32, +x: U32, +hx: {List.get(&2, U32, xs, k) == Some{x} : Maybe<&2, U32>},
  +hxc: {U32.is_eq(x, c) == False{} : Bool}, +hk: {Nat.is_lt(k, to) == True{} : Bool}) ->
  {D.first(xs, k, to, c) == D.first(xs, Nat.add(k, 1n), to, c) : Nat}:
  +m = Nat.sub(to, Nat.add(k, 1n))
  +R = D.run_len(D.slice(xs, Nat.add(k, 1n), m), c)
  %Equal.sym(Nat, Nat.sub(to, k), 1n+m, subsucc(k, to, hk)) : {Nat.add(k, D.run_len(D.slice(xs, k, _), c)) == Nat.add(Nat.add(k, 1n), R) : Nat}
  %Equal.sym(List<&2, U32>, D.slice(xs, k, 1n+m), x <> D.slice(xs, Nat.add(k, 1n), m), PA.slice_cons(xs, k, m, x, hx)) :
    {Nat.add(k, D.run_len(_, c)) == Nat.add(Nat.add(k, 1n), R) : Nat}
  %Equal.sym(Bool, U32.is_eq(x, c), False{}, hxc) : {Nat.add(k, Bool.pick(Nat, _, 0n, Nat.add(1n, R))) == Nat.add(Nat.add(k, 1n), R) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(k, 1n), R), Nat.add(k, Nat.add(1n, R)), N.add_assoc(k, 1n, R))

def step_hit(+xs: List<&2, U32>, +k: Nat, +to: Nat, +hx: {List.get(&2, U32, xs, k) == Some{69} : Maybe<&2, U32>},
  +hk: {Nat.is_lt(k, to) == True{} : Bool}) -> {D.first(xs, k, to, 69) == k : Nat}:
  +m = Nat.sub(to, Nat.add(k, 1n))
  %Equal.sym(Nat, Nat.sub(to, k), 1n+m, subsucc(k, to, hk)) : {Nat.add(k, D.run_len(D.slice(xs, k, _), 69)) == k : Nat}
  %Equal.sym(List<&2, U32>, D.slice(xs, k, 1n+m), 69 <> D.slice(xs, Nat.add(k, 1n), m), PA.slice_cons(xs, k, m, 69, hx)) :
    {Nat.add(k, D.run_len(_, 69)) == k : Nat}
  N.add_zero(k)

# k starts an entry: it is INFO's first byte or follows a ';'.
def SB(+xs: List<&2, U32>, +f: Nat, +k: Nat) -> Bool:
  Nat.is_eq(k, f) || D.has(xs, Nat.sub(k, 1n), 59)

def eq_succ_f(+f: Nat, +k: Nat, +h: {Nat.is_le(f, k) == True{} : Bool}) -> {Nat.is_eq(Nat.add(k, 1n), f) == False{} : Bool}:
  match f k:
    case 0n _:
      %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, N.add_one(k)) : {Nat.is_eq(_, 0n) == False{} : Bool}
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_eq(Nat.add(0n, 1n), 1n+p) == False{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q:
      eq_succ_f(p, q, h)

def sb_next(+xs: List<&2, U32>, +f: Nat, +k: Nat, +hfk: {Nat.is_le(f, k) == True{} : Bool},
  +hg: {List.get(&2, U32, xs, k) == Some{XV(xs, k)} : Maybe<&2, U32>}) -> {U32.is_eq(XV(xs, k), 59) == SB(xs, f, Nat.add(k, 1n)) : Bool}:
  %Equal.sym(Bool, Nat.is_eq(Nat.add(k, 1n), f), False{}, eq_succ_f(f, k, hfk)) : {U32.is_eq(XV(xs, k), 59) == Bool.or(_, D.has(xs, Nat.sub(Nat.add(k, 1n), 1n), 59)) : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(k, 1n), 1n), k, N.sub_add(k, 1n)) : {U32.is_eq(XV(xs, k), 59) == D.has(xs, _, 59) : Bool}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, xs, k), Some{XV(xs, k)}, hg) : {U32.is_eq(XV(xs, k), 59) == D.is_some(_, 59) : Bool}
  {==}
