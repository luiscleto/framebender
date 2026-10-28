import Base
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_list.bend as BL
import ../lawful-words/proof_u32.bend as U

# What the alleles' list test (LP.spec) says: every ALT allele is non-empty
# and all bases; REF and the ALT alleles are distinct; the alleles do not all
# end with the same base, and do not all start with the same base while all
# are long. Every variable is reusable.

def LL() -> Data:
  List<&2, List<&2, U32>>

# Every allele is all bases and not empty.
def allok(ps: LL()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.and(Bool.and(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q))), allok(t))

# No allele is equal to a later one.
def dist(ps: LL()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(Bool.not(LP.memb(x, t)), dist(t))

# No allele of E is one of ps.
def notin(E: LL(), +ps: LL()) -> Bool:
  match E:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(Bool.not(LP.memb(e, ps)), notin(t, ps))

# Every allele ends with z3 / starts with f3 / has two or more bytes.
def lasts(+z3: U32, ps: LL()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.and(U32.is_eq(LP.lastb(q, 0), z3), lasts(z3, t))

def firsts(+f3: U32, ps: LL()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.and(U32.is_eq(LP.headb(q, 0), f3), firsts(f3, t))

def longs(ps: LL()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+q, t}:
      Bool.and(Nat.is_le(2n, List.length(&2, U32, q)), longs(t))

# Bool
# ====

law or_f_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_f_l(a, b, e):
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, LS.ft(Equal.sym(Bool, True{}, False{}, e)))

law or_f_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_f_r(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, LS.ft(Equal.sym(Bool, True{}, False{}, e)))

law not_f:
  for +a: Bool
  for +e: {a == False{} : Bool}
  {Bool.not(a) == True{} : Bool}

def not_f(a, e):
  %Equal.sym(Bool, a, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

law and_tt:
  for +a: Bool
  for +b: Bool
  for +ea: {a == True{} : Bool}
  for +eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_tt(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# Every allele passes
# ===================

law sp_ok:
  for +ps: LL()
  for +E: LL()
  for +z3: U32
  for +f3: U32
  for +L: Bool
  for +Fi: Bool
  for +G: Bool
  for +h: {LP.spec(ps, E, z3, f3, L, Fi, G) == True{} : Bool}
  {allok(ps) == True{} : Bool}

def sp_ok(ps, E, z3, f3, L, Fi, G, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +O = LP.okq(q, E)
      +S = LP.spec(t, LS.lapp(E, [q]), z3, f3, Bool.and(L, U32.is_eq(LP.lastb(q, 0), z3)), Bool.and(Fi, U32.is_eq(LP.headb(q, 0), f3)), Bool.and(G, Nat.is_le(2n, List.length(&2, U32, q))))
      +UL = Bool.and(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)))
      and_tt(UL, allok(t),
        LS.and_l(UL, Bool.not(LP.memb(q, E)), LS.and_l(O, S, h)),
        sp_ok(t, LS.lapp(E, [q]), z3, f3, Bool.and(L, U32.is_eq(LP.lastb(q, 0), z3)), Bool.and(Fi, U32.is_eq(LP.headb(q, 0), f3)), Bool.and(G, Nat.is_le(2n, List.length(&2, U32, q))), LS.and_r(O, S, h)))

# Distinct
# ========

law nat_eq_sym:
  for +a: Nat
  for +b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def nat_eq_sym(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat_eq_sym(p, q)

law u32_eq_sym:
  for +a: U32
  for +b: U32
  {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}

def u32_eq_sym(a, b):
  %Equal.sym(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U.is_eq_to_nat(a, b)) : {_ == U32.is_eq(b, a) : Bool}
  %Equal.sym(Bool, U32.is_eq(b, a), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), U.is_eq_to_nat(b, a)) : {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == _ : Bool}
  nat_eq_sym(U32.to_nat(a), U32.to_nat(b))

law leq_sym:
  for +x: List<&2, U32>
  for +y: List<&2, U32>
  {D.list_eq(x, y) == D.list_eq(y, x) : Bool}

def leq_sym(x, y):
  match x y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +s}:
      {==}
    case Con{+a, +r} Nil{}:
      {==}
    case Con{+a, +r} Con{+b, +s}:
      %u32_eq_sym(b, a) : {Bool.and(_, D.list_eq(r, s)) == Bool.and(U32.is_eq(b, a), D.list_eq(s, r)) : Bool}
      %Equal.sym(Bool, D.list_eq(r, s), D.list_eq(s, r), leq_sym(r, s)) : {Bool.and(U32.is_eq(b, a), _) == Bool.and(U32.is_eq(b, a), D.list_eq(s, r)) : Bool}
      {==}

law notin_nil:
  for +E: LL()
  {notin(E, Nil{}) == True{} : Bool}

def notin_nil(E):
  match E:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      notin_nil(t)

law notin_snoc:
  for +E: LL()
  for +q: List<&2, U32>
  for +t: LL()
  {notin(LS.lapp(E, [q]), t) == Bool.and(notin(E, t), Bool.not(LP.memb(q, t))) : Bool}

def notin_snoc(E, q, t):
  match E:
    case Nil{}:
      LS.and_true(Bool.not(LP.memb(q, t)))
    case Con{+e, +r}:
      +A = Bool.not(LP.memb(e, t))
      %Equal.sym(Bool, notin(LS.lapp(r, [q]), t), Bool.and(notin(r, t), Bool.not(LP.memb(q, t))), notin_snoc(r, q, t)) : {Bool.and(A, _) == Bool.and(Bool.and(A, notin(r, t)), Bool.not(LP.memb(q, t))) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(A, notin(r, t)), Bool.not(LP.memb(q, t))), Bool.and(A, Bool.and(notin(r, t), Bool.not(LP.memb(q, t)))), LS.and_assoc(A, notin(r, t), Bool.not(LP.memb(q, t))))

law notin_cons:
  for +E: LL()
  for +q: List<&2, U32>
  for +t: LL()
  for +h1: {notin(E, t) == True{} : Bool}
  for +h2: {LP.memb(q, E) == False{} : Bool}
  {notin(E, Con{q, t}) == True{} : Bool}

def notin_cons(E, q, t, h1, h2):
  match E:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      +hqe = or_f_l(D.list_eq(q, e), LP.memb(q, r), h2)
      +hqr = or_f_r(D.list_eq(q, e), LP.memb(q, r), h2)
      +A = Bool.not(LP.memb(e, t))
      +het = LS.not_t(LP.memb(e, t), LS.and_l(A, notin(r, t), h1))
      +hrt = LS.and_r(A, notin(r, t), h1)
      %Equal.sym(Bool, D.list_eq(e, q), False{}, Equal.trans(Bool, D.list_eq(e, q), D.list_eq(q, e), False{}, leq_sym(e, q), hqe)) :
        {Bool.and(Bool.not(Bool.or(_, LP.memb(e, t))), notin(r, Con{q, t})) == True{} : Bool}
      %Equal.sym(Bool, LP.memb(e, t), False{}, het) :
        {Bool.and(Bool.not(Bool.or(False{}, _)), notin(r, Con{q, t})) == True{} : Bool}
      notin_cons(r, q, t, hrt, hqr)

law sp_dist:
  for +ps: LL()
  for +E: LL()
  for +z3: U32
  for +f3: U32
  for +L: Bool
  for +Fi: Bool
  for +G: Bool
  for +h: {LP.spec(ps, E, z3, f3, L, Fi, G) == True{} : Bool}
  {Bool.and(dist(ps), notin(E, ps)) == True{} : Bool}

def sp_dist(ps, E, z3, f3, L, Fi, G, h):
  match ps:
    case Nil{}:
      notin_nil(E)
    case Con{+q, +t}:
      +O = LP.okq(q, E)
      +L2 = Bool.and(L, U32.is_eq(LP.lastb(q, 0), z3))
      +F2 = Bool.and(Fi, U32.is_eq(LP.headb(q, 0), f3))
      +G2 = Bool.and(G, Nat.is_le(2n, List.length(&2, U32, q)))
      +E2 = LS.lapp(E, [q])
      +S = LP.spec(t, E2, z3, f3, L2, F2, G2)
      +UL = Bool.and(LP.up(q), Nat.is_lt(0n, List.length(&2, U32, q)))
      +hqE = LS.not_t(LP.memb(q, E), LS.and_r(UL, Bool.not(LP.memb(q, E)), LS.and_l(O, S, h)))
      +ih = sp_dist(t, E2, z3, f3, L2, F2, G2, LS.and_r(O, S, h))
      +hdt = LS.and_l(dist(t), notin(E2, t), ih)
      +hn2 = Equal.trans(Bool, Bool.and(notin(E, t), Bool.not(LP.memb(q, t))), notin(E2, t), True{},
        Equal.sym(Bool, notin(E2, t), Bool.and(notin(E, t), Bool.not(LP.memb(q, t))), notin_snoc(E, q, t)), LS.and_r(dist(t), notin(E2, t), ih))
      and_tt(dist(Con{q, t}), notin(E, Con{q, t}),
        and_tt(Bool.not(LP.memb(q, t)), dist(t), LS.and_r(notin(E, t), Bool.not(LP.memb(q, t)), hn2), hdt),
        notin_cons(E, q, t, LS.and_l(notin(E, t), Bool.not(LP.memb(q, t)), hn2), hqE))

# The flags
# =========

def FLG(+L: Bool, +Fi: Bool, +G: Bool, +z3: U32, +f3: U32, +ps: LL()) -> Bool:
  Bool.and(Bool.not(Bool.and(L, lasts(z3, ps))), Bool.not(Bool.and(Bool.and(Fi, firsts(f3, ps)), Bool.and(G, longs(ps)))))

law sp_flags:
  for +ps: LL()
  for +E: LL()
  for +z3: U32
  for +f3: U32
  for +L: Bool
  for +Fi: Bool
  for +G: Bool
  for +h: {LP.spec(ps, E, z3, f3, L, Fi, G) == True{} : Bool}
  {FLG(L, Fi, G, z3, f3, ps) == True{} : Bool}

def sp_flags(ps, E, z3, f3, L, Fi, G, h):
  match ps:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(L, True{}), L, LS.and_true(L)) :
        {Bool.and(Bool.not(_), Bool.not(Bool.and(Bool.and(Fi, True{}), Bool.and(G, True{})))) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Fi, True{}), Fi, LS.and_true(Fi)) :
        {Bool.and(Bool.not(L), Bool.not(Bool.and(_, Bool.and(G, True{})))) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(G, True{}), G, LS.and_true(G)) :
        {Bool.and(Bool.not(L), Bool.not(Bool.and(Fi, _))) == True{} : Bool}
      h
    case Con{+q, +t}:
      +eL = U32.is_eq(LP.lastb(q, 0), z3)
      +eF = U32.is_eq(LP.headb(q, 0), f3)
      +eG = Nat.is_le(2n, List.length(&2, U32, q))
      +O = LP.okq(q, E)
      +S = LP.spec(t, LS.lapp(E, [q]), z3, f3, Bool.and(L, eL), Bool.and(Fi, eF), Bool.and(G, eG))
      %LS.and_assoc(L, eL, lasts(z3, t)) :
        {Bool.and(Bool.not(_), Bool.not(Bool.and(Bool.and(Fi, Bool.and(eF, firsts(f3, t))), Bool.and(G, Bool.and(eG, longs(t)))))) == True{} : Bool}
      %LS.and_assoc(Fi, eF, firsts(f3, t)) :
        {Bool.and(Bool.not(Bool.and(Bool.and(L, eL), lasts(z3, t))), Bool.not(Bool.and(_, Bool.and(G, Bool.and(eG, longs(t)))))) == True{} : Bool}
      %LS.and_assoc(G, eG, longs(t)) :
        {Bool.and(Bool.not(Bool.and(Bool.and(L, eL), lasts(z3, t))), Bool.not(Bool.and(Bool.and(Bool.and(Fi, eF), firsts(f3, t)), _))) == True{} : Bool}
      sp_flags(t, LS.lapp(E, [q]), z3, f3, Bool.and(L, eL), Bool.and(Fi, eF), Bool.and(G, eG), LS.and_r(O, S, h))
