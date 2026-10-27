import Base
import ./proof_base.bend as P

# Arithmetic and String lemmas for the machine proof (proof_machine.bend).

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      P.le_zero_l(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, P.false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, P.false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

# a <= b gives a <= b + 1.
law le_succ_r:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}

def le_succ_r(a, b, e):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p 1n+q:
      le_succ_r(p, q, e)

law le_succ:
  for +a: Nat
  {Nat.is_le(a, 1n+a) == True{} : Bool}

def le_succ(a):
  le_succ_r(a, a, P.le_refl(a))

# b <= c gives a + b <= a + c.
law le_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}

def le_add_l(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+p:
      le_add_l(p, b, c, e)

# a <= c gives a <= b + c.
law le_add_left:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.is_le(a, c) == True{} : Bool}
  {Nat.is_le(a, Nat.add(b, c)) == True{} : Bool}

def le_add_left(a, b, c, e):
  match b:
    case 0n:
      e
    case 1n+p:
      le_succ_r(a, Nat.add(p, c), le_add_left(a, p, c, e))

law mul_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def mul_add_r(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), mul_add_r(p, b, c)) :
        {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
        P.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

# a <= b gives a * c <= b * c.
law le_mul_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

def le_mul_r(a, b, c, e):
  match a b:
    case 0n _:
      P.le_zero_l(Nat.mul(b, c))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+p, c), 0n) == True{} : Bool}, P.false_ne_true(e))
    case 1n+p 1n+q:
      le_add_l(c, Nat.mul(p, c), Nat.mul(q, c), le_mul_r(p, q, c, e))

# Strings
# =======

law str_assoc:
  for +a: String
  for +b: String
  for +c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def str_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %str_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

law str_nil:
  for +a: String
  {String.append(a, "") == a : String}

def str_nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %str_nil(t) : {SCon{h, String.append(t, "")} == SCon{h, _} : String}
      {==}

law str_len_append:
  for +a: String
  for +b: String
  {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}

def str_len_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %str_len_append(t, b) : {1n+String.length(String.append(t, b)) == 1n+_ : Nat}
      {==}
