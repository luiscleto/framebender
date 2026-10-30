import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as F
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-bytes@0.1.0.0/proof_seq.bend as Q
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_b_alleles_list.bend as LS

# Small word and buffer facts for adv_ok (the same as proof_b_alleles_loop's,
# without its import of fast.bend). Every variable is reusable.

law le_u:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}
  {U32.is_le(a, b) == True{} : Bool}

def le_u(a, b, h):
  %Equal.sym(Bool, U32.is_le(a, b), Nat.is_le(U32.to_nat(a), U32.to_nat(b)), U.is_le_to_nat(a, b)) : {_ == True{} : Bool}
  h

law sub_u:
  for +a: U32
  for +b: U32
  for +h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  {U32.to_nat((a - b : U32)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def sub_u(a, b, h):
  U.to_nat_sub_le(a, b, le_u(b, a, h))

law len_x:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {U32.to_nat(len) == List.length(&2, U32, D.view(C.BT(len, t))) : Nat}

def len_x(len, t, d, h):
  Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(len, t))), U32.to_nat(len), O.view_size_t(len, t, d, h))

# A word below len steps up by one.
law inc_len:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(U32.to_nat(c), U32.to_nat(len)) == True{} : Bool}
  {U32.to_nat((c + 1 : U32)) == Nat.add(U32.to_nat(c), 1n) : Nat}

def inc_len(len, t, d, c, h, hc):
  C.inc_fits(c, d, C.ok_d(len, t, d, h), F.step_lt4(len, t, d, c, h, hc))

# Lists and Nat (copied from proof_b_alleles_loop.bend)

law len_drop:
  for +xs: List<&2, U32>
  for +k: Nat
  {List.length(&2, U32, List.drop(&2, U32, xs, k)) == Nat.sub(List.length(&2, U32, xs), k) : Nat}

def len_drop(xs, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      len_drop(t, p)

law le_sub_r:
  for +i: Nat
  for +k: Nat
  for +m: Nat
  for +h: {Nat.is_le(Nat.add(i, k), m) == True{} : Bool}
  {Nat.is_le(k, Nat.sub(m, i)) == True{} : Bool}

def le_sub_r(i, k, m, h):
  match i m:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.is_le(k, _) == True{} : Bool}
      h
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(k, 0n) == True{} : Bool}, LS.ft(h))
    case 1n+p 1n+q:
      le_sub_r(p, k, q, h)

law slice_len:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  for +h: {Nat.is_le(Nat.add(i, k), List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, D.slice(xs, i, k)) == k : Nat}

def slice_len(xs, i, k, h):
  +L = List.drop(&2, U32, xs, i)
  Q.take_length(L, k,
    %Equal.sym(Nat, List.length(&2, U32, L), Nat.sub(List.length(&2, U32, xs), i), len_drop(xs, i)) : {Nat.is_le(k, _) == True{} : Bool}
    le_sub_r(i, k, List.length(&2, U32, xs), h))

law pos_sub:
  for +a: Nat
  for +c: Nat
  for +h: {Nat.is_lt(a, c) == True{} : Bool}
  {Nat.is_lt(0n, Nat.sub(c, a)) == True{} : Bool}

def pos_sub(a, c, h):
  %Equal.sym(Nat, Nat.sub(c, a), 1n+Nat.sub(c, Nat.add(a, 1n)), LS.sub_lt(c, a, h)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}
