import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/defs.bend as A
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_b_rundefs.bend as RD

# General lemmas for the run area (proof_b_run.bend): Bools, the depth of a
# mirrored block.

# Bools
# =====

law and_mk:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_mk(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

law andl:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def andl(a, b, e):
  AB.and_true_l(a, b, e)

law andr:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def andr(a, b, e):
  AB.and_true_r(a, b, e)

# The depth of a block
# ====================

law full_td:
  for +t: AT.Tree<U32>
  for +d: Nat
  for +h: {A.full(U32, AT.fromT(U32, t), d) == True{} : Bool}
  {RD.tdepth(t) == d : Nat}

def full_td(t, d, h):
  match t d:
    case AT.TLeaf{+x} 0n:
      {==}
    case AT.TLeaf{+x} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, AB.false_ne_true(h))
    case AT.TNode{+l, +r} 0n:
      Empty.absurd({1n+RD.tdepth(l) == 0n : Nat}, AB.false_ne_true(h))
    case AT.TNode{+l, +r} 1n+p:
      +hl = andl(A.full(U32, AT.fromT(U32, l), p), A.full(U32, AT.fromT(U32, r), p), h)
      %full_td(l, p, hl) : {1n+RD.tdepth(l) == 1n+_ : Nat}
      {==}

# A well-formed buffer is well formed at its tree's depth.
law ok_td:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {D.ok(C.BT(len, t), RD.tdepth(t)) == True{} : Bool}

def ok_td(len, t, d, h):
  AB.subst(Nat, x => {D.ok(C.BT(len, t), x) == True{} : Bool}, d, RD.tdepth(t),
    Equal.sym(Nat, RD.tdepth(t), d, full_td(t, d, C.ok_full(len, t, d, h))), h)
