import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# The run area's invariant (definitions only; the proofs are in
# proof_b_run*.bend). No closed big number occurs in it (ob's bound is a U32
# comparison), so the checker may unfold it freely.

# The depth of a mirrored block (along its left edge).
def tdepth(t: AT.Tree<U32>) -> Nat:
  match t:
    case AT.TLeaf{x}:
      0n
    case AT.TNode{l, r}:
      1n+tdepth(l)

# The texts' lengths of a list of items.
def lens(xs: List<&2, NR.Ck>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{c, t}:
      Nat.add(U32.to_nat(NR.Ck.len(c)), lens(t))

# Every key is at most k.
def keys_le(xs: List<&2, NR.Ck>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{c, t}:
      Nat.is_le(NR.Ck.key(c), k) && keys_le(t, k)

def is_nil(xs: List<&2, NR.Ck>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{c, t}:
      False{}

# The buffered items (front, then back reversed).
def items(f: List<&2, NR.Ck>, b: List<&2, NR.Ck>) -> List<&2, NR.Ck>:
  NR.append_ck(f, NR.rev_ck(b, Nil{}))

def no_notes(ns: List<&2, B.Note>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, t}:
      False{}

# Before the #CHROM line, nothing is in ob or buffered, and nothing noted
# while the run goes on.
def pre(i: Bool, +obl: U32, f: List<&2, NR.Ck>, b: List<&2, NR.Ck>, x: Bool, ns: List<&2, B.Note>) -> Bool:
  match i:
    case True{}:
      True{}
    case False{}:
      U32.is_zero(obl) && (is_nil(f) && (is_nil(b) && (x || no_notes(ns))))

# The invariant, by parts:
#   ob well formed (at its block's depth), at most 2^30 bytes;
#   cb well formed, holding the current CHROM;
#   ow plus the buffered texts' lengths is ob's length, and bn counts the
#   buffered items, unless the run stopped (an UNSORTED stop drops the
#   front list); ow is at most ob's length; tl bounds the buffered keys;
#   the held header is bytes; before #CHROM nothing in ob or buffered, and
#   nothing noted unless the run stopped.
def inv.k(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool) -> Bool:
  D.ok(C.BT(obl, obt), tdepth(obt))
  && (U32.is_le(obl, 1073741824)
  && (D.ok(C.BT(cbl, cbt), tdepth(cbt))
  && (String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, ""))
  && (Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), lens(items(f, b))), U32.to_nat(obl)))
  && (Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b))))
  && (keys_le(f, tl)
  && (keys_le(b, tl)
  && (E.is_bytes(h)
  && (pre(i, obl, f, b, x, ns)
  && (Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))))))))))))

def RunInv(+p: P.RunP) -> Bool:
  match p:
    case P.RunP{n, +i, +h, +c, +cbl, +cbt, e, l, +f, +b, +bn, +tl, k, +obl, +obt, +ow, +ns, +x}:
      inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)
