import Base
import ./norm.bend as Norm
import ./proof_b_lit.bend as PL
import ./proof_b_run_num.bend as NM
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# Size bounds of the run area from the program's word checks (Norm.len_le),
# through proof_b_lit.bend's bridges. Exponents stay variables until the end.

# len_le(s, w) with w = 1 << k gives |s| <= 2^k.
def lenw(+s: String, +w: U32, +k: Nat, hw: {U32.shln(1, k) == w : U32}, hk: {Nat.is_lt(k, 32n) == True{} : Bool},
  h: {Norm.len_le(s, w) == True{} : Bool}) -> {Nat.is_le(String.length(s), Nat.pow(2n, k)) == True{} : Bool}:
  AB.subst(Nat, y => {Nat.is_le(String.length(s), y) == True{} : Bool}, U32.to_nat(w), Nat.pow(2n, k), PL.lit_pow(k, w, hw, hk),
    PL.len_le_le(s, w, h))

def len30(+s: String, h: {Norm.len_le(s, 1073741824) == True{} : Bool}) -> {Nat.is_le(String.length(s), Nat.pow(2n, 30n)) == True{} : Bool}:
  lenw(s, 1073741824, 30n, {==}, {==}, h)

def len28(+s: String, h: {Norm.len_le(s, 268435456) == True{} : Bool}) -> {Nat.is_le(String.length(s), Nat.pow(2n, 28n)) == True{} : Bool}:
  lenw(s, 268435456, 28n, {==}, {==}, h)

# x <= 2^28 gives x <= 2^30.
def le28_30(+x: Nat, h: {Nat.is_le(x, Nat.pow(2n, 28n)) == True{} : Bool}) -> {Nat.is_le(x, Nat.pow(2n, 30n)) == True{} : Bool}:
  N.le_trans(x, Nat.pow(2n, 28n), Nat.pow(2n, 30n), h, N.pow_le(28n, 30n, {==}))

# x <= 2^30 gives x + 8 < 2^31 (as D.ok writes it).
def lt31(+x: Nat, h: {Nat.is_le(x, Nat.pow(2n, 30n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}:
  NM.b8(x, 29n, 30n, {==}, {==}, h)
