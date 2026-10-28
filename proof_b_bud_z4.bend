import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_adv_hit.bend as FH
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ./proof_b_bud_z4k.bend as ZK

# Z4 (pb-cache; notes/bytes_proofs_budget.md): with the line's zero window held
# and fitting (bi's zheld), the fast path's window test does not say WNeed.
# hcl added (pb-cache): the window's contig name is at most 2^28 bytes, as
# mb_win gives it (NR.of_str needs it); the proof is proof_b_bud_z4k.bend.
def against_zero(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hz: {BN.zheld(CD.mkWin(fa, CD.WPKnown{c, a, b}), P.btext(len, t, at, (e0 - at : U32)),
    Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  ZK.against_zero.k(fa, c, a, b, len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hb, hwp, hcl, hok, hs, hp, hse, hz)
