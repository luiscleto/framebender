import Base
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_cut_nat.bend as Z
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./proof_b_cut_str.bend as S
import ./proof_b_cut_ne2.bend as NE2
import ./proof_b_cut_ne.bend as E
import lawful-bytes@0.1.1.0/proof_find.bend as PF
import lawful-bytes@0.1.1.0/proof_list.bend as PL
import lawful-bytes@0.1.1.0/proof_shift.bend as PSh
import lawful-words@0.1.0.0/proof_u32.bend as U

# The field ends of a passed line as facts about its view (E-form: the ends
# are M.E0 .. M.E7 of s), and the LF of the line.

def LFG(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> Type:
  {D.first(Z.X(len, t), Z.n(s), Z.n(len), 10) == Z.n(lf) : Nat} & ({Nat.is_lt(Z.n(lf), Z.n(len)) == True{} : Bool} & ({Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s))) == True{} : Bool} & ({Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s))) == True{} : Bool} & ({Nat.is_le(Z.n(M.E7(len, t, s)), Z.n(lf)) == True{} : Bool}))))))))))

# The two cases of lf_q, each with its LF written out (M.E7, M.LF1): lf_q
# then reaches V.LFm through one small equation. Stated through V.LFm, the
# kernel (--verdict) compared the whole result by normalizing E7, eight
# nested searches, and ran past 4 GB.
def lf_qF(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +hq: {U32.is_eq(C.AT(len, t, M.E7(len, t, s)), 9) == False{} : Bool}) ->
  LFG(len, t, s, M.E7(len, t, s)):
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  (Equal.trans(Nat, D.first(Z.X(len, t), Z.n(s), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s)), Z.n(len), hL, f0, l0, u0, t0), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s)), Z.n(len), hL, f1, l1, u1, t1), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s)), Z.n(len), hL, f2, l2, u2, t2), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s)), Z.n(len), hL, f3, l3, u3, t3), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s)), Z.n(len), hL, f4, l4, u4, t4), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s)), Z.n(len), hL, f5, l5, u5, t5), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 10), Z.n(M.E7(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s)), Z.n(len), hL, f6, l6, u6, t6), Z.hit10(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s)), Z.n(len), hL, f7, l7, u7, Z.lf10(len, t, d, Nat.add(Z.n(M.E6(len, t, s)), 1n), M.E7(len, t, s), hok, f7, l7, u7, hq))))))))), (u7, (l0, (Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), (Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), (Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), (Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), (Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), (Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), (Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7), N.le_refl(Z.n(M.E7(len, t, s)))))))))))))

def lf_qT(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +hq: {U32.is_eq(C.AT(len, t, M.E7(len, t, s)), 9) == True{} : Bool}, +hl: {U32.is_eq(M.LJ(len, t, (M.E7(len, t, s) + 1 : U32)), len) == False{} : Bool}) ->
  LFG(len, t, s, M.LF1(len, t, s)):
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  (Equal.trans(Nat, D.first(Z.X(len, t), Z.n(s), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s)), Z.n(len), hL, f0, l0, u0, t0), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s)), Z.n(len), hL, f1, l1, u1, t1), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s)), Z.n(len), hL, f2, l2, u2, t2), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s)), Z.n(len), hL, f3, l3, u3, t3), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s)), Z.n(len), hL, f4, l4, u4, t4), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s)), Z.n(len), hL, f5, l5, u5, t5), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s)), Z.n(len), hL, f6, l6, u6, t6), Equal.trans(Nat, D.first(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 10), D.first(Z.X(len, t), Nat.add(Z.n(M.E7(len, t, s)), 1n), Z.n(len), 10), Z.n(M.LF1(len, t, s)), Z.skip10(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s)), Z.n(len), hL, f7, l7, u7, Z.tabget(len, t, d, M.E7(len, t, s), 9, hok, u7, hq)), AB.subst(Nat, z => {D.first(Z.X(len, t), z, Z.n(len), 10) == Z.n(M.LF1(len, t, s)) : Nat}, Z.n((M.E7(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E7(len, t, s)), 1n), i7, Equal.sym(Nat, Z.n(M.LF1(len, t, s)), D.first(Z.X(len, t), Z.n((M.E7(len, t, s) + 1 : U32)), Z.n(len), 10), Z.lff1(len, t, Z.n((M.E7(len, t, s) + 1 : U32)), M.LF1(len, t, s), Z.lff(len, t, d, (M.E7(len, t, s) + 1 : U32), hok, b8, hl)))))))))))), (Z.lff3(len, t, Z.n((M.E7(len, t, s) + 1 : U32)), M.LF1(len, t, s), Z.lff(len, t, d, (M.E7(len, t, s) + 1 : U32), hok, b8, hl)), (l0, (Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), (Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), (Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), (Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), (Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), (Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), (Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7), N.lt_to_le(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)), Z.succ_lt(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)), AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.LF1(len, t, s))) == True{} : Bool}, Z.n((M.E7(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E7(len, t, s)), 1n), i7, Z.lff2(len, t, Z.n((M.E7(len, t, s) + 1 : U32)), M.LF1(len, t, s), Z.lff(len, t, d, (M.E7(len, t, s) + 1 : U32), hok, b8, hl)))))))))))))))

def lf_q(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +q: Bool, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +hq: {U32.is_eq(C.AT(len, t, M.E7(len, t, s)), 9) == q : Bool}, +hl: {V.LPm(len, t, s, q) == False{} : Bool}) ->
  LFG(len, t, s, V.LFm(len, t, s, q)):
  match q:
    case False{}:
      AB.subst(U32, z => LFG(len, t, s, z), M.E7(len, t, s), V.LFm(len, t, s, False{}), {==},
        lf_qF(len, t, d, s, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, hq))
    case True{}:
      AB.subst(U32, z => LFG(len, t, s, z), M.LF1(len, t, s), V.LFm(len, t, s, True{}), {==},
        lf_qT(len, t, d, s, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, hq, AB.subst(Bool, x => {x == False{} : Bool}, V.LPm(len, t, s, True{}), U32.is_eq(M.LJ(len, t, (M.E7(len, t, s) + 1 : U32)), len), {==}, hl)))

# pass_lf in E-form.
def lf_core(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool}) ->
  LFG(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))):
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  lf_q(len, t, d, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, {==}, hl)

def ltE0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u0

def ltE1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u1

def ltE2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u2

def ltE3(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u3

def ltE4(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u4

def ltE5(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u5

def ltE6(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u6

def ltE7(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  u7

# ---------------------------------------------------------------------------
# pass_fields in E-form
# ---------------------------------------------------------------------------

def FDG(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> Type:
  {J.pfs(B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(lf))))) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(lf))))), 7n)] : List<&2, String>}

# The fields of the text s .. bd-1 (bd at or after INFO's end, a tab there
# when after).
def fields0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +bd: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hE7B: {Nat.is_le(Z.n(M.E7(len, t, s)), bd) == True{} : Bool}, +hBX: {Nat.is_le(bd, List.length(&2, U32, Z.X(len, t))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), bd)) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool}) ->
  {J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}:
  +heB6 = N.lt_le_trans(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), bd, Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7), hE7B)
  +heB5 = N.lt_trans(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), bd, Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), heB6)
  +heB4 = N.lt_trans(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), bd, Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), heB5)
  +heB3 = N.lt_trans(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), bd, Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), heB4)
  +heB2 = N.lt_trans(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), bd, Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), heB3)
  +heB1 = N.lt_trans(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), bd, Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), heB2)
  +heB0 = N.lt_trans(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), bd, Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), heB1)
  +c0 = S.cut_fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s)), bd, l0, heB0, Z.first9(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s)), bd, Z.n(len), hBX, f0, l0, heB0, t0), t0)
  +c1 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s)), bd, l1, heB1, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s)), bd, Z.n(len), hBX, f1, l1, heB1, t1), t1)
  +c2 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s)), bd, l2, heB2, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s)), bd, Z.n(len), hBX, f2, l2, heB2, t2), t2)
  +c3 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s)), bd, l3, heB3, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s)), bd, Z.n(len), hBX, f3, l3, heB3, t3), t3)
  +c4 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s)), bd, l4, heB4, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s)), bd, Z.n(len), hBX, f4, l4, heB4, t4), t4)
  +c5 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s)), bd, l5, heB5, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s)), bd, Z.n(len), hBX, f5, l5, heB5, t5), t5)
  +c6 = S.cut_fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s)), bd, l6, heB6, Z.first9(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s)), bd, Z.n(len), hBX, f6, l6, heB6, t6), t6)
  +hff7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n((M.E6(len, t, s) + 1 : U32)), Equal.sym(Nat, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6), f7)
  +hft7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n((M.E6(len, t, s) + 1 : U32)), Equal.sym(Nat, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6), l7)
  +F0 = S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s)))
  +F1 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s)))
  +F2 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s)))
  +F3 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s)))
  +F4 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s)))
  +F5 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s)))
  +F6 = S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s)))
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Z.n(s), bd)), J.Cut{F0, S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), True{}}, c0) : {J.pfs.g(J.c7.a(_), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd)), J.Cut{F1, S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), True{}}, c1) : {J.pfs.g(J.c7.b(F0, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd)), J.Cut{F2, S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), True{}}, c2) : {J.pfs.g(J.c7.c(F0, F1, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd)), J.Cut{F3, S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), True{}}, c3) : {J.pfs.g(J.c7.d(F0, F1, F2, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd)), J.Cut{F4, S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), True{}}, c4) : {J.pfs.g(J.c7.e(F0, F1, F2, F3, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd)), J.Cut{F5, S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), True{}}, c5) : {J.pfs.g(J.c7.f(F0, F1, F2, F3, F4, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  %Equal.sym(J.Cut, J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd)), J.Cut{F6, S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd), True{}}, c6) : {J.pfs.g(J.c7.g(F0, F1, F2, F3, F4, F5, _), S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))] : List<&2, String>}
  {==}

# The fields of the text s .. bd-1, INFO as J.pfs keeps it (its own field 7).
def fields(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +bd: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hE7B: {Nat.is_le(Z.n(M.E7(len, t, s)), bd) == True{} : Bool}, +hBX: {Nat.is_le(bd, List.length(&2, U32, Z.X(len, t))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), bd)) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool}) ->
  {J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), 7n)] : List<&2, String>}:
  +P = fields0(len, t, d, s, bd, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, hE7B, hBX, hend7)
  Equal.trans(List<&2, String>, J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))], [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), 7n)], P,
    Equal.cong(String, List<&2, String>, z => [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), z], J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), B.Rec.field(J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), 7n),
      Equal.sym(String, B.Rec.field(J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), 7n), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 7n), J.pfs(S.fld(Z.X(len, t), Z.n(s), bd)), [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), J.info.if(J.noend(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))], P))))

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(h))
    case False{}:
      {==}

# The last byte before e (e > a): its index c = e - 1 as a word.
def LST(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}) -> Type:
  {Nat.add(Z.n((e - 1 : U32)), 1n) == Z.n(e) : Nat} & ({Nat.is_le(a, Z.n((e - 1 : U32))) == True{} : Bool}
    & {List.get(&2, U32, Z.X(len, t), Z.n((e - 1 : U32))) == Some{C.AT(len, t, (e - 1 : U32))} : Maybe<&2, U32>})

def lst(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}) -> LST(len, t, d, a, e, hok, hae, hel):
  +ne = Z.n(e)
  +h1n = N.le_trans(1n, Nat.add(a, 1n), ne, N.le_add_l(1n, a), C.succ_le(a, ne, hae))
  +pc = U.to_nat_sub_le(e, 1, Z.nle(1, e, h1n))
  +c = Z.n((e - 1 : U32))
  +hc = Equal.trans(Nat, Nat.add(c, 1n), Nat.add(Nat.sub(ne, 1n), 1n), ne, Equal.cong(Nat, Nat, z => Nat.add(z, 1n), c, Nat.sub(ne, 1n), pc),
    Equal.trans(Nat, Nat.add(Nat.sub(ne, 1n), 1n), Nat.add(1n, Nat.sub(ne, 1n)), ne, N.add_comm(Nat.sub(ne, 1n), 1n), N.le_sub_add(1n, ne, h1n)))
  +hac = AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, Nat.sub(ne, 1n), c, Equal.sym(Nat, c, Nat.sub(ne, 1n), pc),
    N.le_sub_r(1n, a, ne, Equal.trans(Bool, Nat.is_le(1n+a, ne), Nat.is_lt(a, ne), True{}, N.le_succ_lt(a, ne), hae)))
  +hcl = AB.subst(Nat, z => {Nat.is_lt(z, Z.n(len)) == True{} : Bool}, Nat.sub(ne, 1n), c, Equal.sym(Nat, c, Nat.sub(ne, 1n), pc),
    N.le_lt_trans(Nat.sub(ne, 1n), ne, Z.n(len), PSh.sub_le(ne, 1n), hel))
  (hc, (hac, PF.step_get(len, t, d, (e - 1 : U32), hok, hcl)))

def lst1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}, r: LST(len, t, d, a, e, hok, hae, hel)) -> {Nat.add(Z.n((e - 1 : U32)), 1n) == Z.n(e) : Nat}:
  match r:
    case (x, y):
      x

def lst2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}, r: LST(len, t, d, a, e, hok, hae, hel)) -> {Nat.is_le(a, Z.n((e - 1 : U32))) == True{} : Bool}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          u

def lst3(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}, r: LST(len, t, d, a, e, hok, hae, hel)) ->
  {List.get(&2, U32, Z.X(len, t), Z.n((e - 1 : U32))) == Some{C.AT(len, t, (e - 1 : U32))} : Maybe<&2, U32>}:
  match r:
    case (x, y):
      match y:
        case (u, v):
          v

def BE(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: Nat, +e: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hae: {Nat.is_lt(a, Z.n(e)) == True{} : Bool},
  +hel: {Nat.is_lt(Z.n(e), Z.n(len)) == True{} : Bool}) ->
  {B.Line.body(Norm.line(S.fld(Z.X(len, t), a, Z.n(e)))) == S.BDY(Z.X(len, t), a, Z.n(e), Z.n((e - 1 : U32)), U32.is_eq(C.AT(len, t, (e - 1 : U32)), 13)) : String}:
  S.body_eq(Z.X(len, t), a, Z.n(e), Z.n((e - 1 : U32)), C.AT(len, t, (e - 1 : U32)),
    lst1(len, t, d, a, e, hok, hae, hel, lst(len, t, d, a, e, hok, hae, hel)),
    lst2(len, t, d, a, e, hok, hae, hel, lst(len, t, d, a, e, hok, hae, hel)),
    Z.le_len(len, t, d, Z.n(e), hok, N.lt_to_le(Z.n(e), Z.n(len), hel)),
    lst3(len, t, d, a, e, hok, hae, hel, lst(len, t, d, a, e, hok, hae, hel)))

def fd_cr(+cr: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hcr: {U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13) == cr : Bool},
  +hsl: {Nat.is_lt(Z.n(s), Z.n(M.LF1(len, t, s))) == True{} : Bool}, +hll: {Nat.is_lt(Z.n(M.LF1(len, t, s)), Z.n(len)) == True{} : Bool},
  +h7l: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)))) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool},
  +hend8: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)))) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool}) -> FDG(len, t, s, M.LF1(len, t, s)):
  match cr:
    case False{}:
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s))))), S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)), U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13)),
        BE(len, t, d, Z.n(s), M.LF1(len, t, s), hok, hsl, hll)) : {J.pfs(_) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(_), 7n)] : List<&2, String>}
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13), False{}, hcr) :
        {J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)), _)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)), _)), 7n)] : List<&2, String>}
      fields(len, t, d, s, Z.n(M.LF1(len, t, s)), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, N.lt_to_le(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)), h7l),
        Z.le_len(len, t, d, Z.n(M.LF1(len, t, s)), hok, N.lt_to_le(Z.n(M.LF1(len, t, s)), Z.n(len), hll)), hend7)
    case True{}:
      +c = Z.n((M.LF1(len, t, s) - 1 : U32))
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s))))), S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), c, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13)),
        BE(len, t, d, Z.n(s), M.LF1(len, t, s), hok, hsl, hll)) : {J.pfs(_) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(_), 7n)] : List<&2, String>}
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13), True{}, hcr) :
        {J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), c, _)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), c, _)), 7n)] : List<&2, String>}
      r = lst(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll)
      +hcX = N.le_trans(c, Z.n(M.LF1(len, t, s)), List.length(&2, U32, Z.X(len, t)), N.le_trans(c, Nat.add(c, 1n), Z.n(M.LF1(len, t, s)), N.le_add_r(c, 1n),
        AB.subst(Nat, z => {Nat.is_le(Nat.add(c, 1n), z) == True{} : Bool}, Nat.add(c, 1n), Z.n(M.LF1(len, t, s)), lst1(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll, lst(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll)), N.le_refl(Nat.add(c, 1n)))),
        Z.le_len(len, t, d, Z.n(M.LF1(len, t, s)), hok, N.lt_to_le(Z.n(M.LF1(len, t, s)), Z.n(len), hll)))
      fields(len, t, d, s, c, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, lst2(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll, r), hcX, hend8)

def fd_q(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +q: Bool, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hq: {U32.is_eq(C.AT(len, t, M.E7(len, t, s)), 9) == q : Bool}, +hl: {V.LPm(len, t, s, q) == False{} : Bool},
  +hcrt: {M.CRT(len, t, M.E7(len, t, s), V.LFm(len, t, s, q)) == True{} : Bool}) ->
  FDG(len, t, s, V.LFm(len, t, s, q)):
  match q:
    case False{}:
      +e7 = M.E7(len, t, s)
      +hsl = N.le_lt_trans(Z.n(s), Z.n(M.E0(len, t, s)), Z.n(M.E7(len, t, s)), l0, N.lt_trans(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), N.lt_trans(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), N.lt_trans(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), N.lt_trans(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), N.lt_trans(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), N.lt_trans(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7))))))))
      +hx = AB.subst(Bool, z => {Bool.not(z && U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13)) == True{} : Bool}, U32.is_eq(e7, e7), True{}, PL.pl_u32_eq_refl(e7), hcrt)
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(e7)))), S.BDY(Z.X(len, t), Z.n(s), Z.n(e7), Z.n((e7 - 1 : U32)), U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13)),
        BE(len, t, d, Z.n(s), e7, hok, hsl, u7)) : {J.pfs(_) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(_), 7n)] : List<&2, String>}
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13), False{}, not_true(U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13), hx)) :
        {J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(e7), Z.n((e7 - 1 : U32)), _)) == [S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), B.Rec.field(J.pfs(S.BDY(Z.X(len, t), Z.n(s), Z.n(e7), Z.n((e7 - 1 : U32)), _)), 7n)] : List<&2, String>}
      +hend7 = AB.subst(Bool, z => {(Bool.not(z) || D.has(Z.X(len, t), Z.n(e7), 9)) == True{} : Bool}, False{}, Nat.is_lt(Z.n(e7), Z.n(e7)), Equal.sym(Bool, Nat.is_lt(Z.n(e7), Z.n(e7)), False{}, N.lt_irrefl(Z.n(e7))), {==})
      fields(len, t, d, s, Z.n(e7), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, N.le_refl(Z.n(e7)), Z.le_len(len, t, d, Z.n(e7), hok, N.lt_to_le(Z.n(e7), Z.n(len), u7)), hend7)
    case True{}:
      +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
      LFr = Z.lff(len, t, d, (M.E7(len, t, s) + 1 : U32), hok, b8, hl)
      +nA8 = Z.n((M.E7(len, t, s) + 1 : U32))
      +lf1 = M.LF1(len, t, s)
      +lfle = AB.subst(Nat, z => {Nat.is_le(z, Z.n(lf1)) == True{} : Bool}, nA8, Nat.add(Z.n(M.E7(len, t, s)), 1n), i7, Z.lff2(len, t, nA8, lf1, Z.lff(len, t, d, (M.E7(len, t, s) + 1 : U32), hok, b8, hl)))
      +h7l = Z.succ_lt(Z.n(M.E7(len, t, s)), Z.n(lf1), lfle)
      +hll = Z.lff3(len, t, nA8, lf1, LFr)
      +hsl = N.lt_trans(Z.n(s), Z.n(M.E7(len, t, s)), Z.n(lf1), N.le_lt_trans(Z.n(s), Z.n(M.E0(len, t, s)), Z.n(M.E7(len, t, s)), l0, N.lt_trans(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), N.lt_trans(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), N.lt_trans(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), N.lt_trans(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), N.lt_trans(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), N.lt_trans(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7)))))))), h7l)
      +t7 = Z.tabget(len, t, d, M.E7(len, t, s), 9, hok, u7, hq)
      +has7 = Equal.trans(Bool, D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9), U32.is_eq(9, 9), True{}, Z.has_get(Z.X(len, t), Z.n(M.E7(len, t, s)), 9, 9, t7), {==})
      +hend7 = AB.subst(Bool, z => {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(lf1))) || z) == True{} : Bool}, True{}, D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9), Equal.sym(Bool, D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9), True{}, has7), E.or_true_r(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(lf1)))))
      +hend8 = AB.subst(Bool, z => {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n((lf1 - 1 : U32)))) || z) == True{} : Bool}, True{}, D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9), Equal.sym(Bool, D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9), True{}, has7), E.or_true_r(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n((lf1 - 1 : U32))))))
      fd_cr(U32.is_eq(C.AT(len, t, (lf1 - 1 : U32)), 13), len, t, d, s, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, {==}, hsl, hll, h7l, hend7, hend8)

# pass_fields in E-form.
def fd_core(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hcrt: {M.CRT(len, t, M.E7(len, t, s), V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == True{} : Bool}) ->
  FDG(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))):
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  fd_q(len, t, d, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, {==}, hl, hcrt)

def lE1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool}) ->
  {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}:
  +hL = Z.le_len(len, t, d, Z.n(len), hok, N.le_refl(Z.n(len)))
  +f0 = Z.ff1(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +l0 = Z.ff2(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +u0 = Z.ff3(len, t, Z.n(s), M.E0(len, t, s), Z.fld_t(len, t, d, s, hok, hs, h0))
  +t0 = Z.tabget(len, t, d, M.E0(len, t, s), 9, hok, u0, h1)
  +i0 = Z.nx1(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +b1 = Z.nx2(len, M.E0(len, t, s), Z.nxt(len, t, d, M.E0(len, t, s), hok, u0))
  +f1 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff1(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +l1 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E1(len, t, s))) == True{} : Bool}, Z.n((M.E0(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E0(len, t, s)), 1n), i0, Z.ff2(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2)))
  +u1 = Z.ff3(len, t, Z.n((M.E0(len, t, s) + 1 : U32)), M.E1(len, t, s), Z.fld_t(len, t, d, (M.E0(len, t, s) + 1 : U32), hok, b1, h2))
  +t1 = Z.tabget(len, t, d, M.E1(len, t, s), 9, hok, u1, h3)
  +i1 = Z.nx1(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +b2 = Z.nx2(len, M.E1(len, t, s), Z.nxt(len, t, d, M.E1(len, t, s), hok, u1))
  +f2 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff1(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +l2 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E2(len, t, s))) == True{} : Bool}, Z.n((M.E1(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E1(len, t, s)), 1n), i1, Z.ff2(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4)))
  +u2 = Z.ff3(len, t, Z.n((M.E1(len, t, s) + 1 : U32)), M.E2(len, t, s), Z.fld_t(len, t, d, (M.E1(len, t, s) + 1 : U32), hok, b2, h4))
  +t2 = Z.tabget(len, t, d, M.E2(len, t, s), 9, hok, u2, h5)
  +i2 = Z.nx1(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +b3 = Z.nx2(len, M.E2(len, t, s), Z.nxt(len, t, d, M.E2(len, t, s), hok, u2))
  +f3 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff1(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +l3 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E3(len, t, s))) == True{} : Bool}, Z.n((M.E2(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E2(len, t, s)), 1n), i2, Z.ff2(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6)))
  +u3 = Z.ff3(len, t, Z.n((M.E2(len, t, s) + 1 : U32)), M.E3(len, t, s), Z.fld_t(len, t, d, (M.E2(len, t, s) + 1 : U32), hok, b3, h6))
  +t3 = Z.tabget(len, t, d, M.E3(len, t, s), 9, hok, u3, h7)
  +i3 = Z.nx1(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +b4 = Z.nx2(len, M.E3(len, t, s), Z.nxt(len, t, d, M.E3(len, t, s), hok, u3))
  +f4 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff1(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +l4 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E4(len, t, s))) == True{} : Bool}, Z.n((M.E3(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E3(len, t, s)), 1n), i3, Z.ff2(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8)))
  +u4 = Z.ff3(len, t, Z.n((M.E3(len, t, s) + 1 : U32)), M.E4(len, t, s), Z.fld_t(len, t, d, (M.E3(len, t, s) + 1 : U32), hok, b4, h8))
  +t4 = Z.tabget(len, t, d, M.E4(len, t, s), 9, hok, u4, h9)
  +i4 = Z.nx1(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +b5 = Z.nx2(len, M.E4(len, t, s), Z.nxt(len, t, d, M.E4(len, t, s), hok, u4))
  +f5 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff1(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +l5 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E5(len, t, s))) == True{} : Bool}, Z.n((M.E4(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E4(len, t, s)), 1n), i4, Z.ff2(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10)))
  +u5 = Z.ff3(len, t, Z.n((M.E4(len, t, s) + 1 : U32)), M.E5(len, t, s), Z.fld_t(len, t, d, (M.E4(len, t, s) + 1 : U32), hok, b5, h10))
  +t5 = Z.tabget(len, t, d, M.E5(len, t, s), 9, hok, u5, h11)
  +i5 = Z.nx1(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +b6 = Z.nx2(len, M.E5(len, t, s), Z.nxt(len, t, d, M.E5(len, t, s), hok, u5))
  +f6 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff1(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +l6 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E6(len, t, s))) == True{} : Bool}, Z.n((M.E5(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E5(len, t, s)), 1n), i5, Z.ff2(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12)))
  +u6 = Z.ff3(len, t, Z.n((M.E5(len, t, s) + 1 : U32)), M.E6(len, t, s), Z.fld_t(len, t, d, (M.E5(len, t, s) + 1 : U32), hok, b6, h12))
  +t6 = Z.tabget(len, t, d, M.E6(len, t, s), 9, hok, u6, h13)
  +i6 = Z.nx1(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +b7 = Z.nx2(len, M.E6(len, t, s), Z.nxt(len, t, d, M.E6(len, t, s), hok, u6))
  +f7 = AB.subst(Nat, z => {D.first2(Z.X(len, t), z, Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff1(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +l7 = AB.subst(Nat, z => {Nat.is_le(z, Z.n(M.E7(len, t, s))) == True{} : Bool}, Z.n((M.E6(len, t, s) + 1 : U32)), Nat.add(Z.n(M.E6(len, t, s)), 1n), i6, Z.ff2(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14)))
  +u7 = Z.ff3(len, t, Z.n((M.E6(len, t, s) + 1 : U32)), M.E7(len, t, s), Z.fld_t(len, t, d, (M.E6(len, t, s) + 1 : U32), hok, b7, h14))
  +i7 = Z.nx1(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  +b8 = Z.nx2(len, M.E7(len, t, s), Z.nxt(len, t, d, M.E7(len, t, s), hok, u7))
  l1
