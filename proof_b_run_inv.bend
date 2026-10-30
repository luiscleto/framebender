import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_run_lem.bend as LM
import ./proof_b_rundefs.bend as RD
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The run area's invariant (proof_b_rundefs.bend) taken apart and built.

# The parts, as a record of proofs.
def Parts(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool) -> Type:
  {D.ok(C.BT(obl, obt), RD.tdepth(obt)) == True{} : Bool}
  & ({U32.is_le(obl, 1073741824) == True{} : Bool}
  & ({D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) == True{} : Bool}
  & ({String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) == True{} : Bool}
  & ({Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) == True{} : Bool}
  & ({Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) == True{} : Bool}
  & ({RD.keys_le(f, tl) == True{} : Bool}
  & ({RD.keys_le(b, tl) == True{} : Bool}
  & ({E.is_bytes(h) == True{} : Bool}
  & ({RD.pre(i, obl, f, b, x, ns) == True{} : Bool}
  & {Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)) == True{} : Bool})))))))))

def inv_mk(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  %Equal.sym(Bool, D.ok(C.BT(obl, obt), RD.tdepth(obt)), True{}, x1) : {Bool.and(_, U32.is_le(obl, 1073741824) && (D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) && (String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) && (Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) && (Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) && (RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))))))))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(obl, 1073741824), True{}, x2) : {Bool.and(_, D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) && (String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) && (Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) && (Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) && (RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)))))))))) == True{} : Bool}
  %Equal.sym(Bool, D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)), True{}, x3) : {Bool.and(_, String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) && (Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) && (Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) && (RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))))))))) == True{} : Bool}
  %Equal.sym(Bool, String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")), True{}, x4) : {Bool.and(_, Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) && (Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) && (RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)))))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))), True{}, x5) : {Bool.and(_, Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) && (RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))), True{}, x6) : {Bool.and(_, RD.keys_le(f, tl) && (RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)))))) == True{} : Bool}
  %Equal.sym(Bool, RD.keys_le(f, tl), True{}, x7) : {Bool.and(_, RD.keys_le(b, tl) && (E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))))) == True{} : Bool}
  %Equal.sym(Bool, RD.keys_le(b, tl), True{}, x8) : {Bool.and(_, E.is_bytes(h) && (RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)))) == True{} : Bool}
  %Equal.sym(Bool, E.is_bytes(h), True{}, x9) : {Bool.and(_, RD.pre(i, obl, f, b, x, ns) && Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))) == True{} : Bool}
  %Equal.sym(Bool, RD.pre(i, obl, f, b, x, ns), True{}, x10) : {Bool.and(_, Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))) == True{} : Bool}
  x11

def inv_parts(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x):
  +a1 = D.ok(C.BT(obl, obt), RD.tdepth(obt))
  +a2 = U32.is_le(obl, 1073741824)
  +a3 = D.ok(C.BT(cbl, cbt), RD.tdepth(cbt))
  +a4 = String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, ""))
  +a5 = Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl)))
  +a6 = Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b))))
  +a7 = RD.keys_le(f, tl)
  +a8 = RD.keys_le(b, tl)
  +a9 = E.is_bytes(h)
  +a10 = RD.pre(i, obl, f, b, x, ns)
  +a11 = Nat.is_le(U32.to_nat(ow), U32.to_nat(obl))
  +r1 = LM.andr(a1, a2 && (a3 && (a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11)))))))), hi)
  +r2 = LM.andr(a2, a3 && (a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11))))))), r1)
  +r3 = LM.andr(a3, a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11)))))), r2)
  +r4 = LM.andr(a4, a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11))))), r3)
  +r5 = LM.andr(a5, a6 && (a7 && (a8 && (a9 && (a10 && a11)))), r4)
  +r6 = LM.andr(a6, a7 && (a8 && (a9 && (a10 && a11))), r5)
  +r7 = LM.andr(a7, a8 && (a9 && (a10 && a11)), r6)
  +r8 = LM.andr(a8, a9 && (a10 && a11), r7)
  +r9 = LM.andr(a9, a10 && a11, r8)
  (LM.andl(a1, a2 && (a3 && (a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11)))))))), hi), (LM.andl(a2, a3 && (a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11))))))), r1), (LM.andl(a3, a4 && (a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11)))))), r2), (LM.andl(a4, a5 && (a6 && (a7 && (a8 && (a9 && (a10 && a11))))), r3), (LM.andl(a5, a6 && (a7 && (a8 && (a9 && (a10 && a11)))), r4), (LM.andl(a6, a7 && (a8 && (a9 && (a10 && a11))), r5), (LM.andl(a7, a8 && (a9 && (a10 && a11)), r6), (LM.andl(a8, a9 && (a10 && a11), r7), (LM.andl(a9, a10 && a11, r8), (LM.andl(a10, a11, r9), LM.andr(a10, a11, r9)))))))))))

# The parts of the invariant, one at a time.
def pp1(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {D.ok(C.BT(obl, obt), RD.tdepth(obt)) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x1

def pr1(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {D.ok(C.BT(obl, obt), RD.tdepth(obt)) == True{} : Bool}:
  pp1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp2(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {U32.is_le(obl, 1073741824) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x2

def pr2(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {U32.is_le(obl, 1073741824) == True{} : Bool}:
  pp2(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp3(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x3

def pr3(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) == True{} : Bool}:
  pp3(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp4(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x4

def pr4(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) == True{} : Bool}:
  pp4(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp5(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x5

def pr5(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) == True{} : Bool}:
  pp5(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp6(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x6

def pr6(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {Bool.or(x, Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)))) == True{} : Bool}:
  pp6(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp7(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {RD.keys_le(f, tl) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x7

def pr7(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {RD.keys_le(f, tl) == True{} : Bool}:
  pp7(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp8(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {RD.keys_le(b, tl) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x8

def pr8(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {RD.keys_le(b, tl) == True{} : Bool}:
  pp8(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp9(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {E.is_bytes(h) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x9

def pr9(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {E.is_bytes(h) == True{} : Bool}:
  pp9(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp10(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {RD.pre(i, obl, f, b, x, ns) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x10

def pr10(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {RD.pre(i, obl, f, b, x, ns) == True{} : Bool}:
  pp10(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

def pp11(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x11

def pr11(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)) == True{} : Bool}:
  pp11(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))

# The invariant with another held header (of bytes).
def parts_h(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +h2: String,
  q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x), hb: {E.is_bytes(h2) == True{} : Bool}) -> Parts(i, h2, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x):
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (hb, (x10, x11))))))))))

def parts_hb(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x)) -> {E.is_bytes(h) == True{} : Bool}:
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  x9

# The parts with ob's tree replaced (same length).
def parts_ob(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +obt2: AT.Tree<U32>,
  q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x), h1: {D.ok(C.BT(obl, obt2), RD.tdepth(obt2)) == True{} : Bool}) -> Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt2, ow, ns, x):
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  (h1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, x11))))))))))

# The parts with the notes handed out (pre given again).
def parts_ns(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  q: Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x), h10: {RD.pre(i, obl, f, b, x, Nil{}) == True{} : Bool}) -> Parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, Nil{}, x):
  (x1, q1) = q
  (x2, q2) = q1
  (x3, q3) = q2
  (x4, q4) = q3
  (x5, q5) = q4
  (x6, q6) = q5
  (x7, q7) = q6
  (x8, q8) = q7
  (x9, q9) = q8
  (x10, x11) = q9
  (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (h10, x11))))))))))


# A text and a text appended: bytes when both are.
law bytes_app:
  for +a: String
  for +b: String
  for +ha: {E.is_bytes(a) == True{} : Bool}
  for +hb: {E.is_bytes(b) == True{} : Bool}
  {E.is_bytes(String.append(a, b)) == True{} : Bool}

def bytes_app(a, b, ha, hb):
  match a:
    case SNil{}:
      hb
    case SCon{Chr{+x}, +t}:
      LM.and_mk(U32.is_lt(x, 256), E.is_bytes(String.append(t, b)), LM.andl(U32.is_lt(x, 256), E.is_bytes(t), ha),
        bytes_app(t, b, LM.andr(U32.is_lt(x, 256), E.is_bytes(t), ha), hb))

# Texts that are bytes
# ====================

law chars_bytes:
  for +xs: List<&2, U32>
  for +h: {D.all_bytes(xs) == True{} : Bool}
  {E.is_bytes(NR.chars(xs)) == True{} : Bool}

def chars_bytes(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LM.and_mk(U32.is_lt(x, 256), E.is_bytes(NR.chars(t)), LM.andl(U32.is_lt(x, 256), D.all_bytes(t), h),
        chars_bytes(t, LM.andr(U32.is_lt(x, 256), D.all_bytes(t), h)))

law take_bytes:
  for +s: String
  for +n: Nat
  for +h: {E.is_bytes(s) == True{} : Bool}
  {E.is_bytes(String.take(s, n)) == True{} : Bool}

def take_bytes(s, n, h):
  match s n:
    case SNil{} _:
      {==}
    case SCon{Chr{+x}, +t} 0n:
      {==}
    case SCon{Chr{+x}, +t} 1n+m:
      LM.and_mk(U32.is_lt(x, 256), E.is_bytes(String.take(t, m)), LM.andl(U32.is_lt(x, 256), E.is_bytes(t), h),
        take_bytes(t, m, LM.andr(U32.is_lt(x, 256), E.is_bytes(t), h)))

law drop_bytes:
  for +s: String
  for +n: Nat
  for +h: {E.is_bytes(s) == True{} : Bool}
  {E.is_bytes(String.drop(s, n)) == True{} : Bool}

def drop_bytes(s, n, h):
  match s n:
    case SNil{} _:
      {==}
    case SCon{Chr{+x}, +t} 0n:
      h
    case SCon{Chr{+x}, +t} 1n+m:
      drop_bytes(t, m, LM.andr(U32.is_lt(x, 256), E.is_bytes(t), h))

law items_bytes:
  for +cs: List<&2, NR.Ck>
  for +chrom: String
  for +t: String
  for +h: {E.is_bytes(t) == True{} : Bool}
  {P.items_bytes(NR.spec.items(cs, chrom, t)) == True{} : Bool}

def items_bytes(cs, chrom, t, h):
  match cs:
    case Nil{}:
      {==}
    case Con{NR.Ck{+k, +ip, +ln, +ps, +n}, +rest}:
      +m = U32.to_nat(n)
      LM.and_mk(E.is_bytes(String.take(t, m)), P.items_bytes(NR.spec.items(rest, chrom, String.drop(t, m))), take_bytes(t, m, h),
        items_bytes(rest, chrom, String.drop(t, m), drop_bytes(t, m, h)))

# specRun as a function of ob's text.
def SRT(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +k: R.Cnt, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +t: String) -> R.RunSt:
  +chrom = Maybe.default(&2, String, c, "")
  R.RunSt{n, i, h, c, e, NR.spec.last(l, chrom), NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, String.drop(t, U32.to_nat(ow))), k, String.take(t, U32.to_nat(ow)), List.reverse(&2, B.Note, ns), x}

law or_true:
  for +x: Bool
  {Bool.or(x, True{}) == True{} : Bool}

def or_true(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law le0_eq:
  for +a: Nat
  for +h: {Nat.is_le(a, 0n) == True{} : Bool}
  {a == 0n : Nat}

def le0_eq(a, h):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, AB.false_ne_true(h))

# pre after a step that empties the notes and keeps ob no longer.
def pre_take(+i: Bool, +obl: U32, +l2: U32, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +x: Bool, +ns: List<&2, B.Note>,
  +h: {RD.pre(i, obl, f, b, x, ns) == True{} : Bool},
  +hle: {Nat.is_le(U32.to_nat(l2), U32.to_nat(obl)) == True{} : Bool}) ->
  {RD.pre(i, l2, f, b, x, Nil{}) == True{} : Bool}:
  match i:
    case True{}:
      {==}
    case False{}:
      +R = RD.is_nil(f) && (RD.is_nil(b) && (x || RD.no_notes(ns)))
      +hz = LM.andl(U32.is_zero(obl), R, h)
      +hr = LM.andr(U32.is_zero(obl), R, h)
      +hf = LM.andl(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(ns)), hr)
      +hb = LM.andl(RD.is_nil(b), x || RD.no_notes(ns), LM.andr(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(ns)), hr))
      +e0 = N.eq_sound(U32.to_nat(obl), 0n, Equal.trans(Bool, Nat.is_eq(U32.to_nat(obl), 0n), U32.is_zero(obl), True{}, Equal.sym(Bool, U32.is_zero(obl), Nat.is_eq(U32.to_nat(obl), 0n), U.is_zero_to_nat(obl)), hz))
      +e2 = le0_eq(U32.to_nat(l2), AB.subst(Nat, y => {Nat.is_le(U32.to_nat(l2), y) == True{} : Bool}, U32.to_nat(obl), 0n, e0, hle))
      +hz2 = Equal.trans(Bool, U32.is_zero(l2), Nat.is_eq(U32.to_nat(l2), 0n), True{}, U.is_zero_to_nat(l2),
        AB.subst(Nat, y => {Nat.is_eq(y, 0n) == True{} : Bool}, 0n, U32.to_nat(l2), Equal.sym(Nat, U32.to_nat(l2), 0n, e2), {==}))
      LM.and_mk(U32.is_zero(l2), RD.is_nil(f) && (RD.is_nil(b) && (x || RD.no_notes(Nil{}))), hz2,
        LM.and_mk(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(Nil{})), hf, LM.and_mk(RD.is_nil(b), x || RD.no_notes(Nil{}), hb, or_true(x))))

law notes_nil:
  for +ns: List<&2, B.Note>
  for +h: {RD.no_notes(ns) == True{} : Bool}
  {ns == Nil{} : List<&2, B.Note>}

def notes_nil(ns, h):
  match ns:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Empty.absurd({Con{y, t} == Nil{} : List<&2, B.Note>}, AB.false_ne_true(h))

law or_f:
  for +x: Bool
  for +y: Bool
  for +hx: {x == False{} : Bool}
  for +h: {Bool.or(x, y) == True{} : Bool}
  {y == True{} : Bool}

def or_f(x, y, hx, h):
  AB.subst(Bool, z => {Bool.or(z, y) == True{} : Bool}, x, False{}, hx, h)

law or_r:
  for +x: Bool
  for +y: Bool
  for +h: {y == True{} : Bool}
  {Bool.or(x, y) == True{} : Bool}

def or_r(x, y, h):
  match x:
    case True{}:
      {==}
    case False{}:
      h
