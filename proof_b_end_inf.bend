import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_fx.bend as FX
import ./proof_b_cut_str.bend as S
import ./proof_b_cut_ne2.bend as NE2
import ./proof_b_cut_ne.bend as E
import ./proof_b_alleles_loop.bend as LP
import ./proof_c_pre_str.bend as T
import ./proof_c_pre_lp.bend as G
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-bytes@0.1.0.0/proof_list.bend as PL
import lawful-bytes@0.1.0.0/proof_shift.bend as PSh
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# INFO as the String path's full field split has it (B.Rec.fields, field 7)
# is the text of INFO's bytes, whatever INFO holds: proof_c_pre_inf.bend's
# chain (itself phase B's pass_fields chain) without its no-END hypothesis,
# derived from it by data/tmp/fb-end/mk_inf.py (the fb-end agent's script).

def INF(+len: U32, +t: AT.Tree<U32>, +s: U32) -> String:
  S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s)))

def IG(+len: U32, +t: AT.Tree<U32>, +s: U32, +body: String) -> Type:
  {B.Rec.field(B.Rec.fields(body), 7n) == INF(len, t, s) : String}

def IFG(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> Type:
  IG(len, t, s, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(lf)))))

# A cut at a tab: the split is the field, then the split of the rest.
def spl1(+s0: String, +f: String, +r: String, +hc: {J.cut(s0) == J.Cut{f, r, True{}} : J.Cut}) ->
  {String.split(s0, '\t') == f <> String.split(r, '\t') : List<&2, String>}:
  Equal.trans(List<&2, String>, String.split(s0, '\t'), J.Cut.f(J.cut(s0)) <> T.ctail(J.cut(s0)), f <> String.split(r, '\t'), T.split_ft(s0),
    Equal.cong(J.Cut, List<&2, String>, c => J.Cut.f(c) <> T.ctail(c), J.cut(s0), J.Cut{f, r, True{}}, hc))

# Bytes a .. b-1 before the first tab or LF from a0: J.cut keeps them all.
def notab(m: Nat, +xs: List<&2, U32>, +a0: Nat, +a: Nat, +b: Nat, +L: Nat,
  +hff: {D.first2(xs, a0, L, 9, 10) == b : Nat}, +h0: {Nat.is_le(a0, a) == True{} : Bool},
  +hm: {Nat.add(a, m) == b : Nat}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {J.Cut.f(J.cut(S.fld(xs, a, b))) == S.fld(xs, a, b) : String}:
  match m:
    case 0n:
      +e = Equal.trans(Nat, a, Nat.add(a, 0n), b, Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)), hm)
      %Equal.sym(Nat, a, b, e) : {J.Cut.f(J.cut(S.fld(xs, _, b))) == S.fld(xs, _, b) : String}
      %Equal.sym(String, S.fld(xs, b, b), SNil{}, E.fld_end(xs, b)) : {J.Cut.f(J.cut(_)) == _ : String}
      {==}
    case 1n+(+q):
      +hle = AB.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, b, Nat.add(a, 1n+q), Equal.sym(Nat, Nat.add(a, 1n+q), b, hm), N.le_refl(b))
      +hp = G.lt_of(a, q, b, hle)
      +hal = N.lt_le_trans(a, b, List.length(&2, U32, xs), hp, hb)
      +x = E.XV(xs, a)
      +F1 = S.fld(xs, Nat.add(a, 1n), b)
      +h9 = Z.no9(xs, a0, L, b, a, hff, h0, hp)
      +hx9 = Equal.trans(Bool, U32.is_eq(x, 9), D.has(xs, a, 9), False{}, Equal.sym(Bool, D.has(xs, a, 9), U32.is_eq(x, 9), Z.has_get(xs, a, x, 9, E.get_xv(xs, a, hal))), h9)
      +hm2 = Equal.trans(Nat, Nat.add(Nat.add(a, 1n), q), Nat.add(a, Nat.add(1n, q)), b, N.add_assoc(a, 1n, q), hm)
      %Equal.sym(String, S.fld(xs, a, b), SCon{Chr{x}, F1}, E.fld_cons(xs, a, b, hp, hb)) : {J.Cut.f(J.cut(_)) == _ : String}
      %Equal.sym(String, J.Cut.f(J.cut(SCon{Chr{x}, F1})), SCon{Chr{x}, J.Cut.f(J.cut(F1))}, T.cutf_cons(Chr{x}, F1, hx9)) : {_ == SCon{Chr{x}, F1} : String}
      %Equal.sym(String, J.Cut.f(J.cut(F1)), F1, notab(q, xs, a0, Nat.add(a, 1n), b, L, hff, N.le_trans(a0, a, Nat.add(a, 1n), h0, N.le_add_r(a, 1n)), hm2, hb)) :
        {SCon{Chr{x}, _} == SCon{Chr{x}, F1} : String}
      {==}

def cr_k(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +bd: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hc: {Nat.is_lt(Z.n(M.E7(len, t, s)), bd) == c : Bool},
  +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat},
  +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool},
  +hBX: {Nat.is_le(bd, List.length(&2, U32, Z.X(len, t))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), bd)) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool},
  +hE7B: {Nat.is_le(Z.n(M.E7(len, t, s)), bd) == True{} : Bool}) ->
  {J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) == INF(len, t, s) : String}:
  match c:
    case True{}:
      +X = Z.X(len, t)
      +a6 = Nat.add(Z.n(M.E6(len, t, s)), 1n)
      +e7 = Z.n(M.E7(len, t, s))
      +has7 = AB.subst(Bool, z => {(Bool.not(z) || D.has(X, e7, 9)) == True{} : Bool}, Nat.is_lt(e7, bd), True{}, hc, hend7)
      +t7 = LP.has_get(X, e7, 9, has7)
      Equal.cong(J.Cut, String, z => J.Cut.f(z), J.cut(S.fld(X, a6, bd)), J.Cut{S.fld(X, a6, e7), S.fld(X, Nat.add(e7, 1n), bd), True{}},
        S.cut_fld(X, a6, e7, bd, l7, hc, Z.first9(X, a6, e7, bd, Z.n(len), hBX, f7, l7, hc, t7), t7))
    case False{}:
      +X = Z.X(len, t)
      +a6 = Nat.add(Z.n(M.E6(len, t, s)), 1n)
      +e7 = Z.n(M.E7(len, t, s))
      +e = Z.le_antisym(e7, bd, hE7B, N.not_lt_le(e7, bd, hc))
      %e : {J.Cut.f(J.cut(S.fld(X, a6, _))) == INF(len, t, s) : String}
      notab(Nat.sub(e7, a6), X, a6, a6, e7, Z.n(len), f7, N.le_refl(a6), N.le_sub_add(a6, e7, l7), N.le_trans(e7, bd, List.length(&2, U32, X), hE7B, hBX))

def cutR(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +bd: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat},
  +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool},
  +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool},
  +hBX: {Nat.is_le(bd, List.length(&2, U32, Z.X(len, t))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), bd)) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool},
  +hE7B: {Nat.is_le(Z.n(M.E7(len, t, s)), bd) == True{} : Bool}) ->
  {J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) == INF(len, t, s) : String}:
  cr_k(Nat.is_lt(Z.n(M.E7(len, t, s)), bd), len, t, d, s, bd, hok, {==}, f7, l7, hBX, hend7, hE7B)

def ifields(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +bd: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hE7B: {Nat.is_le(Z.n(M.E7(len, t, s)), bd) == True{} : Bool}, +hBX: {Nat.is_le(bd, List.length(&2, U32, Z.X(len, t))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), bd)) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool}) ->
  IG(len, t, s, S.fld(Z.X(len, t), Z.n(s), bd)):
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
  +hcr = cutR(len, t, d, s, bd, hok, f7, l7, u7, hBX, hend7, hE7B)
  +L0 = Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Z.n(s), bd), '\t'), S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))))))), spl1(S.fld(Z.X(len, t), Z.n(s), bd), S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), c0), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))))))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))))))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), c1), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), c2), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), c3), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), c4), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), c5), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))), Equal.trans(List<&2, String>, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd), '\t'), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))), spl1(S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), bd), S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))), S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd), c6), Equal.cong(List<&2, String>, List<&2, String>, z => S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> z, String.split(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd), '\t'), J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))), T.split_ft(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))))))))))))))))
  Equal.trans(String, B.Rec.field(B.Rec.fields(S.fld(Z.X(len, t), Z.n(s), bd)), 7n), J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))), INF(len, t, s),
    Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 7n), String.split(S.fld(Z.X(len, t), Z.n(s), bd), '\t'), S.fld(Z.X(len, t), Z.n(s), Z.n(M.E0(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) <> (S.fld(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) <> (J.Cut.f(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd))) <> T.ctail(J.cut(S.fld(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), bd)))))))))), L0), hcr)

def ifd_cr(+cr: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hcr: {U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13) == cr : Bool},
  +hsl: {Nat.is_lt(Z.n(s), Z.n(M.LF1(len, t, s))) == True{} : Bool}, +hll: {Nat.is_lt(Z.n(M.LF1(len, t, s)), Z.n(len)) == True{} : Bool},
  +h7l: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s))) == True{} : Bool},
  +hend7: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)))) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool},
  +hend8: {(Bool.not(Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)))) || D.has(Z.X(len, t), Z.n(M.E7(len, t, s)), 9)) == True{} : Bool}) -> IFG(len, t, s, M.LF1(len, t, s)):
  match cr:
    case False{}:
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s))))), S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)), U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13)),
        FX.BE(len, t, d, Z.n(s), M.LF1(len, t, s), hok, hsl, hll)) : IG(len, t, s, _)
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13), False{}, hcr) :
        IG(len, t, s, S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), Z.n((M.LF1(len, t, s) - 1 : U32)), _))
      ifields(len, t, d, s, Z.n(M.LF1(len, t, s)), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, N.lt_to_le(Z.n(M.E7(len, t, s)), Z.n(M.LF1(len, t, s)), h7l),
        Z.le_len(len, t, d, Z.n(M.LF1(len, t, s)), hok, N.lt_to_le(Z.n(M.LF1(len, t, s)), Z.n(len), hll)), hend7)
    case True{}:
      +c = Z.n((M.LF1(len, t, s) - 1 : U32))
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s))))), S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), c, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13)),
        FX.BE(len, t, d, Z.n(s), M.LF1(len, t, s), hok, hsl, hll)) : IG(len, t, s, _)
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (M.LF1(len, t, s) - 1 : U32)), 13), True{}, hcr) :
        IG(len, t, s, S.BDY(Z.X(len, t), Z.n(s), Z.n(M.LF1(len, t, s)), c, _))
      r = FX.lst(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll)
      +hcX = N.le_trans(c, Z.n(M.LF1(len, t, s)), List.length(&2, U32, Z.X(len, t)), N.le_trans(c, Nat.add(c, 1n), Z.n(M.LF1(len, t, s)), N.le_add_r(c, 1n),
        AB.subst(Nat, z => {Nat.is_le(Nat.add(c, 1n), z) == True{} : Bool}, Nat.add(c, 1n), Z.n(M.LF1(len, t, s)), FX.lst1(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll, FX.lst(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll)), N.le_refl(Nat.add(c, 1n)))),
        Z.le_len(len, t, d, Z.n(M.LF1(len, t, s)), hok, N.lt_to_le(Z.n(M.LF1(len, t, s)), Z.n(len), hll)))
      ifields(len, t, d, s, c, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, FX.lst2(len, t, d, Z.n(M.E7(len, t, s)), M.LF1(len, t, s), hok, h7l, hll, r), hcX, hend8)


def ifd_q(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +q: Bool, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +f0: {D.first2(Z.X(len, t), Z.n(s), Z.n(len), 9, 10) == Z.n(M.E0(len, t, s)) : Nat}, +l0: {Nat.is_le(Z.n(s), Z.n(M.E0(len, t, s))) == True{} : Bool}, +u0: {Nat.is_lt(Z.n(M.E0(len, t, s)), Z.n(len)) == True{} : Bool}, +f1: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E1(len, t, s)) : Nat}, +l1: {Nat.is_le(Nat.add(Z.n(M.E0(len, t, s)), 1n), Z.n(M.E1(len, t, s))) == True{} : Bool}, +u1: {Nat.is_lt(Z.n(M.E1(len, t, s)), Z.n(len)) == True{} : Bool}, +f2: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E2(len, t, s)) : Nat}, +l2: {Nat.is_le(Nat.add(Z.n(M.E1(len, t, s)), 1n), Z.n(M.E2(len, t, s))) == True{} : Bool}, +u2: {Nat.is_lt(Z.n(M.E2(len, t, s)), Z.n(len)) == True{} : Bool}, +f3: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E3(len, t, s)) : Nat}, +l3: {Nat.is_le(Nat.add(Z.n(M.E2(len, t, s)), 1n), Z.n(M.E3(len, t, s))) == True{} : Bool}, +u3: {Nat.is_lt(Z.n(M.E3(len, t, s)), Z.n(len)) == True{} : Bool}, +f4: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E4(len, t, s)) : Nat}, +l4: {Nat.is_le(Nat.add(Z.n(M.E3(len, t, s)), 1n), Z.n(M.E4(len, t, s))) == True{} : Bool}, +u4: {Nat.is_lt(Z.n(M.E4(len, t, s)), Z.n(len)) == True{} : Bool}, +f5: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E5(len, t, s)) : Nat}, +l5: {Nat.is_le(Nat.add(Z.n(M.E4(len, t, s)), 1n), Z.n(M.E5(len, t, s))) == True{} : Bool}, +u5: {Nat.is_lt(Z.n(M.E5(len, t, s)), Z.n(len)) == True{} : Bool}, +f6: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E6(len, t, s)) : Nat}, +l6: {Nat.is_le(Nat.add(Z.n(M.E5(len, t, s)), 1n), Z.n(M.E6(len, t, s))) == True{} : Bool}, +u6: {Nat.is_lt(Z.n(M.E6(len, t, s)), Z.n(len)) == True{} : Bool}, +f7: {D.first2(Z.X(len, t), Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(len), 9, 10) == Z.n(M.E7(len, t, s)) : Nat}, +l7: {Nat.is_le(Nat.add(Z.n(M.E6(len, t, s)), 1n), Z.n(M.E7(len, t, s))) == True{} : Bool}, +u7: {Nat.is_lt(Z.n(M.E7(len, t, s)), Z.n(len)) == True{} : Bool}, +t0: {List.get(&2, U32, Z.X(len, t), Z.n(M.E0(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t1: {List.get(&2, U32, Z.X(len, t), Z.n(M.E1(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t2: {List.get(&2, U32, Z.X(len, t), Z.n(M.E2(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t3: {List.get(&2, U32, Z.X(len, t), Z.n(M.E3(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t4: {List.get(&2, U32, Z.X(len, t), Z.n(M.E4(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t5: {List.get(&2, U32, Z.X(len, t), Z.n(M.E5(len, t, s))) == Some{9} : Maybe<&2, U32>}, +t6: {List.get(&2, U32, Z.X(len, t), Z.n(M.E6(len, t, s))) == Some{9} : Maybe<&2, U32>}, +i7: {Z.n((M.E7(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E7(len, t, s)), 1n) : Nat}, +b8: {U32.is_le((M.E7(len, t, s) + 1 : U32), len) == True{} : Bool},
  +i6: {Z.n((M.E6(len, t, s) + 1 : U32)) == Nat.add(Z.n(M.E6(len, t, s)), 1n) : Nat},
  +hq: {U32.is_eq(C.AT(len, t, M.E7(len, t, s)), 9) == q : Bool}, +hl: {V.LPm(len, t, s, q) == False{} : Bool},
  +hcrt: {M.CRT(len, t, M.E7(len, t, s), V.LFm(len, t, s, q)) == True{} : Bool}) ->
  IFG(len, t, s, V.LFm(len, t, s, q)):
  match q:
    case False{}:
      +e7 = M.E7(len, t, s)
      +hsl = N.le_lt_trans(Z.n(s), Z.n(M.E0(len, t, s)), Z.n(M.E7(len, t, s)), l0, N.lt_trans(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E0(len, t, s)), Z.n(M.E1(len, t, s)), l1), N.lt_trans(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E1(len, t, s)), Z.n(M.E2(len, t, s)), l2), N.lt_trans(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E2(len, t, s)), Z.n(M.E3(len, t, s)), l3), N.lt_trans(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E3(len, t, s)), Z.n(M.E4(len, t, s)), l4), N.lt_trans(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E4(len, t, s)), Z.n(M.E5(len, t, s)), l5), N.lt_trans(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), Z.succ_lt(Z.n(M.E5(len, t, s)), Z.n(M.E6(len, t, s)), l6), Z.succ_lt(Z.n(M.E6(len, t, s)), Z.n(M.E7(len, t, s)), l7))))))))
      +hx = AB.subst(Bool, z => {Bool.not(z && U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13)) == True{} : Bool}, U32.is_eq(e7, e7), True{}, PL.pl_u32_eq_refl(e7), hcrt)
      %Equal.sym(String, B.Line.body(Norm.line(S.fld(Z.X(len, t), Z.n(s), Z.n(e7)))), S.BDY(Z.X(len, t), Z.n(s), Z.n(e7), Z.n((e7 - 1 : U32)), U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13)),
        FX.BE(len, t, d, Z.n(s), e7, hok, hsl, u7)) : IG(len, t, s, _)
      %Equal.sym(Bool, U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13), False{}, FX.not_true(U32.is_eq(C.AT(len, t, (e7 - 1 : U32)), 13), hx)) :
        IG(len, t, s, S.BDY(Z.X(len, t), Z.n(s), Z.n(e7), Z.n((e7 - 1 : U32)), _))
      +hend7 = AB.subst(Bool, z => {(Bool.not(z) || D.has(Z.X(len, t), Z.n(e7), 9)) == True{} : Bool}, False{}, Nat.is_lt(Z.n(e7), Z.n(e7)), Equal.sym(Bool, Nat.is_lt(Z.n(e7), Z.n(e7)), False{}, N.lt_irrefl(Z.n(e7))), {==})
      ifields(len, t, d, s, Z.n(e7), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, N.le_refl(Z.n(e7)), Z.le_len(len, t, d, Z.n(e7), hok, N.lt_to_le(Z.n(e7), Z.n(len), u7)), hend7)
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
      ifd_cr(U32.is_eq(C.AT(len, t, (lf1 - 1 : U32)), 13), len, t, d, s, hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, {==}, hsl, hll, h7l, hend7, hend8)


def ifd_core(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hs: {U32.is_le(s, len) == True{} : Bool}, +h0: {M.TP(len, t, s) == False{} : Bool}, +h1: {M.TT(len, t, s) == True{} : Bool}, +h2: {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool}, +h3: {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool}, +h4: {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool}, +h5: {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool}, +h6: {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool}, +h7: {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool}, +h8: {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool}, +h9: {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool}, +h10: {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool}, +h11: {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool}, +h12: {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool}, +h13: {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool}, +h14: {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool},
  +hl: {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool},
  +hcrt: {M.CRT(len, t, M.E7(len, t, s), V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == True{} : Bool}) ->
  IFG(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))):
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
  ifd_q(len, t, d, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)), hok, f0, l0, u0, f1, l1, u1, f2, l2, u2, f3, l3, u3, f4, l4, u4, f5, l5, u5, f6, l6, u6, f7, l7, u7, t0, t1, t2, t3, t4, t5, t6, i7, b8, i6, {==}, hl, hcrt)

