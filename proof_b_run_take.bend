import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# run_take (proof_b_run.bend): the end of a step on a pictured run.

def TakeG(+p: P.RunP, +left: U32) -> Type:
  &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> &p2: P.RunP ->
  ({NR.take(P.mkRun(p), left) == ((C.BT(ol, ot), P.RunSt.notes(P.specRun(p))), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run}
  & ({D.ok(C.BT(ol, ot), d) == True{} : Bool}
  & ({NR.chars(D.view(C.BT(ol, ot))) == P.RunSt.out(P.specRun(p)) : String}
  & ({RD.RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == P.clear(P.specRun(p)) : R.RunSt}
  & {P.RunP.ow(p2) == 0 : U32})))))

# The run take.fin builds from (its out, its rest).
def R0(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +ow: U32, +ns: List<&2, B.Note>, +x: Bool) -> NR.Run:
  NR.Run{n, i, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, x}

# ow is 0: nothing written; out is an empty buffer, ob stays.
def take_z(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +left: U32,
  +hz: {U32.is_zero(ow) == True{} : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) ->
  TakeG(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, left):
  +t0 = G.tnew(0n, 0)
  +eow = U.is_eq_true(ow, 0, hz)
  +p2 = {P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, 0, Nil{}, x} : P.RunP}
  +T = NR.chars(D.view(C.BT(obl, obt)))
  +eq0 = AB.subst(D.Bytes, z => {((z, List.reverse(&2, B.Note, ns)), P.mkRun(p2)) == ((C.BT(0, t0), List.reverse(&2, B.Note, ns)), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run},
    C.BT(0, t0), BY.empty(0n), Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), {==})
  +eq = AB.subst(Bool, z => {NR.take.fin(NR.take.if(z, ow, left, C.BT(obl, obt)), R0(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, ow, ns, x)) == ((C.BT(0, t0), List.reverse(&2, B.Note, ns)), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run},
    True{}, U32.is_zero(ow), Equal.sym(Bool, U32.is_zero(ow), True{}, hz), eq0)
  +ok0 = BF.empty_ok_td(0n, {==})
  +hout = AB.subst(U32, w => {NR.chars(D.view(C.BT(0, t0))) == String.take(T, U32.to_nat(w)) : String}, 0, ow, Equal.sym(U32, ow, 0, eow),
    Equal.sym(String, String.take(T, 0n), "", BF.str_take0(T)))
  +hinv = AB.subst(U32, w => {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, w, Nil{}, x) == True{} : Bool}, ow, 0, eow,
    PI.inv_mk(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, Nil{}, x, PI.parts_ns(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x,
      PI.inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
      PI.pre_take(i, obl, obl, f, b, x, ns, PI.pr10(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), N.le_refl(U32.to_nat(obl))))))
  +hspec = AB.subst(U32, w => {PI.SRT(n, i, h, c, e, l, f, b, k, 0, Nil{}, x, T) == P.clear(PI.SRT(n, i, h, c, e, l, f, b, k, w, ns, x, T)) : R.RunSt}, 0, ow, Equal.sym(U32, ow, 0, eow),
    %Equal.sym(String, String.take(T, 0n), "", BF.str_take0(T)) : {R.RunSt{n, i, h, c, e, NR.spec.last(l, Maybe.default(&2, String, c, "")), NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(T, 0n)), k, _, Nil{}, x} == P.clear(PI.SRT(n, i, h, c, e, l, f, b, k, 0, ns, x, T)) : R.RunSt};
    {==})
  (0, (t0, (0n, (p2, (eq, (ok0, (hout, (hinv, (hspec, {==})))))))))

def F31() -> U32:
  1073741824

# Part 5 after a take: the buffered texts are all of the new block.
def p5k(+x: Bool, +ow: U32, +obl: U32, +LS: Nat, +l2: U32,
  +hs5: {Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), LS), U32.to_nat(obl))) == True{} : Bool},
  +el2: {U32.to_nat(l2) == Nat.sub(U32.to_nat(obl), U32.to_nat(ow)) : Nat}) ->
  {Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(0), LS), U32.to_nat(l2))) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      +SB = Nat.sub(U32.to_nat(obl), U32.to_nat(ow))
      +esum = N.eq_sound(Nat.add(U32.to_nat(ow), LS), U32.to_nat(obl), hs5)
      +elsub = Equal.trans(Nat, LS, Nat.sub(Nat.add(U32.to_nat(ow), LS), U32.to_nat(ow)), SB,
        Equal.sym(Nat, Nat.sub(Nat.add(U32.to_nat(ow), LS), U32.to_nat(ow)), LS, N.sub_add_l(U32.to_nat(ow), LS)),
        Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(ow)), Nat.add(U32.to_nat(ow), LS), U32.to_nat(obl), esum))
      AB.subst(Nat, y => {Nat.is_eq(Nat.add(U32.to_nat(0), LS), y) == True{} : Bool}, SB, U32.to_nat(l2), Equal.sym(Nat, U32.to_nat(l2), SB, el2),
        AB.subst(Nat, y => {Nat.is_eq(Nat.add(U32.to_nat(0), y), SB) == True{} : Bool}, SB, LS, Equal.sym(Nat, LS, SB, elsub), N.eq_refl(SB)))

# ow > 0: the first ow bytes are handed out, the rest copied to a new block.
def take_nz.k(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +left: U32,
  +hz: {U32.is_zero(ow) == False{} : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool},
  +hwo: {Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)) == True{} : Bool},
  +eL2: {U32.to_nat((obl - ow : U32)) == Nat.sub(U32.to_nat(obl), U32.to_nat(ow)) : Nat},
  +hs5: {Bool.or(x, Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(RD.items(f, b))), U32.to_nat(obl))) == True{} : Bool},
  +hL2le: {Nat.is_le(U32.to_nat((obl - ow : U32)), U32.to_nat(obl)) == True{} : Bool},
  pb: &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(0, G.tnew(NR.depth(((obl - ow : U32) + left + 65536 : U32)), 0), obl, obt, ow, (obl - ow : U32), l2, t2)) ->
  TakeG(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, left):
  (+l2, q) = pb
  (+t2, r) = q
  (eqp, r1) = r
  (okp, r2) = r1
  (vp, lp) = r2
  +L2 = (obl - ow : U32)
  +dd = NR.depth(((obl - ow : U32) + left + 65536 : U32))
  +t0 = G.tnew(dd, 0)
  +V = D.view(C.BT(obl, obt))
  +T = NR.chars(V)
  +S = D.slice(V, U32.to_nat(ow), U32.to_nat(L2))
  +LS = RD.lens(RD.items(f, b))
  +SB = Nat.sub(U32.to_nat(obl), U32.to_nat(ow))
  +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
  +p2 = {P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, l2, t2, 0, Nil{}, x} : P.RunP}
  +e1 = AB.subst(D.Bytes & D.Bytes, z => {NR.take.fin(NR.take.k(ow, z), R0(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, ow, ns, x)) == ((C.BT(ow, obt), List.reverse(&2, B.Note, ns)), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run},
    (C.BT(l2, t2), C.BT(obl, obt)), NR.put_bytes(C.BT(0, t0), C.BT(obl, obt), ow, L2), Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(0, t0), C.BT(obl, obt), ow, L2), (C.BT(l2, t2), C.BT(obl, obt)), eqp), {==})
  +e2 = AB.subst(D.Bytes, z => {NR.take.fin(NR.take.k(ow, NR.put_bytes(z, C.BT(obl, obt), ow, L2)), R0(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, ow, ns, x)) == ((C.BT(ow, obt), List.reverse(&2, B.Note, ns)), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run},
    C.BT(0, t0), BY.empty(dd), Equal.sym(D.Bytes, BY.empty(dd), C.BT(0, t0), G.empty_eq(dd)), e1)
  +eq = AB.subst(Bool, z => {NR.take.fin(NR.take.if(z, ow, left, C.BT(obl, obt)), R0(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, ow, ns, x)) == ((C.BT(ow, obt), List.reverse(&2, B.Note, ns)), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run},
    False{}, U32.is_zero(ow), Equal.sym(Bool, U32.is_zero(ow), False{}, hz), e2)
  +hokw = O.truncate_ok_t(obl, obt, RD.tdepth(obt), ow, hok, hwo)
  +hout = Equal.trans(String, NR.chars(D.view(C.BT(ow, obt))), NR.chars(List.take(&2, U32, V, U32.to_nat(ow))), String.take(T, U32.to_nat(ow)),
    Equal.cong(List<&2, U32>, String, z => NR.chars(z), D.view(C.BT(ow, obt)), List.take(&2, U32, V, U32.to_nat(ow)), O.truncate_view_t(obl, obt, ow, hwo)),
    BF.chars_take(V, U32.to_nat(ow)))
  +el2 = Equal.trans(Nat, U32.to_nat(l2), U32.to_nat(L2), SB, lp, eL2)
  +hl2o = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(obl)) == True{} : Bool}, SB, U32.to_nat(l2), Equal.sym(Nat, U32.to_nat(l2), SB, el2), U.sub_le(U32.to_nat(obl), U32.to_nat(ow)))
  +hob = Equal.trans(Bool, Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U32.is_le(obl, F31()), True{},
    Equal.sym(Bool, U32.is_le(obl, F31()), Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U.is_le_to_nat(obl, F31())), PI.pr2(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))
  +h2 = Equal.trans(Bool, U32.is_le(l2, F31()), Nat.is_le(U32.to_nat(l2), U32.to_nat(F31())), True{}, U.is_le_to_nat(l2, F31()),
    N.le_trans(U32.to_nat(l2), U32.to_nat(obl), U32.to_nat(F31()), hl2o, hob))
  +h5 = p5k(x, ow, obl, LS, l2, hs5, el2)
  +hinv = PI.inv_mk(i, h, c, cbl, cbt, f, b, bn, tl, l2, t2, 0, Nil{}, x,
    (okp, (h2, (PI.pr3(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr4(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (h5,
    (PI.pr6(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr7(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr8(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
    (PI.pr9(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pre_take(i, obl, l2, f, b, x, ns, PI.pr10(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), hl2o), N.le_zero_l(U32.to_nat(l2)))))))))))))
  +ev = Equal.trans(List<&2, U32>, D.view(C.BT(l2, t2)), List.append(&2, U32, D.view(C.BT(0, t0)), S), List.drop(&2, U32, V, U32.to_nat(ow)), vp,
    Equal.trans(List<&2, U32>, List.append(&2, U32, D.view(C.BT(0, t0)), S), S, List.drop(&2, U32, V, U32.to_nat(ow)),
      AB.subst(List<&2, U32>, z => {List.append(&2, U32, z, S) == S : List<&2, U32>}, Nil{}, D.view(C.BT(0, t0)), Equal.sym(List<&2, U32>, D.view(C.BT(0, t0)), Nil{}, BF.view0(t0)), {==}),
      Equal.trans(List<&2, U32>, S, D.slice(V, U32.to_nat(ow), SB), List.drop(&2, U32, V, U32.to_nat(ow)),
        Equal.cong(Nat, List<&2, U32>, z => D.slice(V, U32.to_nat(ow), z), U32.to_nat(L2), SB, eL2),
        Equal.trans(List<&2, U32>, D.slice(V, U32.to_nat(ow), SB), D.slice(V, U32.to_nat(ow), Nat.sub(List.length(&2, U32, V), U32.to_nat(ow))), List.drop(&2, U32, V, U32.to_nat(ow)),
          Equal.cong(Nat, List<&2, U32>, z => D.slice(V, U32.to_nat(ow), Nat.sub(z, U32.to_nat(ow))), U32.to_nat(obl), List.length(&2, U32, V), Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(obl), O.view_size_t(obl, obt, RD.tdepth(obt), hok))),
          BF.slice_rest(V, U32.to_nat(ow))))))
  +eT2 = Equal.trans(String, NR.chars(D.view(C.BT(l2, t2))), NR.chars(List.drop(&2, U32, V, U32.to_nat(ow))), String.drop(T, U32.to_nat(ow)),
    Equal.cong(List<&2, U32>, String, z => NR.chars(z), D.view(C.BT(l2, t2)), List.drop(&2, U32, V, U32.to_nat(ow)), ev),
    BF.chars_drop(V, U32.to_nat(ow)))
  +Dt = String.drop(T, U32.to_nat(ow))
  +chrom = Maybe.default(&2, String, c, "")
  +hsa = AB.subst(String, z => {R.RunSt{n, i, h, c, e, NR.spec.last(l, chrom), NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, z), k, "", Nil{}, x} == P.clear(PI.SRT(n, i, h, c, e, l, f, b, k, ow, ns, x, T)) : R.RunSt}, Dt, String.drop(Dt, 0n),
    Equal.sym(String, String.drop(Dt, 0n), Dt, BF.str_drop0(Dt)), {==})
  +hs0 = AB.subst(String, z => {R.RunSt{n, i, h, c, e, NR.spec.last(l, chrom), NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, String.drop(Dt, 0n)), k, z, Nil{}, x} == P.clear(PI.SRT(n, i, h, c, e, l, f, b, k, ow, ns, x, T)) : R.RunSt}, "", String.take(Dt, 0n),
    Equal.sym(String, String.take(Dt, 0n), "", BF.str_take0(Dt)), hsa)
  +hspec = AB.subst(String, z => {PI.SRT(n, i, h, c, e, l, f, b, k, 0, Nil{}, x, z) == P.clear(PI.SRT(n, i, h, c, e, l, f, b, k, ow, ns, x, T)) : R.RunSt},
    Dt, NR.chars(D.view(C.BT(l2, t2))), Equal.sym(String, NR.chars(D.view(C.BT(l2, t2))), Dt, eT2), hs0)
  (ow, (obt, (RD.tdepth(obt), (p2, (eq, (hokw, (hout, (hinv, (hspec, {==})))))))))

def take_nz(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +left: U32,
  +hz: {U32.is_zero(ow) == False{} : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) ->
  TakeG(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, left):
  +LS = RD.lens(RD.items(f, b))
  +L2 = (obl - ow : U32)
  +SB = Nat.sub(U32.to_nat(obl), U32.to_nat(ow))
  +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
  +hwo = PI.pr11(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
  +hwoU = Equal.trans(Bool, U32.is_le(ow, obl), Nat.is_le(U32.to_nat(ow), U32.to_nat(obl)), True{}, U.is_le_to_nat(ow, obl), hwo)
  +eL2 = U.to_nat_sub_le(obl, ow, hwoU)
  +hL2le = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(obl)) == True{} : Bool}, SB, U32.to_nat(L2), Equal.sym(Nat, U32.to_nat(L2), SB, eL2), U.sub_le(U32.to_nat(obl), U32.to_nat(ow)))
  +hs = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ow), y), U32.to_nat(obl)) == True{} : Bool}, SB, U32.to_nat(L2), Equal.sym(Nat, U32.to_nat(L2), SB, eL2),
    AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(obl)) == True{} : Bool}, U32.to_nat(obl), Nat.add(U32.to_nat(ow), SB), Equal.sym(Nat, Nat.add(U32.to_nat(ow), SB), U32.to_nat(obl), N.le_sub_add(U32.to_nat(ow), U32.to_nat(obl), hwo)), N.le_refl(U32.to_nat(obl))))
  +hob = Equal.trans(Bool, Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U32.is_le(obl, F31()), True{},
    Equal.sym(Bool, U32.is_le(obl, F31()), Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U.is_le_to_nat(obl, F31())), PI.pr2(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))
  +h30 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(obl), y) == True{} : Bool}, U32.to_nat(F31()), Nat.pow(2n, 30n), PL.lit_pow(30n, F31(), {==}, {==}), hob)
  +hL = NM.lt_c0(U32.to_nat(L2), Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(U32.to_nat(L2), N.le_trans(U32.to_nat(L2), U32.to_nat(obl), Nat.pow(2n, 30n), hL2le, h30)))
  +dd = NR.depth(((obl - ow : U32) + left + 65536 : U32))
  +ok0 = BF.empty_ok_td(dd, NM.depth_le(((obl - ow : U32) + left + 65536 : U32)))
  take_nz.k(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x, left, hz, hi, hwo, eL2, PI.pr5(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), hL2le,
    BF.put_bytes_t(0, G.tnew(dd, 0), obl, obt, RD.tdepth(obt), ow, L2, ok0, hok, hs, hL))

def take_c(+z: Bool, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +left: U32,
  +hz: {U32.is_zero(ow) == z : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) ->
  TakeG(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, left):
  match z:
    case True{}:
      take_z(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x, left, hz, hi)
    case False{}:
      take_nz(n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x, left, hz, hi)

def take_t(+p: P.RunP, +left: U32, +hi: {RD.RunInv(p) == True{} : Bool}) -> TakeG(p, left):
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      take_c(U32.is_zero(ow), n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x, left, {==}, hi)
