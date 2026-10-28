import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# run_head_write (proof_b_run.bend): the #CHROM line writes the header.

law slen_app:
  for +a: String
  for +b: String
  {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}

def slen_app(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %slen_app(t, b) : {1n+String.length(String.append(t, b)) == 1n+_ : Nat}
      {==}

law str_take_all:
  for +s: String
  {String.take(s, String.length(s)) == s : String}

def str_take_all(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %str_take_all(t) : {SCon{c, String.take(t, String.length(t))} == SCon{c, _} : String}
      {==}

# Three texts of at most 2^B bytes make at most 2^e for e = 2 + B.
law three:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +B: Nat
  for +e: Nat
  for +he: {Nat.add(2n, B) == e : Nat}
  for +hx: {Nat.is_le(x, Nat.pow(2n, B)) == True{} : Bool}
  for +hy: {Nat.is_le(y, Nat.pow(2n, B)) == True{} : Bool}
  for +hz: {Nat.is_le(z, Nat.pow(2n, B)) == True{} : Bool}
  {Nat.is_le(Nat.add(x, Nat.add(y, z)), Nat.pow(2n, e)) == True{} : Bool}

def three(x, y, z, B, e, he, hx, hy, hz):
  +P = Nat.pow(2n, B)
  %he : {Nat.is_le(Nat.add(x, Nat.add(y, z)), Nat.pow(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(2n, Nat.mul(2n, P)), Nat.mul(4n, P), NM.mul4(P)) : {Nat.is_le(Nat.add(x, Nat.add(y, z)), _) == True{} : Bool}
  +hyz = N.le_trans(Nat.add(y, z), Nat.add(P, z), Nat.add(P, P), N.le_add_mono_r(z, y, P, hy), N.le_add_mono_l(P, z, P, hz))
  +h1 = N.le_trans(Nat.add(x, Nat.add(y, z)), Nat.add(P, Nat.add(y, z)), Nat.add(P, Nat.add(P, P)), N.le_add_mono_r(Nat.add(y, z), x, P, hx), N.le_add_mono_l(P, Nat.add(y, z), Nat.add(P, P), hyz))
  +h2 = N.le_trans(Nat.add(P, Nat.add(P, P)), Nat.add(P, Nat.add(P, Nat.add(P, P))), Nat.mul(4n, P),
    N.le_add_mono_l(P, Nat.add(P, P), Nat.add(P, Nat.add(P, P)), N.le_add_mono_l(P, P, Nat.add(P, P), N.le_add_r(P, P))),
    AB.subst(Nat, w => {Nat.is_le(Nat.add(P, Nat.add(P, Nat.add(P, w))), Nat.mul(4n, P)) == True{} : Bool}, Nat.add(P, 0n), P, N.add_zero(P), N.le_refl(Nat.mul(4n, P))))
  N.le_trans(Nat.add(x, Nat.add(y, z)), Nat.add(P, Nat.add(P, P)), Nat.mul(4n, P), h1, h2)

def F31() -> U32:
  1073741824

def HeadG(+p: P.RunP, +o: B.Opts, +l: B.Line) -> Type:
  &p2: P.RunP -> ({NR.head_line(True{}, P.mkRun(p), o, l) == P.mkRun(p2) : NR.Run}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.specRun(p2) == R.head_line(True{}, P.specRun(p), o, l) : R.RunSt}))

# The run before #CHROM: ob empty (length 0), nothing buffered.
def hw0(+n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  +o: B.Opts, +bd: String, +term: String,
  +hok0: {D.ok(C.BT(0, obt), RD.tdepth(obt)) == True{} : Bool},
  +h3: {D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) == True{} : Bool},
  +h4: {String.eq(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, "")) == True{} : Bool},
  +h6: {Bool.or(x, Nat.is_eq(bn, 0n)) == True{} : Bool},
  +hb: {E.is_bytes(String.append(h, String.append(R.added(o, term), String.append(bd, term)))) == True{} : Bool},
  +hT: {Nat.is_le(String.length(String.append(h, String.append(R.added(o, term), String.append(bd, term)))), Nat.pow(2n, 30n)) == True{} : Bool}) ->
  HeadG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, Nil{}, Nil{}, bn, tl, k, 0, obt, ow, ns, x}, o, B.Line{bd, term}):
  +TT = String.append(h, String.append(R.added(o, term), String.append(bd, term)))
  +LTT = String.length(TT)
  +L2 = BF.pstl(TT, 0)
  +T2 = BF.PSR(0, obt, TT)
  +hL = NM.lt_c0(LTT, Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(LTT, hT))
  +p2 = {P.RunP{n, True{}, "", c, cbl, cbt, e, la, Nil{}, Nil{}, bn, tl, k, L2, T2, L2, ns, x} : P.RunP}
  +eq = AB.subst(D.Bytes, z => {NR.head_line.out(z, NR.Run{n, True{}, "", c, C.BT(cbl, cbt), e, la, Nil{}, Nil{}, bn, tl, k, BY.empty(0n), ow, ns, x}) == P.mkRun(p2) : NR.Run},
    C.BT(L2, T2), NR.put_str(C.BT(0, obt), TT), Equal.sym(D.Bytes, NR.put_str(C.BT(0, obt), TT), C.BT(L2, T2), BF.put_str_eq(0, obt, TT, C.ok_full(0, obt, RD.tdepth(obt), hok0))), {==})
  +ok2 = BF.put_str_ok(0, obt, RD.tdepth(obt), TT, hok0, hL)
  +elen = BF.put_str_len(0, obt, RD.tdepth(obt), TT, hok0, hL)
  +hle = AB.subst(Nat, w => {Nat.is_le(w, Nat.pow(2n, 30n)) == True{} : Bool}, LTT, U32.to_nat(L2), Equal.sym(Nat, U32.to_nat(L2), LTT, elen), hT)
  +hle2 = AB.subst(Nat, w => {Nat.is_le(U32.to_nat(L2), w) == True{} : Bool}, Nat.pow(2n, 30n), U32.to_nat(F31()), Equal.sym(Nat, U32.to_nat(F31()), Nat.pow(2n, 30n), PL.lit_pow(30n, F31(), {==}, {==})), hle)
  +h2 = Equal.trans(Bool, U32.is_le(L2, F31()), Nat.is_le(U32.to_nat(L2), U32.to_nat(F31())), True{}, U.is_le_to_nat(L2, F31()), hle2)
  +X = U32.to_nat(L2)
  +h5 = AB.subst(Nat, w => {Nat.is_eq(w, X) == True{} : Bool}, X, Nat.add(X, 0n), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)), N.eq_refl(X))
  +hinv = PI.inv_mk(True{}, "", c, cbl, cbt, Nil{}, Nil{}, bn, tl, L2, T2, L2, ns, x, (ok2, (h2, (h3, (h4, (PI.or_r(x, Nat.is_eq(Nat.add(X, 0n), X), h5), (h6, ({==}, ({==}, ({==}, ({==}, N.le_refl(X))))))))))))
  +etx = Equal.trans(String, NR.chars(D.view(C.BT(L2, T2))), String.append(NR.chars(D.view(C.BT(0, obt))), TT), TT,
    BF.put_str_text(0, obt, RD.tdepth(obt), TT, hok0, hb, hL),
    AB.subst(List<&2, U32>, w => {String.append(NR.chars(w), TT) == TT : String}, Nil{}, D.view(C.BT(0, obt)), Equal.sym(List<&2, U32>, D.view(C.BT(0, obt)), Nil{}, BF.view0(obt)), {==}))
  +etk = Equal.trans(String, String.take(NR.chars(D.view(C.BT(L2, T2))), U32.to_nat(L2)), String.take(TT, LTT), TT,
    Equal.trans(String, String.take(NR.chars(D.view(C.BT(L2, T2))), U32.to_nat(L2)), String.take(TT, U32.to_nat(L2)), String.take(TT, LTT),
      Equal.cong(String, String, w => String.take(w, U32.to_nat(L2)), NR.chars(D.view(C.BT(L2, T2))), TT, etx),
      Equal.cong(Nat, String, w => String.take(TT, w), U32.to_nat(L2), LTT, elen)),
    str_take_all(TT))
  +chrom = Maybe.default(&2, String, c, "")
  +hs = AB.subst(String, w => {R.RunSt{n, True{}, "", c, e, NR.spec.last(la, chrom), Nil{}, k, w, List.reverse(&2, B.Note, ns), x} == R.head_line(True{}, P.specRun(P.RunP{n, False{}, h, c, cbl, cbt, e, la, Nil{}, Nil{}, bn, tl, k, 0, obt, ow, ns, x}), o, B.Line{bd, term}) : R.RunSt},
    TT, String.take(NR.chars(D.view(C.BT(L2, T2))), U32.to_nat(L2)), Equal.sym(String, String.take(NR.chars(D.view(C.BT(L2, T2))), U32.to_nat(L2)), TT, etk), {==})
  (p2, (eq, (hinv, hs)))

def head_t(+p: P.RunP, +o: B.Opts, +l: B.Line,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hin: {P.RunP.i(p) == False{} : Bool},
  +hh: {Norm.len_le(P.RunP.h(p), 268435456) == True{} : Bool},
  +hb1: {E.is_bytes(P.RunP.h(p)) == True{} : Bool},
  +hb2: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  +hb3: {E.is_bytes(R.added(o, B.Line.term(l))) == True{} : Bool},
  +hl: {Norm.len_le(B.Line.text(l), 268435456) == True{} : Bool},
  +hadd: {Norm.len_le(R.added(o, B.Line.term(l)), 268435456) == True{} : Bool}) -> HeadG(p, o, l):
  match p l:
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x} _:
      Empty.absurd(HeadG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, k, obl, obt, ow, ns, x}, o, l), AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hin)))
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, Con{+y, +ys}, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x} _:
      +h10 = PI.pr10(False{}, h, c, cbl, cbt, Con{y, ys}, b, bn, tl, obl, obt, ow, ns, x, hi)
      Empty.absurd(HeadG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, Con{y, ys}, b, bn, tl, k, obl, obt, ow, ns, x}, o, l),
        AB.false_ne_true(LM.andr(U32.is_zero(obl), False{} && (RD.is_nil(b) && (x || RD.no_notes(ns))), h10)))
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, Nil{}, Con{+y, +ys}, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x} _:
      +h10 = PI.pr10(False{}, h, c, cbl, cbt, Nil{}, Con{y, ys}, bn, tl, obl, obt, ow, ns, x, hi)
      Empty.absurd(HeadG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, Nil{}, Con{y, ys}, bn, tl, k, obl, obt, ow, ns, x}, o, l),
        AB.false_ne_true(LM.andl(False{}, x || RD.no_notes(ns), LM.andr(True{}, False{} && (x || RD.no_notes(ns)), LM.andr(U32.is_zero(obl), True{} && (False{} && (x || RD.no_notes(ns))), h10)))))
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, Nil{}, Nil{}, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x} B.Line{+bd, +term}:
      +h10 = PI.pr10(False{}, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, x, hi)
      +hz = LM.andl(U32.is_zero(obl), True{} && (True{} && (x || RD.no_notes(ns))), h10)
      +eobl = U.is_eq_true(obl, 0, hz)
      +hok0 = AB.subst(U32, w => {D.ok(C.BT(w, obt), RD.tdepth(obt)) == True{} : Bool}, obl, 0, eobl, PI.pr1(False{}, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, x, hi))
      +A = R.added(o, term)
      +Xs = String.append(bd, term)
      +hb = PI.bytes_app(h, String.append(A, Xs), hb1, PI.bytes_app(A, Xs, hb3, hb2))
      +h3 = three(String.length(h), String.length(A), String.length(Xs), 28n, 30n, {==}, SZ.len28(h, hh), SZ.len28(A, hadd), SZ.len28(Xs, hl))
      +elen = Equal.trans(Nat, String.length(String.append(h, String.append(A, Xs))), Nat.add(String.length(h), String.length(String.append(A, Xs))), Nat.add(String.length(h), Nat.add(String.length(A), String.length(Xs))),
        slen_app(h, String.append(A, Xs)), Equal.cong(Nat, Nat, w => Nat.add(String.length(h), w), String.length(String.append(A, Xs)), Nat.add(String.length(A), String.length(Xs)), slen_app(A, Xs)))
      +hT = AB.subst(Nat, w => {Nat.is_le(w, Nat.pow(2n, 30n)) == True{} : Bool}, Nat.add(String.length(h), Nat.add(String.length(A), String.length(Xs))), String.length(String.append(h, String.append(A, Xs))),
        Equal.sym(Nat, String.length(String.append(h, String.append(A, Xs))), Nat.add(String.length(h), Nat.add(String.length(A), String.length(Xs))), elen), h3)
      AB.subst(U32, w => HeadG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, Nil{}, Nil{}, bn, tl, k, w, obt, ow, ns, x}, o, B.Line{bd, term}), 0, obl, Equal.sym(U32, obl, 0, eobl),
        hw0(n, h, c, cbl, cbt, e, la, bn, tl, k, obt, ow, ns, x, o, bd, term, hok0,
        PI.pr3(False{}, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, x, hi), PI.pr4(False{}, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, x, hi),
        PI.pr6(False{}, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, x, hi), hb, hT))
