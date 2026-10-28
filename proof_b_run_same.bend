import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as Norm
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_run_base.bend as RBS
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-bytes/proof_list.bend as PLS
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# run_same (proof_b_run.bend): the fast path's CHROM test on a pictured run.

def SameG(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32) -> Type:
  &q: Bool -> ({Norm.Run.same(P.mkRun(p), C.BT(bl, bt), s, e0) == (P.mkRun(p), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)}
  & {Bool.pick(Maybe<&2, String>, q, Some{P.btext(bl, bt, s, (e0 - s : U32))}, P.RunP.c(p)) == P.RunP.c(p) : Maybe<&2, String>})

law chars_nil:
  for +xs: List<&2, U32>
  for +h: {NR.chars(xs) == "" : String}
  {xs == Nil{} : List<&2, U32>}

def chars_nil(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, U32>},
        AB.false_ne_true(Equal.cong(String, Bool, z => String.eq(z, ""), SCon{Chr{x}, NR.chars(t)}, "", h)))

law sub_pos:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(0n, Nat.sub(b, a)) == True{} : Bool}

def sub_pos(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p 1n+q:
      sub_pos(p, q, h)

def SLb(+bl: U32, +bt: AT.Tree<U32>, +s: U32, +n: U32) -> List<&2, U32>:
  D.slice(D.view(C.BT(bl, bt)), U32.to_nat(s), U32.to_nat(n))

def SLc(+cbl: U32, +cbt: AT.Tree<U32>, +n: U32) -> List<&2, U32>:
  D.slice(D.view(C.BT(cbl, cbt)), U32.to_nat(0), U32.to_nat(n))

# A passed test: CHROM's bytes are cb's, which hold the current CHROM.
def sv(+w: Bool, +c: Maybe<&2, String>, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +n: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hv: {D.list_eq(SLb(bl, bt, s, n), SLc(cbl, cbt, n)) == w : Bool},
  +en: {n == cbl : U32},
  +hcb: {NR.chars(D.view(C.BT(cbl, cbt))) == Maybe.default(&2, String, c, "") : String},
  +okcb: {D.ok(C.BT(cbl, cbt), RD.tdepth(cbt)) == True{} : Bool},
  +hpos: {Nat.is_lt(0n, U32.to_nat(n)) == True{} : Bool}) ->
  {Bool.pick(Maybe<&2, String>, w, Some{NR.chars(SLb(bl, bt, s, n))}, c) == c : Maybe<&2, String>}:
  match w c:
    case False{} _:
      {==}
    case True{} None{}:
      +e1 = PLS.list_eq_true(SLb(bl, bt, s, n), SLc(cbl, cbt, n), hv)
      +ev = Equal.trans(List<&2, U32>, SLc(cbl, cbt, n), SLc(cbl, cbt, cbl), D.view(C.BT(cbl, cbt)),
        Equal.cong(U32, List<&2, U32>, z => SLc(cbl, cbt, z), n, cbl, en), BF.view_all(cbl, cbt, RD.tdepth(cbt), okcb))
      +enil = chars_nil(D.view(C.BT(cbl, cbt)), hcb)
      +e0 = Equal.trans(Nat, U32.to_nat(cbl), List.length(&2, U32, D.view(C.BT(cbl, cbt))), 0n,
        Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(cbl, cbt))), U32.to_nat(cbl), O.view_size_t(cbl, cbt, RD.tdepth(cbt), okcb)),
        Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), D.view(C.BT(cbl, cbt)), Nil{}, enil))
      +hz = AB.subst(U32, z => {Nat.is_lt(0n, U32.to_nat(z)) == True{} : Bool}, n, cbl, en, hpos)
      +hz0 = AB.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, U32.to_nat(cbl), 0n, e0, hz)
      Empty.absurd({Some{NR.chars(SLb(bl, bt, s, n))} == None{} : Maybe<&2, String>}, AB.false_ne_true(hz0))
    case True{} Some{+cs}:
      +e1 = PLS.list_eq_true(SLb(bl, bt, s, n), SLc(cbl, cbt, n), hv)
      +ev = Equal.trans(List<&2, U32>, SLc(cbl, cbt, n), SLc(cbl, cbt, cbl), D.view(C.BT(cbl, cbt)),
        Equal.cong(U32, List<&2, U32>, z => SLc(cbl, cbt, z), n, cbl, en), BF.view_all(cbl, cbt, RD.tdepth(cbt), okcb))
      +eb = Equal.trans(List<&2, U32>, SLb(bl, bt, s, n), SLc(cbl, cbt, n), D.view(C.BT(cbl, cbt)), e1, ev)
      +es = Equal.trans(String, NR.chars(SLb(bl, bt, s, n)), NR.chars(D.view(C.BT(cbl, cbt))), cs,
        Equal.cong(List<&2, U32>, String, z => NR.chars(z), SLb(bl, bt, s, n), D.view(C.BT(cbl, cbt)), eb), hcb)
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, NR.chars(SLb(bl, bt, s, n)), cs, es)

def same_c(+z: Bool, +n0: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool,
  +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32,
  +hz: {U32.is_eq((e0 - s : U32), cbl) == z : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +hlt: {U32.is_lt(s, e0) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool}) ->
  SameG(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, bl, bt, s, e0):
  match z:
    case False{}:
      +eq = AB.subst(Bool, w => {Norm.Run.same.k(NR.Run{n0, i, h, c, BY.empty(0n), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, x}, NF.same.if(w, C.BT(bl, bt), s, C.BT(cbl, cbt), (e0 - s : U32)))
          == (P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), (C.BT(bl, bt), False{})) : NR.Run & (D.Bytes & Bool)},
        False{}, U32.is_eq((e0 - s : U32), cbl), Equal.sym(Bool, U32.is_eq((e0 - s : U32), cbl), False{}, hz), {==})
      (False{}, (eq, {==}))
    case True{}:
      +n = (e0 - s : U32)
      +V = Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, n)))
      +eq1 = AB.subst(D.Bytes & (D.Bytes & Bool), w => {Norm.Run.same.k(NR.Run{n0, i, h, c, BY.empty(0n), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, x}, w)
          == (P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), (C.BT(bl, bt), V)) : NR.Run & (D.Bytes & Bool)},
        (C.BT(bl, bt), (C.BT(cbl, cbt), V)), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, n),
        Equal.sym(D.Bytes & (D.Bytes & Bool), BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, n), (C.BT(bl, bt), (C.BT(cbl, cbt), V)), SM.same_pair_t(bl, bt, cbl, cbt, s, 0, n)), {==})
      +eq = AB.subst(Bool, w => {Norm.Run.same.k(NR.Run{n0, i, h, c, BY.empty(0n), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, x}, NF.same.if(w, C.BT(bl, bt), s, C.BT(cbl, cbt), n))
          == (P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), (C.BT(bl, bt), V)) : NR.Run & (D.Bytes & Bool)},
        True{}, U32.is_eq(n, cbl), Equal.sym(Bool, U32.is_eq(n, cbl), True{}, hz), eq1)
      +en = U.is_eq_true(n, cbl, hz)
      +okcb = PI.pr3(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +hcb = RBS.str_eq_sound(NR.chars(D.view(C.BT(cbl, cbt))), Maybe.default(&2, String, c, ""), PI.pr4(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))
      +hsU = Equal.trans(Bool, U32.is_le(s, e0), Nat.is_le(U32.to_nat(s), U32.to_nat(e0)), True{}, U.is_le_to_nat(s, e0), hs)
      +enat = U.to_nat_sub_le(e0, s, hsU)
      +hltN = Equal.trans(Bool, Nat.is_lt(U32.to_nat(s), U32.to_nat(e0)), U32.is_lt(s, e0), True{}, Equal.sym(Bool, U32.is_lt(s, e0), Nat.is_lt(U32.to_nat(s), U32.to_nat(e0)), U.is_lt_to_nat(s, e0)), hlt)
      +hpos = AB.subst(Nat, w => {Nat.is_lt(0n, w) == True{} : Bool}, Nat.sub(U32.to_nat(e0), U32.to_nat(s)), U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), Nat.sub(U32.to_nat(e0), U32.to_nat(s)), enat),
        sub_pos(U32.to_nat(s), U32.to_nat(e0), hltN))
      +hi1 = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(s), w), U32.to_nat(bl)) == True{} : Bool}, Nat.sub(U32.to_nat(e0), U32.to_nat(s)), U32.to_nat(n), Equal.sym(Nat, U32.to_nat(n), Nat.sub(U32.to_nat(e0), U32.to_nat(s)), enat),
        AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(bl)) == True{} : Bool}, U32.to_nat(e0), Nat.add(U32.to_nat(s), Nat.sub(U32.to_nat(e0), U32.to_nat(s))),
          Equal.sym(Nat, Nat.add(U32.to_nat(s), Nat.sub(U32.to_nat(e0), U32.to_nat(s))), U32.to_nat(e0), N.le_sub_add(U32.to_nat(s), U32.to_nat(e0), hs)), he))
      +hj1 = AB.subst(U32, w => {Nat.is_le(Nat.add(U32.to_nat(0), U32.to_nat(w)), U32.to_nat(cbl)) == True{} : Bool}, cbl, n, Equal.sym(U32, n, cbl, en), N.le_refl(U32.to_nat(cbl)))
      +hv = Equal.sym(Bool, V, D.list_eq(SLb(bl, bt, s, n), SLc(cbl, cbt, n)), SM.same_view_t(bl, bt, cbl, cbt, bd, RD.tdepth(cbt), s, 0, n, hok, okcb, hi1, hj1))
      (V, (eq, sv(V, c, bl, bt, s, n, cbl, cbt, hv, en, hcb, okcb, hpos)))

def same_t(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +hlt: {U32.is_lt(s, e0) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool}) -> SameG(p, bl, bt, s, e0):
  match p:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      same_c(U32.is_eq((e0 - s : U32), cbl), n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x, bl, bt, bd, s, e0, {==}, hi, hok, hs, hlt, he)
