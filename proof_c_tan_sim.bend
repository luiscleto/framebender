import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_num.bend as TN
import ./proof_c_tan_el.bend as TE
import ./proof_c_tan_alk.bend as TA
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_seq.bend as BQ
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase C, area "tan": all alleles on the closed form (Q.ALKS). NX.ends's
# flags are tan.bend's lasts_eq/firsts_eq and all_long; inits, shifted and
# tails move the counters; Q.KL (every allele keeps a base) holds along.

law lt_add0:
  for +t: Nat
  for +l: Nat
  for +h: {Nat.is_lt(Nat.add(t, 0n), l) == True{} : Bool}
  {Nat.is_lt(t, l) == True{} : Bool}

def lt_add0(t, l, h):
  %N.add_zero(t) : {Nat.is_lt(_, l) == True{} : Bool}
  h

law ends_go_last:
  for als: List<&2, NX.Ap>
  for +e: Bool
  for +l0: Bool
  for +x0: U32
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {Q.ENDS.go(als, e, l0, NX.code(x0), bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu) == Q.EB{e && V.same_last(Some{Q.bf(x0)}, Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)), l0 && V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n))} : Q.EB}

def ends_go_last(als, e, l0, x0, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(e, True{}), e, N.and_true_r_id(e)) : {Q.EB{e, l0} == Q.EB{_, Bool.and(l0, True{})} : Q.EB}
      %Equal.sym(Bool, Bool.and(l0, True{}), l0, N.and_true_r_id(l0)) : {Q.EB{e, l0} == Q.EB{e, _} : Q.EB}
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +xa = Q.EL(bl, bt, wl, wt, a, k, ((NX.Ap.ln(a) - tr : U32) - 1 : U32), p0, offu)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)
      +Ea = U32.is_eq(NX.code(xa), NX.code(x0))
      +La = U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(0n) : U32))
      +SLt = V.same_last(Some{Q.bf(x0)}, At)
      +ALt = V.all_long(At)
      +LH = Q.ENDS.go(t, e && Ea, l0 && La, NX.code(x0), bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu)
      +htr = lt_add0(Q.n(tr), l, hkh)
      %Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, Aa), Some{Q.bf(xa)}, TA.alk_last(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr)) :
        {LH == Q.EB{e && (V.opt_eq(Some{Q.bf(x0)}, _) && SLt), l0 && (Nat.is_le(2n, List.length(&2, B.Base, Aa)) && ALt)} : Q.EB}
      %Equal.sym(Bool, B.Base.is_eq(Q.bf(x0), Q.bf(xa)), Ea, TL.beq_code(x0, xa)) :
        {LH == Q.EB{e && (_ && SLt), l0 && (Nat.is_le(2n, List.length(&2, B.Base, Aa)) && ALt)} : Q.EB}
      %Equal.sym(Nat, List.length(&2, B.Base, Aa), Nat.sub(Nat.sub(l, Q.n(tr)), 0n), TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, 0n, hb, hw, hin, hk, ho)) :
        {LH == Q.EB{e && (Ea && SLt), l0 && (Nat.is_le(2n, _) && ALt)} : Q.EB}
      %TN.u_long(NX.Ap.ln(a), tr, 0n, hkh) :
        {LH == Q.EB{e && (Ea && SLt), l0 && (_ && ALt)} : Q.EB}
      %TL.and_assoc(e, Ea, SLt) : {LH == Q.EB{_, l0 && (La && ALt)} : Q.EB}
      %TL.and_assoc(l0, La, ALt) : {LH == Q.EB{(e && Ea) && SLt, _} : Q.EB}
      ends_go_last(t, e && Ea, l0 && La, x0, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, hat, hk, ho, hkt)

law ends_go_first:
  for als: List<&2, NX.Ap>
  for +e: Bool
  for +l0: Bool
  for +x0: U32
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, d) == True{} : Bool}
  {Q.ENDS.go(als, e, l0, NX.code(x0), bl, bt, wl, wt, k, tr, d, False{}, p0, offu) == Q.EB{e && V.same_first(Some{Q.bf(x0)}, Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)), l0 && V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d))} : Q.EB}

def ends_go_first(als, e, l0, x0, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(e, True{}), e, N.and_true_r_id(e)) : {Q.EB{e, l0} == Q.EB{_, Bool.and(l0, True{})} : Q.EB}
      %Equal.sym(Bool, Bool.and(l0, True{}), l0, N.and_true_r_id(l0)) : {Q.EB{e, l0} == Q.EB{e, _} : Q.EB}
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +xa = Q.EL(bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)
      +Ea = U32.is_eq(NX.code(xa), NX.code(x0))
      +La = U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32))
      +SLt = V.same_first(Some{Q.bf(x0)}, At)
      +ALt = V.all_long(At)
      +LH = Q.ENDS.go(t, e && Ea, l0 && La, NX.code(x0), bl, bt, wl, wt, k, tr, d, False{}, p0, offu)
      %Equal.sym(Maybe<&2, B.Base>, List.head(&2, B.Base, Aa), Some{Q.bf(xa)}, TA.alk_head(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hkh)) :
        {LH == Q.EB{e && (V.opt_eq(Some{Q.bf(x0)}, _) && SLt), l0 && (Nat.is_le(2n, List.length(&2, B.Base, Aa)) && ALt)} : Q.EB}
      %Equal.sym(Bool, B.Base.is_eq(Q.bf(x0), Q.bf(xa)), Ea, TL.beq_code(x0, xa)) :
        {LH == Q.EB{e && (_ && SLt), l0 && (Nat.is_le(2n, List.length(&2, B.Base, Aa)) && ALt)} : Q.EB}
      %Equal.sym(Nat, List.length(&2, B.Base, Aa), Nat.sub(Nat.sub(l, Q.n(tr)), d), TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho)) :
        {LH == Q.EB{e && (Ea && SLt), l0 && (Nat.is_le(2n, _) && ALt)} : Q.EB}
      %TN.u_long(NX.Ap.ln(a), tr, d, hkh) :
        {LH == Q.EB{e && (Ea && SLt), l0 && (_ && ALt)} : Q.EB}
      %TL.and_assoc(e, Ea, SLt) : {LH == Q.EB{_, l0 && (La && ALt)} : Q.EB}
      %TL.and_assoc(l0, La, ALt) : {LH == Q.EB{(e && Ea) && SLt, _} : Q.EB}
      ends_go_first(t, e && Ea, l0 && La, x0, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, hat, hk, ho, hkt)

law ends_last_t:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {Q.ENDS(als, bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu) == Q.EB{V.lasts_eq(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)), V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n))} : Q.EB}

def ends_last_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +htr = lt_add0(Q.n(tr), l, hkh)
      +xa = Q.EL(bl, bt, wl, wt, a, k, ((NX.Ap.ln(a) - tr : U32) - 1 : U32), p0, offu)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)
      +La = U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(0n) : U32))
      +LH = Q.ENDS.go(t, True{}, La, NX.code(xa), bl, bt, wl, wt, k, tr, 0n, True{}, p0, offu)
      %Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, Aa), Some{Q.bf(xa)}, TA.alk_last(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr)) :
        {LH == Q.EB{V.same_last(_, At), Nat.is_le(2n, List.length(&2, B.Base, Aa)) && V.all_long(At)} : Q.EB}
      %Equal.sym(Nat, List.length(&2, B.Base, Aa), Nat.sub(Nat.sub(l, Q.n(tr)), 0n), TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, 0n, hb, hw, hin, hk, ho)) :
        {LH == Q.EB{V.same_last(Some{Q.bf(xa)}, At), Nat.is_le(2n, _) && V.all_long(At)} : Q.EB}
      %TN.u_long(NX.Ap.ln(a), tr, 0n, hkh) :
        {LH == Q.EB{V.same_last(Some{Q.bf(xa)}, At), _ && V.all_long(At)} : Q.EB}
      ends_go_last(t, True{}, La, xa, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, hat, hk, ho, hkt)

law ends_first_t:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, d) == True{} : Bool}
  {Q.ENDS(als, bl, bt, wl, wt, k, tr, d, False{}, p0, offu) == Q.EB{V.firsts_eq(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)), V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d))} : Q.EB}

def ends_first_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +xa = Q.EL(bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)
      +La = U32.is_le(2, ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32))
      +LH = Q.ENDS.go(t, True{}, La, NX.code(xa), bl, bt, wl, wt, k, tr, d, False{}, p0, offu)
      %Equal.sym(Maybe<&2, B.Base>, List.head(&2, B.Base, Aa), Some{Q.bf(xa)}, TA.alk_head(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hkh)) :
        {LH == Q.EB{V.same_first(_, At), Nat.is_le(2n, List.length(&2, B.Base, Aa)) && V.all_long(At)} : Q.EB}
      %Equal.sym(Nat, List.length(&2, B.Base, Aa), Nat.sub(Nat.sub(l, Q.n(tr)), d), TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho)) :
        {LH == Q.EB{V.same_first(Some{Q.bf(xa)}, At), Nat.is_le(2n, _) && V.all_long(At)} : Q.EB}
      %TN.u_long(NX.Ap.ln(a), tr, d, hkh) :
        {LH == Q.EB{V.same_first(Some{Q.bf(xa)}, At), _ && V.all_long(At)} : Q.EB}
      ends_go_first(t, True{}, La, xa, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, hat, hk, ho, hkt)

law alks_total:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {V.total(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)) == NX.tot(als, tr) : Nat}

def alks_total(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +htr = lt_add0(Q.n(tr), l, hkh)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)
      +m = Nat.sub(l, Q.n(tr))
      +RH = Nat.add(Q.n((NX.Ap.ln(a) - tr : U32)), NX.tot(t, tr))
      %Equal.sym(Nat, List.length(&2, B.Base, Aa), Nat.sub(m, 0n), TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, 0n, hb, hw, hin, hk, ho)) :
        {Nat.add(_, V.total(At)) == RH : Nat}
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.add(_, V.total(At)) == RH : Nat}
      %TL.u_sub(NX.Ap.ln(a), tr, TL.le_of_lt(Q.n(tr), l, htr)) : {Nat.add(_, V.total(At)) == RH : Nat}
      %Equal.sym(Nat, V.total(At), NX.tot(t, tr), alks_total(t, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, hat, hk, ho, hkt)) :
        {Nat.add(Q.n((NX.Ap.ln(a) - tr : U32)), _) == RH : Nat}
      {==}

law alks_inits:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  {V.inits(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)) == Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, (tr + 1 : U32), 0n) : List<&2, List<&2, B.Base>>}

def alks_inits(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +htr = lt_add0(Q.n(tr), l, hkh)
      +RH = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a <> t, k, (tr + 1 : U32), 0n)
      %Equal.sym(List<&2, B.Base>, V.init(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))), Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, (tr + 1 : U32), 0n)), TA.alk_init(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr)) :
        {{_ <> V.inits(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)) : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, List<&2, B.Base>>, V.inits(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, (tr + 1 : U32), 0n), alks_inits(t, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, hat, hk, ho, hkt)) :
        {{Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, (tr + 1 : U32), 0n)) <> _ : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      {==}

law alks_shift:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, 0n) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  {V.shifted(TA.SB(wl, wt, p0, offu, k), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, 0n)) == Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, (k + 1 : U32), tr, 0n) : List<&2, List<&2, B.Base>>}

def alks_shift(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, ha, hk, ho, hkl, hS, hH):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 0n), l), Q.KL(t, tr, 0n), hkl)
      +htr = lt_add0(Q.n(tr), l, hkh)
      +b = TA.SB(wl, wt, p0, offu, k)
      +RH = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a <> t, (k + 1 : U32), tr, 0n)
      %Equal.sym(List<&2, B.Base>, {b <> V.init(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))) : List<&2, B.Base>}, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, (k + 1 : U32), tr, 0n)), TA.alk_shift(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr, hS, hH)) :
        {{_ <> V.shifted(b, Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)) : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, List<&2, B.Base>>, V.shifted(b, Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, 0n)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, (k + 1 : U32), tr, 0n), alks_shift(t, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, hb, hw, hat, hk, ho, hkt, hS, hH)) :
        {{Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, (k + 1 : U32), tr, 0n)) <> _ : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      {==}

law alks_tails:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  {V.tails(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)) == Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, Nat.add(1n, d)) : List<&2, List<&2, B.Base>>}

def alks_tails(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +RH = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a <> t, k, tr, Nat.add(1n, d))
      %Equal.sym(List<&2, B.Base>, List.tail(&2, B.Base, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))), Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, Nat.add(1n, d))), TA.alk_tail(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d)) :
        {{_ <> V.tails(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)) : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, List<&2, B.Base>>, V.tails(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)), Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, Nat.add(1n, d)), alks_tails(t, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d)) :
        {{Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, Nat.add(1n, d))) <> _ : List<&2, List<&2, B.Base>>} == RH : List<&2, List<&2, B.Base>>}
      {==}

# A left trim (every allele two long or more) keeps Q.KL.
law kl_long:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hkl: {Q.KL(als, tr, d) == True{} : Bool}
  for +hal: {V.all_long(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)) == True{} : Bool}
  {Q.KL(als, tr, Nat.add(1n, d)) == True{} : Bool}

def kl_long(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl, hal):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +Aa = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))
      +At = Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)
      TL.and_tt(Nat.is_lt(Nat.add(Q.n(tr), Nat.add(1n, d)), l), Q.KL(t, tr, Nat.add(1n, d)),
        TN.kl_step(Q.n(tr), d, l, hkh,
          %TA.alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho) : {Nat.is_le(2n, _) == True{} : Bool}
          TL.and_l(Nat.is_le(2n, List.length(&2, B.Base, Aa)), V.all_long(At), hal)),
        kl_long(t, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, hat, hk, ho, hkt, TL.and_r(Nat.is_le(2n, List.length(&2, B.Base, Aa)), V.all_long(At), hal)))

law kl_inc_h:
  for +tr: U32
  for +ln: U32
  for +h: {Nat.is_lt(Nat.add(Q.n(tr), 1n), Q.n(ln)) == True{} : Bool}
  {Nat.is_lt(Nat.add(Q.n((tr + 1 : U32)), 0n), Q.n(ln)) == True{} : Bool}

def kl_inc_h(tr, ln, h):
  +t1 = Q.n((tr + 1 : U32))
  %Equal.sym(Nat, Nat.add(t1, 0n), t1, N.add_zero(t1)) : {Nat.is_lt(_, Q.n(ln)) == True{} : Bool}
  %Equal.sym(Nat, t1, Nat.add(Q.n(tr), 1n), TL.u_inc(tr, ln, N.le_lt_trans(Q.n(tr), Nat.add(Q.n(tr), 1n), Q.n(ln), N.le_add_r(Q.n(tr), 1n), h))) :
    {Nat.is_lt(_, Q.n(ln)) == True{} : Bool}
  h

# A right trim (every allele two long or more) keeps Q.KL.
law kl_inc:
  for als: List<&2, NX.Ap>
  for +tr: U32
  for +hkl: {Q.KL(als, tr, 1n) == True{} : Bool}
  {Q.KL(als, (tr + 1 : U32), 0n) == True{} : Bool}

def kl_inc(als, tr, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), 1n), l), Q.KL(t, tr, 1n), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), 1n), l), Q.KL(t, tr, 1n), hkl)
      TL.and_tt(Nat.is_lt(Nat.add(Q.n((tr + 1 : U32)), 0n), l), Q.KL(t, (tr + 1 : U32), 0n), kl_inc_h(tr, NX.Ap.ln(a), hkh), kl_inc(t, tr, hkt))

# Before any step every allele has its own bases.
law kl0:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +ha: {Q.ALS_IN(bl, als) == True{} : Bool}
  {Q.KL(als, 0, 0n) == True{} : Bool}

def kl0(als, bl, ha):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +h1l = TL.and_l(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      TL.and_tt(Nat.is_lt(0n, l), Q.KL(t, 0, 0n),
        Equal.trans(Bool, Nat.is_lt(0n, l), Nat.is_le(1n, l), True{}, Equal.sym(Bool, Nat.is_le(1n, l), Nat.is_lt(0n, l), N.le_succ_lt(0n, l)), h1l),
        kl0(t, bl, hat))

# The record's alleles are the closed form with no step taken.
law bfs_init:
  for als: List<&2, NX.Ap>
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +p0: U32
  for +offu: U32
  {Q.BFS(Q.xs(bl, bt), als) == Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, 0, 0, 0n) : List<&2, List<&2, B.Base>>}

def bfs_init(als, bl, bt, wl, wt, p0, offu):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +ys = Q.xs(bl, bt)
      +ws = Q.xs(wl, wt)
      +l = Q.n(NX.Ap.ln(a))
      +Dw = List.drop(&2, U32, ws, Nat.sub(Nat.sub(Nat.sub(Q.n(p0), 1n), 0n), Q.n(offu)))
      +Dy = List.drop(&2, U32, ys, Q.n(NX.Ap.st(a)))
      +S = Q.SL(ys, a)
      +T0 = List.take(&2, U32, List.append(&2, U32, List.take(&2, U32, Dw, 0n), S), Nat.sub(l, 0n))
      +At = Q.ALKS(ys, ws, p0, offu, t, 0, 0, 0n)
      +LH = {Q.BF(S) <> Q.BFS(ys, t) : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, T0, 0n), T0, TL.drop_zero(T0)) : {LH == {Q.BF(_) <> At : List<&2, List<&2, B.Base>>} : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Dw, 0n), Nil{}, BQ.take_zero(Dw)) :
        {LH == {Q.BF(List.take(&2, U32, List.append(&2, U32, _, S), Nat.sub(l, 0n))) <> At : List<&2, List<&2, B.Base>>} : List<&2, List<&2, B.Base>>}
      %Equal.sym(Nat, Nat.sub(l, 0n), l, N.sub_zero(l)) : {LH == {Q.BF(List.take(&2, U32, S, _)) <> At : List<&2, List<&2, B.Base>>} : List<&2, List<&2, B.Base>>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, S, l), S, TL.take_take(Dy, l, l, N.le_refl(l))) : {LH == {Q.BF(_) <> At : List<&2, List<&2, B.Base>>} : List<&2, List<&2, B.Base>>}
      %bfs_init(t, bl, bt, wl, wt, p0, offu) : {LH == {Q.BF(S) <> _ : List<&2, List<&2, B.Base>>} : List<&2, List<&2, B.Base>>}
      {==}
