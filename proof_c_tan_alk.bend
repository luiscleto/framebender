import Base
import ./types.bend as B
import ./tan.bend as V
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_num.bend as TN
import ./proof_c_tan_el.bend as TE
import ./proof_var_lists.bend as VL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C, area "tan": one allele on the closed form. With k shifts and tr
# right trims the allele is take(XA, L - tr) (XA = R_k ++ a); after d left
# trims, drop(that, d) (Q.ALK). Its last and first bases are the bytes
# NX.el reads; tan.bend's init, tail and shifted move the counters.

# Byte j of R_k ++ a is the byte NX.el reads.
def el_get.c(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +wd: Nat, +a: NX.Ap, +p0: U32, +offu: U32, +k: U32, +j: U32,
  inw: Bool, +hinw: {U32.is_lt(j, k) == inw : Bool},
  +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool},
  +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool},
  +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool},
  +hj: {Nat.is_lt(Q.n(j), Q.n(NX.Ap.ln(a))) == True{} : Bool}) ->
  {List.get(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Q.n(j)) == Some{Q.EL.if(inw, bl, bt, wl, wt, ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32), ((NX.Ap.st(a) + j : U32) - k : U32))} : Maybe<&2, U32>}:
  match inw:
    case True{}:
      TE.el_get.w(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hw, hk, ho,
        Equal.trans(Bool, Nat.is_lt(Q.n(j), Q.n(k)), U32.is_lt(j, k), True{}, Equal.sym(Bool, U32.is_lt(j, k), Nat.is_lt(Q.n(j), Q.n(k)), U.is_lt_to_nat(j, k)), hinw))
    case False{}:
      TE.el_get.l(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho,
        N.not_lt_le(Q.n(j), Q.n(k), Equal.trans(Bool, Nat.is_lt(Q.n(j), Q.n(k)), U32.is_lt(j, k), False{}, Equal.sym(Bool, U32.is_lt(j, k), Nat.is_lt(Q.n(j), Q.n(k)), U.is_lt_to_nat(j, k)), hinw)),
        hj)

law el_get:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +j: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hj: {Nat.is_lt(Q.n(j), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {List.get(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Q.n(j)) == Some{Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)} : Maybe<&2, U32>}

def el_get(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho, hj):
  el_get.c(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, U32.is_lt(j, k), {==}, hb, hw, hin, hk, ho, hj)

# m <= |XA|, for m = L - tr.
law m_le:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {Nat.is_le(Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr)), List.length(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k))) == True{} : Bool}

def m_le(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho):
  +l = Q.n(NX.Ap.ln(a))
  %Equal.sym(Nat, List.length(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)), Nat.add(Q.n(k), l), TE.len_xa(bl, bt, bd, wl, wt, wd, a, p0, offu, k, hb, hw, hin, hk, ho)) : {Nat.is_le(Nat.sub(l, Q.n(tr)), _) == True{} : Bool}
  N.le_trans(Nat.sub(l, Q.n(tr)), l, Nat.add(Q.n(k), l), TN.sub_le_self(l, Q.n(tr)), N.le_add_l(l, Q.n(k)))

# The index of the last base, as a number.
law j_last:
  for +ln: U32
  for +tr: U32
  for +htr: {Nat.is_lt(Q.n(tr), Q.n(ln)) == True{} : Bool}
  {Q.n(((ln - tr : U32) - 1 : U32)) == Nat.sub(Nat.sub(Q.n(ln), Q.n(tr)), 1n) : Nat}

def j_last(ln, tr, htr):
  +m = Nat.sub(Q.n(ln), Q.n(tr))
  +lt = (ln - tr : U32)
  +E1 = TL.u_sub(ln, tr, TL.le_of_lt(Q.n(tr), Q.n(ln), htr))
  %Equal.sym(Nat, Q.n((lt - 1 : U32)), Nat.sub(Q.n(lt), 1n), TL.u_sub(lt, 1,
    %Equal.sym(Nat, Q.n(lt), m, E1) : {Nat.is_le(1n, _) == True{} : Bool}
    TL.le_sub(Q.n(tr), 1n, Q.n(ln), TL.lt_succ_le(Q.n(tr), Q.n(ln), htr)))) : {_ == Nat.sub(m, 1n) : Nat}
  %Equal.sym(Nat, Q.n(lt), m, E1) : {Nat.sub(_, 1n) == Nat.sub(m, 1n) : Nat}
  {==}

law alk_last:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +htr: {Nat.is_lt(Q.n(tr), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {List.last(&2, B.Base, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))) == Some{Q.bf(Q.EL(bl, bt, wl, wt, a, k, ((NX.Ap.ln(a) - tr : U32) - 1 : U32), p0, offu))} : Maybe<&2, B.Base>}

def alk_last(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +j = ((NX.Ap.ln(a) - tr : U32) - 1 : U32)
  +R = {Some{Q.bf(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu))} : Maybe<&2, B.Base>}
  +h1 = TL.le_sub(Q.n(tr), 1n, l, TL.lt_succ_le(Q.n(tr), l, htr))
  +Ej = j_last(NX.Ap.ln(a), tr, htr)
  +hm1 = TL.le_succ_lt(Nat.sub(m, 1n), l,
    %Equal.sym(Nat, Nat.add(Nat.sub(m, 1n), 1n), m, TN.pred_succ(m, h1)) : {Nat.is_le(_, l) == True{} : Bool}
    TN.sub_le_self(l, Q.n(tr)))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, T, 0n), T, TL.drop_zero(T)) : {List.last(&2, B.Base, Q.BF(_)) == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, B.Base>, List.last(&2, B.Base, Q.BF(T)), TL.MB(List.last(&2, U32, T)), TL.bf_last(T)) : {_ == R : Maybe<&2, B.Base>}
  %VL.succ_sub_one(m, h1) : {TL.MB(List.last(&2, U32, List.take(&2, U32, X, _))) == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.last(&2, U32, List.take(&2, U32, X, 1n+Nat.sub(m, 1n))), List.get(&2, U32, X, Nat.sub(m, 1n)), TL.last_take(X, Nat.sub(m, 1n),
      %Equal.sym(Nat, List.length(&2, U32, X), Nat.add(Q.n(k), l), TE.len_xa(bl, bt, bd, wl, wt, wd, a, p0, offu, k, hb, hw, hin, hk, ho)) :
        {Nat.is_lt(Nat.sub(m, 1n), _) == True{} : Bool}
      N.lt_le_trans(Nat.sub(m, 1n), l, Nat.add(Q.n(k), l), hm1, N.le_add_l(l, Q.n(k))))) :
    {TL.MB(_) == R : Maybe<&2, B.Base>}
  %Ej : {TL.MB(List.get(&2, U32, X, _)) == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, X, Q.n(j)), Some{Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)}, el_get(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho,
      %Equal.sym(Nat, Q.n(j), Nat.sub(m, 1n), Ej) : {Nat.is_lt(_, l) == True{} : Bool}
      hm1)) :
    {TL.MB(_) == R : Maybe<&2, B.Base>}
  {==}

law alk_head:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +htd: {Nat.is_lt(Nat.add(Q.n(tr), d), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {List.head(&2, B.Base, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) == Some{Q.bf(Q.EL(bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu))} : Maybe<&2, B.Base>}

def alk_head(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, htd):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +j = U32.from_nat(d)
  +R = {Some{Q.bf(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu))} : Maybe<&2, B.Base>}
  +hdl = N.le_lt_trans(d, Nat.add(Q.n(tr), d), l, N.le_add_l(d, Q.n(tr)), htd)
  +Ed = TL.u_from(d, NX.Ap.ln(a), hdl)
  %Equal.sym(Maybe<&2, B.Base>, List.head(&2, B.Base, Q.BF(List.drop(&2, U32, T, d))), TL.MB(List.head(&2, U32, List.drop(&2, U32, T, d))), TL.bf_head(List.drop(&2, U32, T, d))) :
    {_ == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.head(&2, U32, List.drop(&2, U32, T, d)), List.get(&2, U32, T, d), TL.head_drop(T, d)) :
    {TL.MB(_) == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, T, d), List.get(&2, U32, X, d), TL.get_take(X, m, d, TN.lt_sub(Q.n(tr), d, l, htd))) :
    {TL.MB(_) == R : Maybe<&2, B.Base>}
  %Ed : {TL.MB(List.get(&2, U32, X, _)) == R : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, X, Q.n(j)), Some{Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)}, el_get(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho,
      %Equal.sym(Nat, Q.n(j), d, Ed) : {Nat.is_lt(_, l) == True{} : Bool}
      hdl)) :
    {TL.MB(_) == R : Maybe<&2, B.Base>}
  {==}

law alk_len:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {List.length(&2, B.Base, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) == Nat.sub(Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr)), d) : Nat}

def alk_len(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +RH = Nat.sub(m, d)
  %Equal.sym(Nat, List.length(&2, B.Base, Q.BF(List.drop(&2, U32, T, d))), List.length(&2, U32, List.drop(&2, U32, T, d)), TL.bf_len(List.drop(&2, U32, T, d))) :
    {_ == RH : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, T, d)), Nat.sub(List.length(&2, U32, T), d), TL.len_drop(T, d)) :
    {_ == RH : Nat}
  %Equal.sym(Nat, List.length(&2, U32, T), m, TL.len_take(X, m, m_le(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho))) :
    {Nat.sub(_, d) == RH : Nat}
  {==}

# tan.bend's init on take(X, m).
law init_core:
  for +X: List<&2, U32>
  for +m: Nat
  for +h: {Nat.is_le(m, List.length(&2, U32, X)) == True{} : Bool}
  {V.init(Q.BF(List.drop(&2, U32, List.take(&2, U32, X, m), 0n))) == Q.BF(List.take(&2, U32, X, Nat.sub(m, 1n))) : List<&2, B.Base>}

def init_core(X, m, h):
  +T = List.take(&2, U32, X, m)
  +RH = Q.BF(List.take(&2, U32, X, Nat.sub(m, 1n)))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, T, 0n), T, TL.drop_zero(T)) : {V.init(Q.BF(_)) == RH : List<&2, B.Base>}
  %Equal.sym(Nat, List.length(&2, B.Base, Q.BF(T)), List.length(&2, U32, T), TL.bf_len(T)) :
    {List.take(&2, B.Base, Q.BF(T), Nat.sub(_, 1n)) == RH : List<&2, B.Base>}
  %Equal.sym(Nat, List.length(&2, U32, T), m, TL.len_take(X, m, h)) :
    {List.take(&2, B.Base, Q.BF(T), Nat.sub(_, 1n)) == RH : List<&2, B.Base>}
  %TL.bf_take(T, Nat.sub(m, 1n)) : {_ == RH : List<&2, B.Base>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, T, Nat.sub(m, 1n)), List.take(&2, U32, X, Nat.sub(m, 1n)), TL.take_take(X, m, Nat.sub(m, 1n), TN.sub_le_self(m, 1n))) :
    {Q.BF(_) == RH : List<&2, B.Base>}
  {==}

law alk_init:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +htr: {Nat.is_lt(Q.n(tr), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {V.init(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))) == Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, (tr + 1 : U32), 0n)) : List<&2, B.Base>}

def alk_init(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +LH = Q.BF(List.take(&2, U32, X, Nat.sub(m, 1n)))
  +T1 = List.take(&2, U32, X, Nat.sub(l, Q.n((tr + 1 : U32))))
  %Equal.sym(List<&2, B.Base>, V.init(Q.BF(List.drop(&2, U32, T, 0n))), LH, init_core(X, m, m_le(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho))) :
    {_ == Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, (tr + 1 : U32), 0n)) : List<&2, B.Base>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, T1, 0n), T1, TL.drop_zero(T1)) : {LH == Q.BF(_) : List<&2, B.Base>}
  %Equal.sym(Nat, Q.n((tr + 1 : U32)), Nat.add(Q.n(tr), 1n), TL.u_inc(tr, NX.Ap.ln(a), htr)) :
    {LH == Q.BF(List.take(&2, U32, X, Nat.sub(l, _))) : List<&2, B.Base>}
  %TL.sub_sub(l, Q.n(tr), 1n) : {LH == Q.BF(List.take(&2, U32, X, _)) : List<&2, B.Base>}
  {==}

law alk_tail:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +d: Nat
  {List.tail(&2, B.Base, Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) == Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, Nat.add(1n, d))) : List<&2, B.Base>}

def alk_tail(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +RH = Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, Nat.add(1n, d)))
  %Equal.sym(List<&2, B.Base>, List.tail(&2, B.Base, Q.BF(List.drop(&2, U32, T, d))), Q.BF(List.tail(&2, U32, List.drop(&2, U32, T, d))), TL.bf_tail(List.drop(&2, U32, T, d))) :
    {_ == RH : List<&2, B.Base>}
  %Equal.sym(List<&2, U32>, List.tail(&2, U32, List.drop(&2, U32, T, d)), List.drop(&2, U32, T, 1n+d), TL.tail_drop(T, d)) :
    {Q.BF(_) == RH : List<&2, B.Base>}
  {==}

# The letter a shift puts in front (contig index p0 - k - 2).
def SB(+wl: U32, +wt: AT.Tree<U32>, +p0: U32, +offu: U32, +k: U32) -> B.Base:
  Q.bf(C.AT(wl, wt, ((((p0 - k : U32) - 2 : U32) - offu : U32))))

law u_nat:
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  {Q.n(((((p0 - k : U32) - 2 : U32) - offu : U32))) == Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu)) : Nat}

def u_nat(p0, offu, k, hk0, hS, hH):
  +np = Q.n(p0)
  +nk = Q.n(k)
  +u1 = (p0 - k : U32)
  +u2 = (u1 - 2 : U32)
  +E1 = TL.u_sub(p0, k, hk0)
  +E2 = TL.u_sub(u1, 2,
    %Equal.sym(Nat, Q.n(u1), Nat.sub(np, nk), E1) : {Nat.is_le(2n, _) == True{} : Bool}
    hS)
  +E3 = TL.u_sub(u2, offu,
    %Equal.sym(Nat, Q.n(u2), Nat.sub(Q.n(u1), 2n), E2) : {Nat.is_le(Q.n(offu), _) == True{} : Bool}
    %Equal.sym(Nat, Q.n(u1), Nat.sub(np, nk), E1) : {Nat.is_le(Q.n(offu), Nat.sub(_, 2n)) == True{} : Bool}
    hH)
  %Equal.sym(Nat, Q.n((u2 - offu : U32)), Nat.sub(Q.n(u2), Q.n(offu)), E3) : {_ == Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu)) : Nat}
  %Equal.sym(Nat, Q.n(u2), Nat.sub(Q.n(u1), 2n), E2) : {Nat.sub(_, Q.n(offu)) == Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu)) : Nat}
  %Equal.sym(Nat, Q.n(u1), Nat.sub(np, nk), E1) : {Nat.sub(Nat.sub(_, 2n), Q.n(offu)) == Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu)) : Nat}
  {==}

law win_at:
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {List.get(&2, U32, Q.xs(wl, wt), Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu))) == Some{C.AT(wl, wt, ((((p0 - k : U32) - 2 : U32) - offu : U32)))} : Maybe<&2, U32>}

def win_at(wl, wt, wd, p0, offu, k, hw, hk0, hS, hH, ho):
  +u = ((((p0 - k : U32) - 2 : U32) - offu : U32))
  +AW = {Some{C.AT(wl, wt, u)} : Maybe<&2, U32>}
  +Eu = u_nat(p0, offu, k, hk0, hS, hH)
  %Eu : {List.get(&2, U32, Q.xs(wl, wt), _) == AW : Maybe<&2, U32>}
  Equal.sym(Maybe<&2, U32>, AW, List.get(&2, U32, Q.xs(wl, wt), Q.n(u)),
    C.at_view_t(wl, wt, wd, u, C.ok_full(wl, wt, wd, hw), C.ok_d(wl, wt, wd, hw), C.ok_len(wl, wt, wd, hw),
      %Equal.sym(Nat, Q.n(u), Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu)), Eu) : {Nat.is_lt(_, Q.n(wl)) == True{} : Bool}
      TN.sh_lt(Q.n(p0), Q.n(k), Q.n(offu), Q.n(wl), hS, hH, ho)))

# tan.bend reads the shift's letter through the window.
law win_sb:
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hk0: {Nat.is_le(Q.n(k), Q.n(p0)) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {V.Win.get(Q.n(offu), Q.BF(Q.xs(wl, wt)), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == Some{SB(wl, wt, p0, offu, k)} : Maybe<&2, B.Base>}

def win_sb(wl, wt, wd, p0, offu, k, hw, hk0, hS, hH, ho):
  +ws = Q.xs(wl, wt)
  +i = Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)
  +o = Q.n(offu)
  +RB = {Some{SB(wl, wt, p0, offu, k)} : Maybe<&2, B.Base>}
  %Equal.sym(Bool, Nat.is_lt(i, o), False{}, N.le_not_lt(o, i, hH)) : {V.Win.get.if(_, Q.BF(ws), o, i) == RB : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, B.Base>, List.get(&2, B.Base, Q.BF(ws), Nat.sub(i, o)), TL.MB(List.get(&2, U32, ws, Nat.sub(i, o))), TL.bf_get(ws, Nat.sub(i, o))) :
    {_ == RB : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, ws, Nat.sub(i, o)), Some{C.AT(wl, wt, ((((p0 - k : U32) - 2 : U32) - offu : U32)))}, win_at(wl, wt, wd, p0, offu, k, hw, hk0, hS, hH, ho)) :
    {TL.MB(_) == RB : Maybe<&2, B.Base>}
  {==}

law alk_shift:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +a: NX.Ap
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +tr: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +htr: {Nat.is_lt(Q.n(tr), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  for +hS: {Nat.is_le(2n, Nat.sub(Q.n(p0), Q.n(k))) == True{} : Bool}
  for +hH: {Nat.is_le(Q.n(offu), Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n)) == True{} : Bool}
  {{SB(wl, wt, p0, offu, k) <> V.init(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, 0n))) : List<&2, B.Base>} == Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, (k + 1 : U32), tr, 0n)) : List<&2, B.Base>}

def alk_shift(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho, htr, hS, hH):
  +X = TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)
  +l = Q.n(NX.Ap.ln(a))
  +m = Nat.sub(l, Q.n(tr))
  +T = List.take(&2, U32, X, m)
  +np = Q.n(p0)
  +nk = Q.n(k)
  +o = Q.n(offu)
  +ws = Q.xs(wl, wt)
  +S = Q.SL(Q.xs(bl, bt), a)
  +k1 = (k + 1 : U32)
  +w0 = C.AT(wl, wt, ((((p0 - k : U32) - 2 : U32) - offu : U32)))
  +i0 = Nat.sub(Nat.sub(Nat.sub(Q.n(p0), Q.n(k)), 2n), Q.n(offu))
  +h1 = TL.le_sub(Q.n(tr), 1n, l, TL.lt_succ_le(Q.n(tr), l, htr))
  +hk0 = TN.kok_le(nk, o, np, hk)
  +LH = {SB(wl, wt, p0, offu, k) <> Q.BF(List.take(&2, U32, X, Nat.sub(m, 1n))) : List<&2, B.Base>}
  +X1 = List.append(&2, U32, Q.RK(ws, p0, offu, k1), S)
  %Equal.sym(List<&2, B.Base>, V.init(Q.BF(List.drop(&2, U32, T, 0n))), Q.BF(List.take(&2, U32, X, Nat.sub(m, 1n))), init_core(X, m, m_le(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho))) :
    {SB(wl, wt, p0, offu, k) <> _ == Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k1, tr, 0n)) : List<&2, B.Base>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.take(&2, U32, X1, m), 0n), List.take(&2, U32, X1, m), TL.drop_zero(List.take(&2, U32, X1, m))) :
    {LH == Q.BF(_) : List<&2, B.Base>}
  %Equal.sym(Nat, Q.n(k1), Nat.add(nk, 1n), TL.u_inc(k, p0, TN.kok_lt(nk, o, np, hk))) :
    {LH == Q.BF(List.take(&2, U32, List.append(&2, U32, List.take(&2, U32, List.drop(&2, U32, ws, Nat.sub(Nat.sub(Nat.sub(np, 1n), _), o)), _), S), m)) : List<&2, B.Base>}
  %Equal.sym(Nat, Nat.sub(Nat.sub(Nat.sub(np, 1n), Nat.add(nk, 1n)), o), i0, TN.sh_b0(np, nk, o)) :
    {LH == Q.BF(List.take(&2, U32, List.append(&2, U32, List.take(&2, U32, List.drop(&2, U32, ws, _), Nat.add(nk, 1n)), S), m)) : List<&2, B.Base>}
  %Equal.sym(Nat, Nat.add(nk, 1n), 1n+nk, N.add_one(nk)) :
    {LH == Q.BF(List.take(&2, U32, List.append(&2, U32, List.take(&2, U32, List.drop(&2, U32, ws, i0), _), S), m)) : List<&2, B.Base>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, ws, i0), 1n+nk), w0 <> List.take(&2, U32, List.drop(&2, U32, ws, Nat.add(i0, 1n)), nk),
      TL.slice_cons(ws, i0, nk, w0, win_at(wl, wt, wd, p0, offu, k, hw, hk0, hS, hH, ho))) :
    {LH == Q.BF(List.take(&2, U32, List.append(&2, U32, _, S), m)) : List<&2, B.Base>}
  %Equal.sym(Nat, Nat.add(i0, 1n), Nat.sub(Nat.sub(Nat.sub(np, 1n), nk), o), TN.sh_b1(np, nk, o, hS, hH)) :
    {LH == Q.BF(List.take(&2, U32, List.append(&2, U32, w0 <> List.take(&2, U32, List.drop(&2, U32, ws, _), nk), S), m)) : List<&2, B.Base>}
  %VL.succ_sub_one(m, h1) : {LH == Q.BF(List.take(&2, U32, w0 <> X, _)) : List<&2, B.Base>}
  {==}
