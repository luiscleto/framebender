import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_num.bend as TN
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C, area "tan": the bytes NX.el reads are the elements of R_k ++ a
# (XA below): byte j < k of it is in the window C.BT(wl, wt), the others in
# the line C.BT(bl, bt). Hypotheses: the buffers are well formed (D.ok), the
# allele lies in the line (hin), R_k lies in the window (hk: k + o + 1 <= p;
# ho: p - 1 <= o + w).

def XA(+ys: List<&2, U32>, +ws: List<&2, U32>, +p0: U32, +offu: U32, +a: NX.Ap, +k: U32) -> List<&2, U32>:
  List.append(&2, U32, Q.RK(ws, p0, offu, k), Q.SL(ys, a))

# R_k's start in the window.
def B0(+p0: U32, +offu: U32, +k: U32) -> Nat:
  Nat.sub(Nat.sub(Nat.sub(Q.n(p0), 1n), Q.n(k)), Q.n(offu))

law len_rk:
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +wd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {List.length(&2, U32, Q.RK(Q.xs(wl, wt), p0, offu, k)) == Q.n(k) : Nat}

def len_rk(wl, wt, wd, p0, offu, k, hw, hk, ho):
  +ws = Q.xs(wl, wt)
  +b0 = B0(p0, offu, k)
  TL.len_take(List.drop(&2, U32, ws, b0), Q.n(k),
    %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, ws, b0)), Nat.sub(List.length(&2, U32, ws), b0), TL.len_drop(ws, b0)) :
      {Nat.is_le(Q.n(k), _) == True{} : Bool}
    %Equal.sym(Nat, List.length(&2, U32, ws), Q.n(wl), O.view_size_t(wl, wt, wd, hw)) :
      {Nat.is_le(Q.n(k), Nat.sub(_, b0)) == True{} : Bool}
    TL.le_sub(b0, Q.n(k), Q.n(wl), TN.wk8(Q.n(k), Q.n(offu), Q.n(p0), Q.n(wl), hk, ho)))

law len_sl:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +a: NX.Ap
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  {List.length(&2, U32, Q.SL(Q.xs(bl, bt), a)) == Q.n(NX.Ap.ln(a)) : Nat}

def len_sl(bl, bt, bd, a, hb, hin):
  +ys = Q.xs(bl, bt)
  +s = Q.n(NX.Ap.st(a))
  +l = Q.n(NX.Ap.ln(a))
  TL.len_take(List.drop(&2, U32, ys, s), l,
    %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, ys, s)), Nat.sub(List.length(&2, U32, ys), s), TL.len_drop(ys, s)) :
      {Nat.is_le(l, _) == True{} : Bool}
    %Equal.sym(Nat, List.length(&2, U32, ys), Q.n(bl), O.view_size_t(bl, bt, bd, hb)) :
      {Nat.is_le(l, Nat.sub(_, s)) == True{} : Bool}
    TL.le_sub(s, l, Q.n(bl), hin))

law len_xa:
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
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  {List.length(&2, U32, XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k)) == Nat.add(Q.n(k), Q.n(NX.Ap.ln(a))) : Nat}

def len_xa(bl, bt, bd, wl, wt, wd, a, p0, offu, k, hb, hw, hin, hk, ho):
  +R = Q.RK(Q.xs(wl, wt), p0, offu, k)
  +S = Q.SL(Q.xs(bl, bt), a)
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, R, S)), Nat.add(List.length(&2, U32, R), List.length(&2, U32, S)), TL.len_app(R, S)) :
    {_ == Nat.add(Q.n(k), Q.n(NX.Ap.ln(a))) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, R), Q.n(k), len_rk(wl, wt, wd, p0, offu, k, hw, hk, ho)) :
    {Nat.add(_, List.length(&2, U32, S)) == Nat.add(Q.n(k), Q.n(NX.Ap.ln(a))) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, S), Q.n(NX.Ap.ln(a)), len_sl(bl, bt, bd, a, hb, hin)) :
    {Nat.add(Q.n(k), _) == Nat.add(Q.n(k), Q.n(NX.Ap.ln(a))) : Nat}
  {==}

# The window index NX.el reads for byte j < k.
law iw_nat:
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +j: U32
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +hjk: {Nat.is_lt(Q.n(j), Q.n(k)) == True{} : Bool}
  {Q.n(((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32)) == Nat.add(B0(p0, offu, k), Q.n(j)) : Nat}

def iw_nat(p0, offu, k, j, hk, hjk):
  +p = Q.n(p0)
  +nk = Q.n(k)
  +o = Q.n(offu)
  +nj = Q.n(j)
  +u1 = (p0 - 1 : U32)
  +u2 = (u1 - k : U32)
  +u3 = (u2 + j : U32)
  +E1 = TL.u_sub(p0, 1, TN.one_le(nk, o, p, hk))
  +E2 = TL.u_sub(u1, k,
    %Equal.sym(Nat, Q.n(u1), Nat.sub(p, 1n), E1) : {Nat.is_le(nk, _) == True{} : Bool}
    TN.wk2(nk, o, p, hk))
  +E3 = TL.u_add(u2, j, p0,
    %Equal.sym(Nat, Q.n(u2), Nat.sub(Q.n(u1), nk), E2) : {Nat.is_le(Nat.add(_, nj), p) == True{} : Bool}
    %Equal.sym(Nat, Q.n(u1), Nat.sub(p, 1n), E1) : {Nat.is_le(Nat.add(Nat.sub(_, nk), nj), p) == True{} : Bool}
    TN.wk4(nk, o, p, nj, hk, hjk))
  +E4 = TL.u_sub(u3, offu,
    %Equal.sym(Nat, Q.n(u3), Nat.add(Q.n(u2), nj), E3) : {Nat.is_le(o, _) == True{} : Bool}
    %Equal.sym(Nat, Q.n(u2), Nat.sub(Q.n(u1), nk), E2) : {Nat.is_le(o, Nat.add(_, nj)) == True{} : Bool}
    %Equal.sym(Nat, Q.n(u1), Nat.sub(p, 1n), E1) : {Nat.is_le(o, Nat.add(Nat.sub(_, nk), nj)) == True{} : Bool}
    TN.wk5(nk, o, p, nj, hk))
  %Equal.sym(Nat, Q.n((u3 - offu : U32)), Nat.sub(Q.n(u3), o), E4) : {_ == Nat.add(B0(p0, offu, k), nj) : Nat}
  %Equal.sym(Nat, Q.n(u3), Nat.add(Q.n(u2), nj), E3) : {Nat.sub(_, o) == Nat.add(B0(p0, offu, k), nj) : Nat}
  %Equal.sym(Nat, Q.n(u2), Nat.sub(Q.n(u1), nk), E2) : {Nat.sub(Nat.add(_, nj), o) == Nat.add(B0(p0, offu, k), nj) : Nat}
  %Equal.sym(Nat, Q.n(u1), Nat.sub(p, 1n), E1) : {Nat.sub(Nat.add(Nat.sub(_, nk), nj), o) == Nat.add(B0(p0, offu, k), nj) : Nat}
  TN.wk6(nk, o, p, nj, hk)

# The line index NX.el reads for byte j >= k.
law il_nat:
  for +bl: U32
  for +a: NX.Ap
  for +k: U32
  for +j: U32
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hkj: {Nat.is_le(Q.n(k), Q.n(j)) == True{} : Bool}
  for +hj: {Nat.is_lt(Q.n(j), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {Q.n(((NX.Ap.st(a) + j : U32) - k : U32)) == Nat.sub(Nat.add(Q.n(NX.Ap.st(a)), Q.n(j)), Q.n(k)) : Nat}

def il_nat(bl, a, k, j, hin, hkj, hj):
  +s = Q.n(NX.Ap.st(a))
  +nj = Q.n(j)
  +u = (NX.Ap.st(a) + j : U32)
  +E1 = TL.u_add(NX.Ap.st(a), j, bl, TN.ln1(s, Q.n(NX.Ap.ln(a)), Q.n(bl), nj, hin, hj))
  +E2 = TL.u_sub(u, k,
    %Equal.sym(Nat, Q.n(u), Nat.add(s, nj), E1) : {Nat.is_le(Q.n(k), _) == True{} : Bool}
    TN.ln2(s, nj, Q.n(k), hkj))
  %Equal.sym(Nat, Q.n((u - k : U32)), Nat.sub(Q.n(u), Q.n(k)), E2) : {_ == Nat.sub(Nat.add(s, nj), Q.n(k)) : Nat}
  %Equal.sym(Nat, Q.n(u), Nat.add(s, nj), E1) : {Nat.sub(_, Q.n(k)) == Nat.sub(Nat.add(s, nj), Q.n(k)) : Nat}
  {==}

law el_get.w:
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
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hjk: {Nat.is_lt(Q.n(j), Q.n(k)) == True{} : Bool}
  {List.get(&2, U32, XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Q.n(j)) == Some{C.AT(wl, wt, ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32))} : Maybe<&2, U32>}

def el_get.w(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hw, hk, ho, hjk):
  +ws = Q.xs(wl, wt)
  +R = Q.RK(ws, p0, offu, k)
  +S = Q.SL(Q.xs(bl, bt), a)
  +b0 = B0(p0, offu, k)
  +nj = Q.n(j)
  +iw = ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32)
  +AW = {Some{C.AT(wl, wt, iw)} : Maybe<&2, U32>}
  +Ei = iw_nat(p0, offu, k, j, hk, hjk)
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, R, S), nj), List.get(&2, U32, R, nj),
    TL.get_app_l(R, S, nj,
      %Equal.sym(Nat, List.length(&2, U32, R), Q.n(k), len_rk(wl, wt, wd, p0, offu, k, hw, hk, ho)) : {Nat.is_lt(nj, _) == True{} : Bool}
      hjk)) :
    {_ == AW : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, R, nj), List.get(&2, U32, List.drop(&2, U32, ws, b0), nj), TL.get_take(List.drop(&2, U32, ws, b0), Q.n(k), nj, hjk)) :
    {_ == AW : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ws, b0), nj), List.get(&2, U32, ws, Nat.add(b0, nj)), TL.get_drop(ws, b0, nj)) :
    {_ == AW : Maybe<&2, U32>}
  %Ei : {List.get(&2, U32, ws, _) == AW : Maybe<&2, U32>}
  Equal.sym(Maybe<&2, U32>, AW, List.get(&2, U32, ws, Q.n(iw)),
    C.at_view_t(wl, wt, wd, iw, C.ok_full(wl, wt, wd, hw), C.ok_d(wl, wt, wd, hw), C.ok_len(wl, wt, wd, hw),
      %Equal.sym(Nat, Q.n(iw), Nat.add(b0, nj), Ei) : {Nat.is_lt(_, Q.n(wl)) == True{} : Bool}
      TN.wk7(Q.n(k), Q.n(offu), Q.n(p0), Q.n(wl), nj, hk, ho, hjk)))

law el_get.l:
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
  for +hkj: {Nat.is_le(Q.n(k), Q.n(j)) == True{} : Bool}
  for +hj: {Nat.is_lt(Q.n(j), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {List.get(&2, U32, XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Q.n(j)) == Some{C.AT(bl, bt, ((NX.Ap.st(a) + j : U32) - k : U32))} : Maybe<&2, U32>}

def el_get.l(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho, hkj, hj):
  +ys = Q.xs(bl, bt)
  +R = Q.RK(Q.xs(wl, wt), p0, offu, k)
  +S = Q.SL(ys, a)
  +s = Q.n(NX.Ap.st(a))
  +l = Q.n(NX.Ap.ln(a))
  +nk = Q.n(k)
  +nj = Q.n(j)
  +i = Nat.sub(nj, nk)
  +il = ((NX.Ap.st(a) + j : U32) - k : U32)
  +AL = {Some{C.AT(bl, bt, il)} : Maybe<&2, U32>}
  +Ei = il_nat(bl, a, k, j, hin, hkj, hj)
  %N.le_sub_add(nk, nj, hkj) : {List.get(&2, U32, List.append(&2, U32, R, S), _) == AL : Maybe<&2, U32>}
  %len_rk(wl, wt, wd, p0, offu, k, hw, hk, ho) : {List.get(&2, U32, List.append(&2, U32, R, S), Nat.add(_, i)) == AL : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, R, S), Nat.add(List.length(&2, U32, R), i)), List.get(&2, U32, S, i), TL.get_app_r(R, S, i)) :
    {_ == AL : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, S, i), List.get(&2, U32, List.drop(&2, U32, ys, s), i), TL.get_take(List.drop(&2, U32, ys, s), l, i, TN.ln4(l, nj, nk, hj))) :
    {_ == AL : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, s), i), List.get(&2, U32, ys, Nat.add(s, i)), TL.get_drop(ys, s, i)) :
    {_ == AL : Maybe<&2, U32>}
  %TN.ln3(s, nj, nk, hkj) : {List.get(&2, U32, ys, _) == AL : Maybe<&2, U32>}
  %Ei : {List.get(&2, U32, ys, _) == AL : Maybe<&2, U32>}
  Equal.sym(Maybe<&2, U32>, AL, List.get(&2, U32, ys, Q.n(il)),
    C.at_view_t(bl, bt, bd, il, C.ok_full(bl, bt, bd, hb), C.ok_d(bl, bt, bd, hb), C.ok_len(bl, bt, bd, hb),
      %Equal.sym(Nat, Q.n(il), Nat.sub(Nat.add(s, nj), nk), Ei) : {Nat.is_lt(_, Q.n(bl)) == True{} : Bool}
      TN.ln5(s, l, Q.n(bl), nj, nk, hin, hj)))
