import Base
import ./norm_split.bend as NS
import ./proof_s_w.bend as W
import ./proof_b_rundefs.bend as RD
import ./proof_s_scan.bend as SC
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_shift.bend as SH
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# The records' buffer check (norm_split.bend's out.ck): the buffer comes
# back (Some) only when it holds n LFs and, unless the terminator is CR LF,
# no CR. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# The buffer holds n LFs, and no CR unless cr.
def CK(+l2: U32, +t2: AT.Tree<U32>, +k: Nat, +cr: Bool) -> Type:
  {FD.count(W.V(l2, t2), 10) == k : Nat} & {(cr || Nat.is_eq(FD.count(W.V(l2, t2), 13), 0n)) == True{} : Bool}

def CKB(+b: Bool, +len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, -out: NS.Ans, +k: Nat, +cr: Bool) -> Type:
  match b:
    case True{}:
      {out == NS.Out{C.BT(len, t), Some{C.BT(l2, t2)}} : NS.Ans} & CK(l2, t2, k, cr)
    case False{}:
      {out == NS.Out{C.BT(len, t), None{}} : NS.Ans}

def CKR(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, -out: NS.Ans, +k: Nat, +cr: Bool) -> Type:
  &b: Bool -> CKB(b, len, t, l2, t2, out, k, cr)

def drop0(xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, r}:
      {==}

# The whole buffer's bytes.
def bs_all(+l2: U32, +t2: AT.Tree<U32>, +hok: {W.OK(l2, t2) == True{} : Bool}) -> {SC.BS(l2, t2, 0, l2) == W.V(l2, t2) : List<&2, U32>}:
  +V = W.V(l2, t2)
  %Equal.sym(Nat, Nat.sub(n(l2), 0n), n(l2), N.sub_zero(n(l2))) : {D.slice(V, 0n, _) == V : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, drop0(V)) : {List.take(&2, U32, _, n(l2)) == V : List<&2, U32>}
  SH.take_all(V, n(l2), {%Equal.sym(Nat, List.length(&2, U32, V), D.size(C.BT(l2, t2)), O.view_size_t(l2, t2, RD.tdepth(t2), hok)) : {Nat.is_le(_, n(l2)) == True{} : Bool}; N.le_refl(n(l2)) : {Nat.is_le(List.length(&2, U32, V), n(l2)) == True{} : Bool}})

# The count over the whole buffer.
def CNTV(+l2: U32, +t2: AT.Tree<U32>, +c: U32, -r: D.Bytes & Nat) -> Type:
  &k: Nat -> ({r == (C.BT(l2, t2), k) : D.Bytes & Nat} & {k == FD.count(W.V(l2, t2), c) : Nat})

def cnt_all.k(+l2: U32, +t2: AT.Tree<U32>, +c: U32, +hok: {W.OK(l2, t2) == True{} : Bool},
  r: SC.CNT(l2, t2, 0n, 0, l2, c, NS.count(C.BT(l2, t2), NS.Rg{0, l2}, c))) -> CNTV(l2, t2, c, NS.count(C.BT(l2, t2), NS.Rg{0, l2}, c)):
  (+k, q) = r
  (e, ek) = q
  (k, (e, Equal.trans(Nat, k, FD.count(SC.BS(l2, t2, 0, l2), c), FD.count(W.V(l2, t2), c), SC.cnt_val(l2, t2, 0, l2, c, k, ek),
    Equal.cong(List<&2, U32>, Nat, xs => FD.count(xs, c), SC.BS(l2, t2, 0, l2), W.V(l2, t2), bs_all(l2, t2, hok)))))

def cnt_all(+l2: U32, +t2: AT.Tree<U32>, +c: U32, +hok: {W.OK(l2, t2) == True{} : Bool}, +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  CNTV(l2, t2, c, NS.count(C.BT(l2, t2), NS.Rg{0, l2}, c)):
  cnt_all.k(l2, t2, c, hok, SC.count_t(l2, t2, RD.tdepth(t2), 0, l2, c, hok, N.le_zero_l(n(l2)), N.le_refl(n(l2)), hc))

# No CR (the terminator is LF alone).
def nocr.c(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +k: Nat, +h10: {FD.count(W.V(l2, t2), 10) == k : Nat},
  +k3: Nat, +e3: {k3 == FD.count(W.V(l2, t2), 13) : Nat}, +c: Bool, +e: {Nat.is_eq(k3, 0n) == c : Bool}) ->
  CKR(len, t, l2, t2, NS.out.if(c, C.BT(len, t), C.BT(l2, t2)), k, False{}):
  match c:
    case True{}:
      (True{}, ({==}, (h10, {%e3 : {Nat.is_eq(_, 0n) == True{} : Bool}; e : {Nat.is_eq(FD.count(W.V(l2, t2), 13), 0n) == True{} : Bool}})))
    case False{}:
      (False{}, {==})

def nocr.k(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +k: Nat, +h10: {FD.count(W.V(l2, t2), 10) == k : Nat},
  -r: D.Bytes & Nat, c3: CNTV(l2, t2, 13, r)) -> CKR(len, t, l2, t2, NS.out.cr(C.BT(len, t), r), k, False{}):
  (+k3, q) = c3
  (ec, e3) = q
  %Equal.sym(D.Bytes & Nat, r, (C.BT(l2, t2), k3), ec) : CKR(len, t, l2, t2, NS.out.cr(C.BT(len, t), _), k, False{})
  nocr.c(len, t, l2, t2, k, h10, k3, e3, Nat.is_eq(k3, 0n), {==})

def lf.t(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +hok: {W.OK(l2, t2) == True{} : Bool}, +k: Nat,
  +h10: {FD.count(W.V(l2, t2), 10) == k : Nat}, +crf: Bool) ->
  CKR(len, t, l2, t2, NS.out.lf.if(True{}, crf, C.BT(len, t), C.BT(l2, t2), l2), k, crf):
  match crf:
    case True{}:
      (True{}, ({==}, (h10, {==})))
    case False{}:
      nocr.k(len, t, l2, t2, k, h10, NS.count(C.BT(l2, t2), NS.Rg{0, l2}, 13), cnt_all(l2, t2, 13, hok, {==}))

def lf.c(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +hok: {W.OK(l2, t2) == True{} : Bool}, +k: Nat, +crf: Bool,
  +k2: Nat, +e2: {k2 == FD.count(W.V(l2, t2), 10) : Nat}, +c: Bool, +e: {Nat.is_eq(k2, k) == c : Bool}) ->
  CKR(len, t, l2, t2, NS.out.lf.if(c, crf, C.BT(len, t), C.BT(l2, t2), l2), k, crf):
  match c:
    case False{}:
      (False{}, {==})
    case True{}:
      lf.t(len, t, l2, t2, hok, k, Equal.trans(Nat, FD.count(W.V(l2, t2), 10), k2, k, Equal.sym(Nat, k2, FD.count(W.V(l2, t2), 10), e2), N.eq_sound(k2, k, e)), crf)

def ck.k(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +hok: {W.OK(l2, t2) == True{} : Bool}, +k: Nat, +crf: Bool,
  -r: D.Bytes & Nat, c2: CNTV(l2, t2, 10, r)) -> CKR(len, t, l2, t2, NS.out.lf(k, crf, C.BT(len, t), r, l2), k, crf):
  (+k2, q) = c2
  (ec, e2) = q
  %Equal.sym(D.Bytes & Nat, r, (C.BT(l2, t2), k2), ec) : CKR(len, t, l2, t2, NS.out.lf(k, crf, C.BT(len, t), _, l2), k, crf)
  lf.c(len, t, l2, t2, hok, k, crf, k2, e2, Nat.is_eq(k2, k), {==})

# out.ck on a buffer with its flag set: the buffer back with the check, or None.
law ck_t:
  for +len: U32
  for +t: AT.Tree<U32>
  for +l2: U32
  for +t2: AT.Tree<U32>
  for +p: NS.Rg
  for +k: Nat
  for +cr: Bool
  for +hok: {W.OK(l2, t2) == True{} : Bool}
  CKR(len, t, l2, t2, NS.out.ck(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, True{}}, k, cr), k, cr)

def ck_t(len, t, l2, t2, p, k, cr, hok):
  ck.k(len, t, l2, t2, hok, k, cr, NS.count(C.BT(l2, t2), NS.Rg{0, l2}, 10), cnt_all(l2, t2, 10, hok, {==}))
