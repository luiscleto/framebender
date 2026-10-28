import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_let.bend as L
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import ./proof_b_cut_nat.bend as Z
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_find.bend as PF
import ../lawful-bytes/proof_same.bend as PSm
import ../lawful-bytes/proof_seq.bend as SQ
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# The rewrite path's small byte loops (lets, feq, dis.go) on the mirror,
# described by list functions of the view: the letters test is Q.lets and
# L.UPA of the slice, feq is B.Bases.eq of the bases, dis.go is "not a
# member" of the earlier alleles' bases.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# Stepping through a range that fits
# ---------------------------------------------------------------------------

def lt_of(+a: Nat, +k: Nat, +bl: Nat, +h: {Nat.is_le(Nat.add(a, 1n+k), bl) == True{} : Bool}) -> {Nat.is_lt(a, bl) == True{} : Bool}:
  +h2 = AB.subst(Nat, z => {Nat.is_le(z, bl) == True{} : Bool}, Nat.add(a, 1n+k), 1n+Nat.add(a, k), N.add_succ(a, k), h)
  +h3 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, k), bl), Nat.is_le(1n+Nat.add(a, k), bl), True{}, Equal.sym(Bool, Nat.is_le(1n+Nat.add(a, k), bl), Nat.is_lt(Nat.add(a, k), bl), N.le_succ_lt(Nat.add(a, k), bl)), h2)
  N.le_lt_trans(a, Nat.add(a, k), bl, N.le_add_r(a, k), h3)

def inc_of(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(n(j), 1n+k), n(len)) == True{} : Bool}) -> {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat}:
  C.inc_fits(j, d, C.ok_d(len, t, d, h), PF.step_lt4(len, t, d, j, h, lt_of(n(j), k, n(len), hj)))

def nx_of(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(n(j), 1n+k), n(len)) == True{} : Bool}) -> {Nat.is_le(Nat.add(n((j + 1 : U32)), k), n(len)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(Nat.add(z, k), n(len)) == True{} : Bool}, Nat.add(n(j), 1n), n((j + 1 : U32)), Equal.sym(Nat, n((j + 1 : U32)), Nat.add(n(j), 1n), inc_of(len, t, d, j, k, h, hj)),
    AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, Nat.add(n(j), 1n+k), Nat.add(Nat.add(n(j), 1n), k), Equal.sym(Nat, Nat.add(Nat.add(n(j), 1n), k), Nat.add(n(j), 1n+k), N.add_assoc(n(j), 1n, k)), hj))

def get_of(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +k: Nat, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(n(j), 1n+k), n(len)) == True{} : Bool}) -> {List.get(&2, U32, Q.xs(len, t), n(j)) == Some{C.AT(len, t, j)} : Maybe<&2, U32>}:
  PF.step_get(len, t, d, j, h, lt_of(n(j), k, n(len), hj))

# ---------------------------------------------------------------------------
# lets
# ---------------------------------------------------------------------------

def LGV(+len: U32, +t: AT.Tree<U32>, +j: U32, +m: Nat, ok: Bool, up: Bool) -> P.L2:
  P.L2{Bool.and(ok, Q.lets(D.slice(Q.xs(len, t), n(j), m))), Bool.and(up, L.UPA(D.slice(Q.xs(len, t), n(j), m)))}

def lg_v(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +ok: Bool, +up: Bool,
  +hj: {Nat.is_le(Nat.add(n(j), m), n(len)) == True{} : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {P.LG(m, len, t, C.AT(len, t, j), j, ok, up) == LGV(len, t, j, m, ok, up) : P.L2}:
  match m:
    case 0n:
      +Lz = List.drop(&2, U32, Q.xs(len, t), n(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Lz, 0n), Nil{}, SQ.take_zero(Lz)) :
        {P.L2{ok, up} == P.L2{Bool.and(ok, Q.lets(_)), Bool.and(up, L.UPA(_))} : P.L2}
      %Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok)) : {P.L2{ok, up} == P.L2{_, Bool.and(up, True{})} : P.L2}
      %Equal.sym(Bool, Bool.and(up, True{}), up, LS.and_true(up)) : {P.L2{ok, up} == P.L2{ok, _} : P.L2}
      {==}
    case 1n+k:
      +VW = Q.xs(len, t)
      +y = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +S1 = D.slice(VW, n(j1), k)
      +ok1 = Bool.and(ok, NX.isl(y))
      +up1 = Bool.and(up, U32.is_lt(y, 97))
      %Equal.sym(List<&2, U32>, D.slice(VW, n(j), 1n+k), y <> D.slice(VW, Nat.add(n(j), 1n), k), PSm.slice_cons(VW, n(j), k, y, get_of(len, t, d, j, k, h, hj))) :
        {P.LG(k, len, t, C.AT(len, t, j1), j1, ok1, up1) == P.L2{Bool.and(ok, Q.lets(_)), Bool.and(up, L.UPA(_))} : P.L2}
      %inc_of(len, t, d, j, k, h, hj) :
        {P.LG(k, len, t, C.AT(len, t, j1), j1, ok1, up1) == P.L2{Bool.and(ok, Bool.and(NX.isl(y), Q.lets(D.slice(VW, _, k)))), Bool.and(up, Bool.and(U32.is_lt(y, 97), L.UPA(D.slice(VW, _, k))))} : P.L2}
      %LS.and_assoc(ok, NX.isl(y), Q.lets(S1)) :
        {P.LG(k, len, t, C.AT(len, t, j1), j1, ok1, up1) == P.L2{_, Bool.and(up, Bool.and(U32.is_lt(y, 97), L.UPA(S1)))} : P.L2}
      %LS.and_assoc(up, U32.is_lt(y, 97), L.UPA(S1)) :
        {P.LG(k, len, t, C.AT(len, t, j1), j1, ok1, up1) == P.L2{Bool.and(ok1, Q.lets(S1)), _} : P.L2}
      lg_v(k, len, t, d, j1, ok1, up1, nx_of(len, t, d, j, k, h, hj), h)

# Bytes a .. c-1: the letters test, and all upper case.
def lets_v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {P.LETS(len, t, a, c) == P.L2{Q.lets(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))), L.UPA(D.slice(Q.xs(len, t), n(a), n((c - a : U32))))} : P.L2}:
  +hs = LP.sub_u(c, a, hac)
  +hj = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(c), Nat.add(n(a), n((c - a : U32))),
    Equal.sym(Nat, Nat.add(n(a), n((c - a : U32))), n(c), Equal.trans(Nat, Nat.add(n(a), n((c - a : U32))), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
      Equal.cong(Nat, Nat, z => Nat.add(n(a), z), n((c - a : U32)), Nat.sub(n(c), n(a)), hs), N.le_sub_add(n(a), n(c), hac))), hcl)
  lg_v(n((c - a : U32)), len, t, d, a, True{}, True{}, hj, h)

# ---------------------------------------------------------------------------
# feq
# ---------------------------------------------------------------------------

def FGV(+len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +m: Nat, acc: Bool) -> Bool:
  Bool.and(acc, L.FL(D.slice(Q.xs(len, t), n(i), m), D.slice(Q.xs(len, t), n(j), m)))

def fg_v(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +i: U32, +j: U32, +acc: Bool,
  +hi: {Nat.is_le(Nat.add(n(i), m), n(len)) == True{} : Bool},
  +hj: {Nat.is_le(Nat.add(n(j), m), n(len)) == True{} : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {P.FG(m, len, t, C.AT(len, t, i), C.AT(len, t, j), i, j, acc) == FGV(len, t, i, j, m, acc) : Bool}:
  match m:
    case 0n:
      +Li = List.drop(&2, U32, Q.xs(len, t), n(i))
      +Lj = List.drop(&2, U32, Q.xs(len, t), n(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Li, 0n), Nil{}, SQ.take_zero(Li)) : {acc == Bool.and(acc, L.FL(_, List.take(&2, U32, Lj, 0n))) : Bool}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Lj, 0n), Nil{}, SQ.take_zero(Lj)) : {acc == Bool.and(acc, L.FL(Nil{}, _)) : Bool}
      Equal.sym(Bool, Bool.and(acc, True{}), acc, LS.and_true(acc))
    case 1n+k:
      +VW = Q.xs(len, t)
      +x = C.AT(len, t, i)
      +y = C.AT(len, t, j)
      +i1 = (i + 1 : U32)
      +j1 = (j + 1 : U32)
      +z = U32.is_zero(((x .^. y : U32) .&. 223 : U32))
      +Si = D.slice(VW, n(i1), k)
      +Sj = D.slice(VW, n(j1), k)
      +acc1 = Bool.and(acc, z)
      %Equal.sym(List<&2, U32>, D.slice(VW, n(i), 1n+k), x <> D.slice(VW, Nat.add(n(i), 1n), k), PSm.slice_cons(VW, n(i), k, x, get_of(len, t, d, i, k, h, hi))) :
        {P.FG(k, len, t, C.AT(len, t, i1), C.AT(len, t, j1), i1, j1, acc1) == Bool.and(acc, L.FL(_, D.slice(VW, n(j), 1n+k))) : Bool}
      %Equal.sym(List<&2, U32>, D.slice(VW, n(j), 1n+k), y <> D.slice(VW, Nat.add(n(j), 1n), k), PSm.slice_cons(VW, n(j), k, y, get_of(len, t, d, j, k, h, hj))) :
        {P.FG(k, len, t, C.AT(len, t, i1), C.AT(len, t, j1), i1, j1, acc1) == Bool.and(acc, L.FL(x <> D.slice(VW, Nat.add(n(i), 1n), k), _)) : Bool}
      %inc_of(len, t, d, i, k, h, hi) :
        {P.FG(k, len, t, C.AT(len, t, i1), C.AT(len, t, j1), i1, j1, acc1) == Bool.and(acc, Bool.and(z, L.FL(D.slice(VW, _, k), D.slice(VW, Nat.add(n(j), 1n), k)))) : Bool}
      %inc_of(len, t, d, j, k, h, hj) :
        {P.FG(k, len, t, C.AT(len, t, i1), C.AT(len, t, j1), i1, j1, acc1) == Bool.and(acc, Bool.and(z, L.FL(Si, D.slice(VW, _, k)))) : Bool}
      %LS.and_assoc(acc, z, L.FL(Si, Sj)) :
        {P.FG(k, len, t, C.AT(len, t, i1), C.AT(len, t, j1), i1, j1, acc1) == _ : Bool}
      fg_v(k, len, t, d, i1, j1, acc1, nx_of(len, t, d, i, k, h, hi), nx_of(len, t, d, j, k, h, hj), h)

def bf_len(+ys: List<&2, U32>) -> {List.length(&2, B.Base, Q.BF(ys)) == List.length(&2, U32, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %Equal.sym(Nat, List.length(&2, B.Base, Q.BF(yt)), List.length(&2, U32, yt), bf_len(yt)) : {1n+_ == 1n+List.length(&2, U32, yt) : Nat}
      {==}

# Base lists of different lengths are not equal.
def beq_len(+a: List<&2, B.Base>, +b: List<&2, B.Base>, +h: {Nat.is_eq(List.length(&2, B.Base, a), List.length(&2, B.Base, b)) == False{} : Bool}) ->
  {B.Bases.eq(a, b) == False{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      Empty.absurd({True{} == False{} : Bool}, LS.ft(Equal.sym(Bool, True{}, False{}, h)))
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      {==}
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, B.Bases.eq(xt, yt), False{}, beq_len(xt, yt, h)) : {Bool.and(B.Base.is_eq(x, y), _) == False{} : Bool}
      N.and_false_r(B.Base.is_eq(x, y))

# An allele inside the buffer.
def INB(+len: U32, +a: NX.Ap) -> Bool:
  Nat.is_le(Nat.add(n(NX.Ap.st(a)), n(NX.Ap.ln(a))), n(len))

def feq_k(+b: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +sx: U32, +ax: U32, +sp: U32, +ap: U32, +hb: {U32.is_eq(ax, ap) == b : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {Nat.is_le(Nat.add(n(sx), n(ax)), n(len)) == True{} : Bool}, +hp: {Nat.is_le(Nat.add(n(sp), n(ap)), n(len)) == True{} : Bool},
  +lx: {Q.lets(D.slice(Q.xs(len, t), n(sx), n(ax))) == True{} : Bool}, +lp: {Q.lets(D.slice(Q.xs(len, t), n(sp), n(ap))) == True{} : Bool}) ->
  {P.FQI(b, len, t, sx, sp, ax) == B.Bases.eq(Q.BF(D.slice(Q.xs(len, t), n(sx), n(ax))), Q.BF(D.slice(Q.xs(len, t), n(sp), n(ap)))) : Bool}:
  match b:
    case True{}:
      +e = U.is_eq_true(ax, ap, hb)
      +Sx = D.slice(Q.xs(len, t), n(sx), n(ax))
      +Sp = D.slice(Q.xs(len, t), n(sp), n(ax))
      +hp2 = AB.subst(U32, z => {Nat.is_le(Nat.add(n(sp), n(z)), n(len)) == True{} : Bool}, ap, ax, Equal.sym(U32, ax, ap, e), hp)
      +lp2 = AB.subst(U32, z => {Q.lets(D.slice(Q.xs(len, t), n(sp), n(z))) == True{} : Bool}, ap, ax, Equal.sym(U32, ax, ap, e), lp)
      %e : {P.FG(n(ax), len, t, C.AT(len, t, sx), C.AT(len, t, sp), sx, sp, True{}) == B.Bases.eq(Q.BF(Sx), Q.BF(D.slice(Q.xs(len, t), n(sp), n(_)))) : Bool}
      Equal.trans(Bool, P.FG(n(ax), len, t, C.AT(len, t, sx), C.AT(len, t, sp), sx, sp, True{}), L.FL(Sx, Sp), B.Bases.eq(Q.BF(Sx), Q.BF(Sp)),
        fg_v(n(ax), len, t, d, sx, sp, True{}, hx, hp2, h), Equal.sym(Bool, B.Bases.eq(Q.BF(Sx), Q.BF(Sp)), L.FL(Sx, Sp), L.fl_beq(Sx, Sp, lx, lp2)))
    case False{}:
      +Sx = D.slice(Q.xs(len, t), n(sx), n(ax))
      +Sp = D.slice(Q.xs(len, t), n(sp), n(ap))
      +hL = LP.len_x(len, t, d, h)
      +ex = Equal.trans(Nat, List.length(&2, B.Base, Q.BF(Sx)), List.length(&2, U32, Sx), n(ax), bf_len(Sx), LP.slice_len(Q.xs(len, t), n(sx), n(ax), AB.subst(Nat, z => {Nat.is_le(Nat.add(n(sx), n(ax)), z) == True{} : Bool}, n(len), List.length(&2, U32, Q.xs(len, t)), hL, hx)))
      +ep = Equal.trans(Nat, List.length(&2, B.Base, Q.BF(Sp)), List.length(&2, U32, Sp), n(ap), bf_len(Sp), LP.slice_len(Q.xs(len, t), n(sp), n(ap), AB.subst(Nat, z => {Nat.is_le(Nat.add(n(sp), n(ap)), z) == True{} : Bool}, n(len), List.length(&2, U32, Q.xs(len, t)), hL, hp)))
      +hne = Z.une(ax, ap, hb)
      Equal.sym(Bool, B.Bases.eq(Q.BF(Sx), Q.BF(Sp)), False{}, beq_len(Q.BF(Sx), Q.BF(Sp),
        AB.subst(Nat, z => {Nat.is_eq(z, List.length(&2, B.Base, Q.BF(Sp))) == False{} : Bool}, n(ax), List.length(&2, B.Base, Q.BF(Sx)), Equal.sym(Nat, List.length(&2, B.Base, Q.BF(Sx)), n(ax), ex),
          AB.subst(Nat, z => {Nat.is_eq(n(ax), z) == False{} : Bool}, n(ap), List.length(&2, B.Base, Q.BF(Sp)), Equal.sym(Nat, List.length(&2, B.Base, Q.BF(Sp)), n(ap), ep), hne))))

def feq_v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NX.Ap, +p: NX.Ap, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {INB(len, x) == True{} : Bool}, +hp: {INB(len, p) == True{} : Bool},
  +lx: {Q.lets(Q.SL(Q.xs(len, t), x)) == True{} : Bool}, +lp: {Q.lets(Q.SL(Q.xs(len, t), p)) == True{} : Bool}) ->
  {P.FEQ(len, t, x, p) == B.Bases.eq(Q.BF(Q.SL(Q.xs(len, t), x)), Q.BF(Q.SL(Q.xs(len, t), p))) : Bool}:
  match x p:
    case NX.Ap{+sx, +ax} NX.Ap{+sp, +ap}:
      feq_k(U32.is_eq(ax, ap), len, t, d, sx, ax, sp, ap, {==}, h, hx, hp, lx, lp)

def nor(+a: Bool, +b: Bool) -> {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bfx(+len: U32, +t: AT.Tree<U32>, +x: NX.Ap) -> List<&2, B.Base>:
  Q.BF(Q.SL(Q.xs(len, t), x))

def dok(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NX.Ap, +p: NX.Ap, +m: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {INB(len, x) == True{} : Bool}, +hp: {INB(len, p) == True{} : Bool},
  +lx: {Q.lets(Q.SL(Q.xs(len, t), x)) == True{} : Bool}, +lp: {Q.lets(Q.SL(Q.xs(len, t), p)) == True{} : Bool}) ->
  {Bool.and(P.DO(ok, len, t, x, p), Bool.not(m)) == Bool.and(ok, Bool.not(Bool.or(B.Bases.eq(bfx(len, t, x), bfx(len, t, p)), m))) : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.FEQ(len, t, x, p), B.Bases.eq(bfx(len, t, x), bfx(len, t, p)), feq_v(len, t, d, x, p, h, hx, hp, lx, lp)) :
        {Bool.and(Bool.not(_), Bool.not(m)) == Bool.not(Bool.or(B.Bases.eq(bfx(len, t, x), bfx(len, t, p)), m)) : Bool}
      nor(B.Bases.eq(bfx(len, t, x), bfx(len, t, p)), m)
    case False{}:
      {==}

# Every allele of ps inside the buffer, with letters only.
def GD(+len: U32, +t: AT.Tree<U32>, ps: List<&2, NX.Ap>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> q:
      Bool.and(Bool.and(INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p))), GD(len, t, q))

def dg_m(+ps: List<&2, NX.Ap>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +ok: Bool, +x: NX.Ap, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hx: {INB(len, x) == True{} : Bool}, +lx: {Q.lets(Q.SL(Q.xs(len, t), x)) == True{} : Bool}, +hg: {GD(len, t, ps) == True{} : Bool}) ->
  {P.DG(ps, len, t, ok, x) == Bool.and(ok, Bool.not(B.Alleles.member(bfx(len, t, x), Q.BFS(Q.xs(len, t), ps)))) : Bool}:
  match ps:
    case Nil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok))
    case +p <> +q:
      +A = Bool.and(INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p)))
      +hA = LS.and_l(A, GD(len, t, q), hg)
      +hq = LS.and_r(A, GD(len, t, q), hg)
      +m = B.Alleles.member(bfx(len, t, x), Q.BFS(Q.xs(len, t), q))
      Equal.trans(Bool, P.DG(q, len, t, P.DO(ok, len, t, x, p), x), Bool.and(P.DO(ok, len, t, x, p), Bool.not(m)), Bool.and(ok, Bool.not(Bool.or(B.Bases.eq(bfx(len, t, x), bfx(len, t, p)), m))),
        dg_m(q, len, t, d, P.DO(ok, len, t, x, p), x, h, hx, lx, hq),
        dok(ok, len, t, d, x, p, m, h, hx, LS.and_l(INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p)), hA), lx, LS.and_r(INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p)), hA)))
