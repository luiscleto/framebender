import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_let.bend as L
import ./proof_c_pre_lp.bend as G
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import ./proof_b_alleles_spec.bend as SP
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The ALT loop (NX.alts.go, mirrored by P.XG): when it ends with every
# allele fine, the alleles it adds (XN) are the comma-separated pieces of
# the ALT field, each one or more letters inside it, distinct from each
# other and from the alleles before them, and its up flag says all their
# letters are upper case.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def LL() -> Data:
  List<&2, List<&2, U32>>

def BL() -> Data:
  List<&2, List<&2, B.Base>>

# The next comma (or the field's end e) from a, and the allele before it.
def CC(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> U32:
  M.F1(len, t, a, e, 44)

def AP(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> NX.Ap:
  NX.Ap{a, (CC(len, t, e, a) - a : U32)}

def UP2(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +up: Bool) -> Bool:
  Bool.and(up, P.L2.up(P.LETS(len, t, a, CC(len, t, e, a))))

def OK2(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>) -> Bool:
  Bool.and(Bool.and(P.L2.ok(P.LETS(len, t, a, CC(len, t, e, a))), U32.is_lt(a, CC(len, t, e, a))), P.DG(ps, len, t, True{}, AP(len, t, e, a)))

# The alleles the loop adds, in order.
def XN(k: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, x: P.XD) -> List<&2, NX.Ap>:
  match k x:
    case 0n P.XD{a, ps, ok, up, m}:
      Nil{}
    case 1n+j P.XD{a, ps, ok, up, False{}}:
      Nil{}
    case 1n+j P.XD{+a, +ps, ok, up, True{}}:
      AP(len, t, e, a) <> XN(j, len, t, e, P.XS(len, t, e, a, ps, ok, up))

def xp_rev(+k: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, +x: P.XD) ->
  {P.XD.ps(P.XG(k, len, t, e, x)) == NX.rev_ap(XN(k, len, t, e, x), P.XD.ps(x)) : List<&2, NX.Ap>}:
  match k x:
    case 0n P.XD{+a, +ps, +ok, +up, +m}:
      {==}
    case 1n+j P.XD{+a, +ps, +ok, +up, False{}}:
      {==}
    case 1n+j P.XD{+a, +ps, +ok, +up, True{}}:
      xp_rev(j, len, t, e, P.XS(len, t, e, a, ps, ok, up))

def rr(+ns: List<&2, NX.Ap>, +A: List<&2, NX.Ap>) -> {NX.rev_ap(NX.rev_ap(ns, A), Nil{}) == NX.rev_ap(A, ns) : List<&2, NX.Ap>}:
  match ns:
    case Nil{}:
      {==}
    case +x <> +q:
      rr(q, x <> A)

def xg_false(+k: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool, +m: Bool) ->
  {P.XD.ok(P.XG(k, len, t, e, P.XD{a, ps, False{}, up, m})) == False{} : Bool}:
  match k m:
    case 0n _:
      {==}
    case 1n+j False{}:
      {==}
    case 1n+j True{}:
      xg_false(j, len, t, e, (CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, UP2(len, t, e, a, up), False{})

# ---------------------------------------------------------------------------
# Lists of alleles
# ---------------------------------------------------------------------------

def MSL(+xs: List<&2, U32>, ps: List<&2, NX.Ap>) -> LL():
  match ps:
    case Nil{}:
      Nil{}
    case +p <> q:
      Q.SL(xs, p) <> MSL(xs, q)

def UPS(+xs: List<&2, U32>, ps: List<&2, NX.Ap>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> q:
      Bool.and(L.UPA(Q.SL(xs, p)), UPS(xs, q))

# No allele of E is one of ls.
def NOTIN(E: BL(), +ls: BL()) -> Bool:
  match E:
    case Nil{}:
      True{}
    case +x <> q:
      Bool.and(Bool.not(B.Alleles.member(x, ls)), NOTIN(q, ls))

def notin_nil(+E: BL()) -> {NOTIN(E, Nil{}) == True{} : Bool}:
  match E:
    case Nil{}:
      {==}
    case +x <> +q:
      notin_nil(q)

def notin_cons(+E: BL(), +x: List<&2, B.Base>, +ls: BL(), +h1: {NOTIN(E, ls) == True{} : Bool}, +h2: {B.Alleles.member(x, E) == False{} : Bool}) ->
  {NOTIN(E, x <> ls) == True{} : Bool}:
  match E:
    case Nil{}:
      {==}
    case +y <> +q:
      +hxy = SP.or_f_l(B.Bases.eq(x, y), B.Alleles.member(x, q), h2)
      +hxq = SP.or_f_r(B.Bases.eq(x, y), B.Alleles.member(x, q), h2)
      +A = Bool.not(B.Alleles.member(y, ls))
      +hyl = LS.not_t(B.Alleles.member(y, ls), LS.and_l(A, NOTIN(q, ls), h1))
      +hql = LS.and_r(A, NOTIN(q, ls), h1)
      %Equal.sym(Bool, B.Bases.eq(y, x), False{}, Equal.trans(Bool, B.Bases.eq(y, x), B.Bases.eq(x, y), False{}, L.bases_sym(y, x), hxy)) :
        {Bool.and(Bool.not(Bool.or(_, B.Alleles.member(y, ls))), NOTIN(q, x <> ls)) == True{} : Bool}
      %Equal.sym(Bool, B.Alleles.member(y, ls), False{}, hyl) :
        {Bool.and(Bool.not(Bool.or(False{}, _)), NOTIN(q, x <> ls)) == True{} : Bool}
      notin_cons(q, x, ls, hql, hxq)

def sub_pos(+a: Nat, +c: Nat, +h: {Nat.is_lt(a, c) == True{} : Bool}) -> {Nat.is_le(1n, Nat.sub(c, a)) == True{} : Bool}:
  match a c:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, LS.ft(h))
    case 0n 1n+q:
      N.le_zero_l(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, LS.ft(h))
    case 1n+p 1n+q:
      sub_pos(p, q, h)

# ---------------------------------------------------------------------------
# One step
# ---------------------------------------------------------------------------

# What the loop's answer says from state a (ps before it).
def ALC(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool, +ns: List<&2, NX.Ap>, +u: Bool) -> Type:
  {MSL(Q.xs(len, t), ns) == LP.PS(len, t, a, e) : LL()}
  & ({G.GD(len, t, ns) == True{} : Bool}
  & ({Q.ALS_IN(e, ns) == True{} : Bool}
  & ({Bool.and(B.Alleles.distinct(Q.BFS(Q.xs(len, t), ns)), NOTIN(Q.BFS(Q.xs(len, t), ps), Q.BFS(Q.xs(len, t), ns))) == True{} : Bool}
  & {u == Bool.and(up, UPS(Q.xs(len, t), ns)) : Bool})))

def LTN(+a: U32, +b: U32, +h: {U32.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(n(a), n(b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(n(a), n(b)), U32.is_lt(a, b), True{}, Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(n(a), n(b)), U.is_lt_to_nat(a, b)), h)

def LTF(+a: U32, +b: U32, +h: {U32.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(n(a), n(b)) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(n(a), n(b)), U32.is_lt(a, b), False{}, Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(n(a), n(b)), U.is_lt_to_nat(a, b)), h)

# The step's facts, from the range of the comma search.
def hac(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}) -> {Nat.is_le(n(a), n(CC(len, t, e, a))) == True{} : Bool}:
  LS.and_l(Nat.is_le(n(a), n(CC(len, t, e, a))), Nat.is_le(n(CC(len, t, e, a)), n(e)), LP.fv_range(len, t, d, a, e, h, hae, hel))

def hce(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}) -> {Nat.is_le(n(CC(len, t, e, a)), n(e)) == True{} : Bool}:
  LS.and_r(Nat.is_le(n(a), n(CC(len, t, e, a))), Nat.is_le(n(CC(len, t, e, a)), n(e)), LP.fv_range(len, t, d, a, e, h, hae, hel))

# a + (c - a) = c, as numbers.
def hsum(+a: U32, +c: U32, +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}) -> {Nat.add(n(a), n((c - a : U32))) == n(c) : Nat}:
  Equal.trans(Nat, Nat.add(n(a), n((c - a : U32))), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
    Equal.cong(Nat, Nat, z => Nat.add(n(a), z), n((c - a : U32)), Nat.sub(n(c), n(a)), LP.sub_u(c, a, hac)), N.le_sub_add(n(a), n(c), hac))

def lets_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {P.L2.ok(P.LETS(len, t, a, c)) == Q.lets(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))) : Bool}:
  Equal.cong(P.L2, Bool, z => P.L2.ok(z), P.LETS(len, t, a, c), P.L2{Q.lets(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))), L.UPA(D.slice(Q.xs(len, t), n(a), n((c - a : U32))))}, G.lets_v(len, t, d, a, c, h, hac, hcl))

def lets_up(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {P.L2.up(P.LETS(len, t, a, c)) == L.UPA(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))) : Bool}:
  Equal.cong(P.L2, Bool, z => P.L2.up(z), P.LETS(len, t, a, c), P.L2{Q.lets(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))), L.UPA(D.slice(Q.xs(len, t), n(a), n((c - a : U32))))}, G.lets_v(len, t, d, a, c, h, hac, hcl))

# The first piece of a .. e-1 is the allele.
def piece1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +ts: LL(),
  +hts: {LP.TS(len, t, CC(len, t, e, a), e) == ts : LL()}) ->
  {Q.SL(Q.xs(len, t), AP(len, t, e, a)) <> ts == LP.PS(len, t, a, e) : LL()}:
  +c = CC(len, t, e, a)
  %Equal.sym(Nat, n((c - a : U32)), Nat.sub(n(c), n(a)), LP.sub_u(c, a, hac(len, t, d, e, a, h, hae, hel))) :
    {D.slice(Q.xs(len, t), n(a), _) <> ts == LP.PS(len, t, a, e) : LL()}
  %hts : {LP.BS(len, t, a, c) <> _ == LP.PS(len, t, a, e) : LL()}
  Equal.sym(LL(), LP.PS(len, t, a, e), LP.BS(len, t, a, c) <> LP.TS(len, t, c, e), LP.ps_first(len, t, d, a, e, h, hae, hel))

# The tests a step passed (OK2 true).
def k_lok(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {P.L2.ok(P.LETS(len, t, a, CC(len, t, e, a))) == True{} : Bool}:
  +c = CC(len, t, e, a)
  LS.and_l(P.L2.ok(P.LETS(len, t, a, c)), U32.is_lt(a, c), LS.and_l(Bool.and(P.L2.ok(P.LETS(len, t, a, c)), U32.is_lt(a, c)), P.DG(ps, len, t, True{}, AP(len, t, e, a)), hb))

def k_lt(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {U32.is_lt(a, CC(len, t, e, a)) == True{} : Bool}:
  +c = CC(len, t, e, a)
  LS.and_r(P.L2.ok(P.LETS(len, t, a, c)), U32.is_lt(a, c), LS.and_l(Bool.and(P.L2.ok(P.LETS(len, t, a, c)), U32.is_lt(a, c)), P.DG(ps, len, t, True{}, AP(len, t, e, a)), hb))

def k_dg(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {P.DG(ps, len, t, True{}, AP(len, t, e, a)) == True{} : Bool}:
  +c = CC(len, t, e, a)
  LS.and_r(Bool.and(P.L2.ok(P.LETS(len, t, a, c)), U32.is_lt(a, c)), P.DG(ps, len, t, True{}, AP(len, t, e, a)), hb)

def SLA(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> List<&2, U32>:
  Q.SL(Q.xs(len, t), AP(len, t, e, a))

def k_lets(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {Q.lets(SLA(len, t, e, a)) == True{} : Bool}:
  +c = CC(len, t, e, a)
  +ac = hac(len, t, d, e, a, h, hae, hel)
  Equal.trans(Bool, Q.lets(SLA(len, t, e, a)), P.L2.ok(P.LETS(len, t, a, c)), True{},
    Equal.sym(Bool, P.L2.ok(P.LETS(len, t, a, c)), Q.lets(SLA(len, t, e, a)), lets_ok(len, t, d, a, c, h, ac, N.le_trans(n(c), n(e), n(len), hce(len, t, d, e, a, h, hae, hel), hel))),
    k_lok(len, t, e, a, ps, hb))

def k_inb(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n(a), n((CC(len, t, e, a) - a : U32))), n(e)) == True{} : Bool}:
  +c = CC(len, t, e, a)
  AB.subst(Nat, z => {Nat.is_le(z, n(e)) == True{} : Bool}, n(c), Nat.add(n(a), n((c - a : U32))),
    Equal.sym(Nat, Nat.add(n(a), n((c - a : U32))), n(c), hsum(a, c, hac(len, t, d, e, a, h, hae, hel))), hce(len, t, d, e, a, h, hae, hel))

def k_one(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {Nat.is_le(1n, n((CC(len, t, e, a) - a : U32))) == True{} : Bool}:
  +c = CC(len, t, e, a)
  AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.sub(n(c), n(a)), n((c - a : U32)),
    Equal.sym(Nat, n((c - a : U32)), Nat.sub(n(c), n(a)), LP.sub_u(c, a, hac(len, t, d, e, a, h, hae, hel))),
    sub_pos(n(a), n(c), LTN(a, c, k_lt(len, t, e, a, ps, hb))))

def k_gd(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {Bool.and(G.INB(len, AP(len, t, e, a)), Q.lets(SLA(len, t, e, a))) == True{} : Bool}:
  +c = CC(len, t, e, a)
  SP.and_tt(G.INB(len, AP(len, t, e, a)), Q.lets(SLA(len, t, e, a)),
    N.le_trans(Nat.add(n(a), n((c - a : U32))), n(e), n(len), k_inb(len, t, d, e, a, h, hae, hel), hel),
    k_lets(len, t, d, e, a, ps, h, hae, hel, hb))

def k_mem(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool}) ->
  {B.Alleles.member(G.bfx(len, t, AP(len, t, e, a)), Q.BFS(Q.xs(len, t), ps)) == False{} : Bool}:
  +ap = AP(len, t, e, a)
  +gd = k_gd(len, t, d, e, a, ps, h, hae, hel, hb)
  +mb = B.Alleles.member(G.bfx(len, t, ap), Q.BFS(Q.xs(len, t), ps))
  LS.not_t(mb, Equal.trans(Bool, Bool.not(mb), P.DG(ps, len, t, True{}, ap), True{},
    Equal.sym(Bool, P.DG(ps, len, t, True{}, ap), Bool.not(mb),
      G.dg_m(ps, len, t, d, True{}, ap, h, LS.and_l(G.INB(len, ap), Q.lets(SLA(len, t, e, a)), gd), LS.and_r(G.INB(len, ap), Q.lets(SLA(len, t, e, a)), gd), hg)),
    k_dg(len, t, e, a, ps, hb)))

# The next state: c + 1 <= e when c < e.
def k_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hm: {U32.is_lt(CC(len, t, e, a), e) == True{} : Bool}) ->
  {Nat.is_le(n((CC(len, t, e, a) + 1 : U32)), n(e)) == True{} : Bool}:
  +c = CC(len, t, e, a)
  +lt = LTN(c, e, hm)
  +i = LP.inc_len(len, t, d, c, h, N.lt_le_trans(n(c), n(e), n(len), lt, hel))
  AB.subst(Nat, z => {Nat.is_le(z, n(e)) == True{} : Bool}, 1n+n(c), n((c + 1 : U32)),
    Equal.sym(Nat, n((c + 1 : U32)), 1n+n(c), Equal.trans(Nat, n((c + 1 : U32)), Nat.add(n(c), 1n), 1n+n(c), i, N.add_one(n(c)))),
    Equal.trans(Bool, Nat.is_le(1n+n(c), n(e)), Nat.is_lt(n(c), n(e)), True{}, N.le_succ_lt(n(c), n(e)), lt))

def ALS1(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> Bool:
  Bool.and(Nat.is_le(1n, n((CC(len, t, e, a) - a : U32))), Nat.is_le(Nat.add(n(a), n((CC(len, t, e, a) - a : U32))), n(e)))

def k_als(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool}) ->
  {ALS1(len, t, e, a) == True{} : Bool}:
  SP.and_tt(Nat.is_le(1n, n((CC(len, t, e, a) - a : U32))), Nat.is_le(Nat.add(n(a), n((CC(len, t, e, a) - a : U32))), n(e)),
    k_one(len, t, d, e, a, ps, h, hae, hel, hb), k_inb(len, t, d, e, a, h, hae, hel))

def k_up(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool}) ->
  {P.L2.up(P.LETS(len, t, a, CC(len, t, e, a))) == L.UPA(SLA(len, t, e, a)) : Bool}:
  lets_up(len, t, d, a, CC(len, t, e, a), h, hac(len, t, d, e, a, h, hae, hel), N.le_trans(n(CC(len, t, e, a)), n(e), n(len), hce(len, t, d, e, a, h, hae, hel), hel))

def astep_tt.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool, +ns: List<&2, NX.Ap>, +u: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool},
  +hm: {U32.is_lt(CC(len, t, e, a), e) == True{} : Bool},
  +f1: {MSL(Q.xs(len, t), ns) == LP.PS(len, t, (CC(len, t, e, a) + 1 : U32), e) : LL()},
  +f2: {G.GD(len, t, ns) == True{} : Bool},
  +f3: {Q.ALS_IN(e, ns) == True{} : Bool},
  +f4: {Bool.and(B.Alleles.distinct(Q.BFS(Q.xs(len, t), ns)), NOTIN(Q.BFS(Q.xs(len, t), AP(len, t, e, a) <> ps), Q.BFS(Q.xs(len, t), ns))) == True{} : Bool},
  +f5: {u == Bool.and(UP2(len, t, e, a, up), UPS(Q.xs(len, t), ns)) : Bool}) ->
  ALC(len, t, e, a, ps, up, AP(len, t, e, a) <> ns, u):
  +c = CC(len, t, e, a)
  +ap = AP(len, t, e, a)
  +xs = Q.xs(len, t)
  +X = G.bfx(len, t, ap)
  +BN = Q.BFS(xs, ns)
  +BP = Q.BFS(xs, ps)
  +lt = LTN(c, e, hm)
  +hts = Equal.trans(LL(), LP.TS(len, t, c, e), LP.PS(len, t, (c + 1 : U32), e), MSL(xs, ns),
    LP.ts_next(len, t, d, c, e, h, hel, lt, LP.fv_hit(len, t, d, a, e, h, hae, hel, lt)), Equal.sym(LL(), MSL(xs, ns), LP.PS(len, t, (c + 1 : U32), e), f1))
  +nt = LS.and_r(B.Alleles.distinct(BN), NOTIN(X <> BP, BN), f4)
  +dn = LS.and_l(B.Alleles.distinct(BN), NOTIN(X <> BP, BN), f4)
  +hU = Equal.trans(Bool, u, Bool.and(UP2(len, t, e, a, up), UPS(xs, ns)), Bool.and(up, Bool.and(L.UPA(SLA(len, t, e, a)), UPS(xs, ns))), f5,
    Equal.trans(Bool, Bool.and(Bool.and(up, P.L2.up(P.LETS(len, t, a, c))), UPS(xs, ns)), Bool.and(Bool.and(up, L.UPA(SLA(len, t, e, a))), UPS(xs, ns)), Bool.and(up, Bool.and(L.UPA(SLA(len, t, e, a)), UPS(xs, ns))),
      Equal.cong(Bool, Bool, z => Bool.and(Bool.and(up, z), UPS(xs, ns)), P.L2.up(P.LETS(len, t, a, c)), L.UPA(SLA(len, t, e, a)), k_up(len, t, d, e, a, h, hae, hel)),
      LS.and_assoc(up, L.UPA(SLA(len, t, e, a)), UPS(xs, ns))))
  (piece1(len, t, d, e, a, h, hae, hel, MSL(xs, ns), hts),
    (SP.and_tt(Bool.and(G.INB(len, ap), Q.lets(SLA(len, t, e, a))), G.GD(len, t, ns), k_gd(len, t, d, e, a, ps, h, hae, hel, hb), f2),
    (SP.and_tt(ALS1(len, t, e, a), Q.ALS_IN(e, ns), k_als(len, t, d, e, a, ps, h, hae, hel, hb), f3),
    (SP.and_tt(B.Alleles.distinct(X <> BN), NOTIN(BP, X <> BN),
       SP.and_tt(Bool.not(B.Alleles.member(X, BN)), B.Alleles.distinct(BN), LS.and_l(Bool.not(B.Alleles.member(X, BN)), NOTIN(BP, BN), nt), dn),
       notin_cons(BP, X, BN, LS.and_r(Bool.not(B.Alleles.member(X, BN)), NOTIN(BP, BN), nt), k_mem(len, t, d, e, a, ps, h, hae, hel, hb, hg))),
    hU))))

# A step that continues: the answer from the next state, extended.
def astep_tt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool, +ns: List<&2, NX.Ap>, +u: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool},
  +hm: {U32.is_lt(CC(len, t, e, a), e) == True{} : Bool},
  r: ALC(len, t, e, (CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, UP2(len, t, e, a, up), ns, u)) ->
  ALC(len, t, e, a, ps, up, AP(len, t, e, a) <> ns, u):
  match r:
    case (f1, r2):
      match r2:
        case (f2, r3):
          match r3:
            case (f3, r4):
              match r4:
                case (f4, f5):
                  astep_tt.k(len, t, d, e, a, ps, up, ns, u, h, hae, hel, hg, hb, hm, f1, f2, f3, f4, f5)

def XT(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool, +b: Bool, +m: Bool) -> P.XD:
  P.XD{(CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, b, UP2(len, t, e, a, up), Bool.and(b, m)}

# A step that ends the loop: the comma search reached the field's end.
def astep_tf(+k: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == True{} : Bool},
  +hm: {U32.is_lt(CC(len, t, e, a), e) == False{} : Bool},
  +hok: {P.XD.ok(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, True{}, False{}))) == True{} : Bool}) ->
  ALC(len, t, e, a, ps, up, AP(len, t, e, a) <> XN(k, len, t, e, XT(len, t, e, a, ps, up, True{}, False{})), P.XD.up(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, True{}, False{})))):
  match k:
    case 0n:
      Empty.absurd(ALC(len, t, e, a, ps, up, [AP(len, t, e, a)], P.XD.up(P.XG(0n, len, t, e, XT(len, t, e, a, ps, up, True{}, False{})))), LS.ft(hok))
    case 1n+j:
      +c = CC(len, t, e, a)
      +ap = AP(len, t, e, a)
      +X = G.bfx(len, t, ap)
      +BP = Q.BFS(Q.xs(len, t), ps)
      +ceq = Z.le_antisym(n(c), n(e), hce(len, t, d, e, a, h, hae, hel), N.not_lt_le(n(c), n(e), LTF(c, e, hm)))
      +U2 = Bool.and(up, P.L2.up(P.LETS(len, t, a, c)))
      (piece1(len, t, d, e, a, h, hae, hel, Nil{}, LP.ts_last(len, t, c, e, ceq)),
        (SP.and_tt(Bool.and(G.INB(len, ap), Q.lets(SLA(len, t, e, a))), True{}, k_gd(len, t, d, e, a, ps, h, hae, hel, hb), {==}),
        (SP.and_tt(ALS1(len, t, e, a), True{}, k_als(len, t, d, e, a, ps, h, hae, hel, hb), {==}),
        (notin_cons(BP, X, Nil{}, notin_nil(BP), k_mem(len, t, d, e, a, ps, h, hae, hel, hb, hg)),
        Equal.trans(Bool, U2, Bool.and(up, L.UPA(SLA(len, t, e, a))), Bool.and(up, Bool.and(L.UPA(SLA(len, t, e, a)), True{})),
          Equal.cong(Bool, Bool, z => Bool.and(up, z), P.L2.up(P.LETS(len, t, a, c)), L.UPA(SLA(len, t, e, a)), k_up(len, t, d, e, a, h, hae, hel)),
          Equal.cong(Bool, Bool, z => Bool.and(up, z), L.UPA(SLA(len, t, e, a)), Bool.and(L.UPA(SLA(len, t, e, a)), True{}), Equal.sym(Bool, Bool.and(L.UPA(SLA(len, t, e, a)), True{}), L.UPA(SLA(len, t, e, a)), LS.and_true(L.UPA(SLA(len, t, e, a))))))))))

def astep_k(+b: Bool, +m: Bool, +k: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool}, +hb: {OK2(len, t, e, a, ps) == b : Bool},
  +hm: {U32.is_lt(CC(len, t, e, a), e) == m : Bool},
  +hok: {P.XD.ok(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, b, m))) == True{} : Bool},
  ih: {Nat.is_le(n((CC(len, t, e, a) + 1 : U32)), n(e)) == True{} : Bool} -> {G.GD(len, t, AP(len, t, e, a) <> ps) == True{} : Bool} ->
    {P.XD.ok(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, True{}, True{}))) == True{} : Bool} ->
    ALC(len, t, e, (CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, UP2(len, t, e, a, up), XN(k, len, t, e, XT(len, t, e, a, ps, up, True{}, True{})), P.XD.up(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, True{}, True{}))))) ->
  ALC(len, t, e, a, ps, up, AP(len, t, e, a) <> XN(k, len, t, e, XT(len, t, e, a, ps, up, b, m)), P.XD.up(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, b, m)))):
  match b m:
    case False{} _:
      Empty.absurd(ALC(len, t, e, a, ps, up, AP(len, t, e, a) <> XN(k, len, t, e, XT(len, t, e, a, ps, up, False{}, m)), P.XD.up(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, False{}, m)))),
        LS.ft(Equal.trans(Bool, False{}, P.XD.ok(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, False{}, m))), True{},
          Equal.sym(Bool, P.XD.ok(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, False{}, m))), False{}, xg_false(k, len, t, e, (CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, UP2(len, t, e, a, up), False{})), hok)))
    case True{} True{}:
      astep_tt(len, t, d, e, a, ps, up, XN(k, len, t, e, XT(len, t, e, a, ps, up, True{}, True{})), P.XD.up(P.XG(k, len, t, e, XT(len, t, e, a, ps, up, True{}, True{}))),
        h, hae, hel, hg, hb, hm,
        ih(k_next(len, t, d, e, a, h, hel, hm),
          SP.and_tt(Bool.and(G.INB(len, AP(len, t, e, a)), Q.lets(SLA(len, t, e, a))), G.GD(len, t, ps), k_gd(len, t, d, e, a, ps, h, hae, hel, hb), hg),
          hok))
    case True{} False{}:
      astep_tf(k, len, t, d, e, a, ps, up, h, hae, hel, hg, hb, hm, hok)

def X1(+a: U32, +ps: List<&2, NX.Ap>, +up: Bool) -> P.XD:
  P.XD{a, ps, True{}, up, True{}}

# The loop from a (ps before it), when its answer is fine.
def aloop(+k: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}, +hel: {Nat.is_le(n(e), n(len)) == True{} : Bool},
  +hg: {G.GD(len, t, ps) == True{} : Bool},
  +hok: {P.XD.ok(P.XG(k, len, t, e, X1(a, ps, up))) == True{} : Bool}) ->
  ALC(len, t, e, a, ps, up, XN(k, len, t, e, X1(a, ps, up)), P.XD.up(P.XG(k, len, t, e, X1(a, ps, up)))):
  match k:
    case 0n:
      Empty.absurd(ALC(len, t, e, a, ps, up, Nil{}, up), LS.ft(hok))
    case 1n+j:
      astep_k(OK2(len, t, e, a, ps), U32.is_lt(CC(len, t, e, a), e), j, len, t, d, e, a, ps, up, h, hae, hel, hg, {==}, {==}, hok,
        +x1 => +x2 => +x3 => aloop(j, len, t, d, e, (CC(len, t, e, a) + 1 : U32), AP(len, t, e, a) <> ps, UP2(len, t, e, a, up), h, x1, hel, x2, x3))
