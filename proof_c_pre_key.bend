import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_let.bend as L
import ./proof_c_pre_lp.bend as G
import ./proof_b_alleles.bend as AL
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-bytes@0.1.0.0/proof_list.bend as PL
import lawful-bytes@0.1.0.0/proof_same.bend as PSm
import lawful-bytes@0.1.0.0/proof_seq.bend as SQ
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# INFO's stale keys: when NX.nostale passes on INFO's bytes, B.Info.has is
# False on INFO's text for CIGAR, HOMLEN, HOMSEQ and AA. The scan (P.SG)
# walks the entries (the pieces between ';'); an entry's key ends at its
# first '=' (or ';', or INFO's end), as B.Info.key reads it.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def LL() -> Data:
  List<&2, List<&2, U32>>

# ---------------------------------------------------------------------------
# Text and keys
# ---------------------------------------------------------------------------

def csplit_g(+xs: List<&2, U32>, +c: U32) -> {String.split(Norm.chars(xs), Chr{c}) == AL.mapc(FD.split(xs, c)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +q:
      %Equal.sym(List<&2, String>, String.split(Norm.chars(q), Chr{c}), AL.mapc(FD.split(q, c)), csplit_g(q, c)) :
        {String.split.fin(Chr{x}, _, U32.is_eq(x, c)) == AL.mapc(FD.split(x <> q, c)) : List<&2, String>}
      AL.cs.k(x, U32.is_eq(x, c), FD.split(q, c))

def LO_and(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) -> {P.LO(ok, len, t, k, j) == Bool.and(ok, U32.is_eq(C.AT(len, t, j), k)) : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# lit.go on the mirror: the bytes from j are ks.
def lit_v(+ks: List<&2, U32>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +ok: Bool, +j: U32,
  +hj: {Nat.is_le(Nat.add(n(j), List.length(&2, U32, ks)), n(len)) == True{} : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {P.LIT(ks, len, t, ok, j) == Bool.and(ok, D.list_eq(D.slice(Q.xs(len, t), n(j), List.length(&2, U32, ks)), ks)) : Bool}:
  match ks:
    case Nil{}:
      +Lz = List.drop(&2, U32, Q.xs(len, t), n(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Lz, 0n), Nil{}, SQ.take_zero(Lz)) : {ok == Bool.and(ok, D.list_eq(_, Nil{})) : Bool}
      Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok))
    case +k <> +q:
      +VW = Q.xs(len, t)
      +y = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +m = List.length(&2, U32, q)
      +S1 = D.slice(VW, n(j1), m)
      %Equal.sym(Bool, P.LO(ok, len, t, k, j), Bool.and(ok, U32.is_eq(C.AT(len, t, j), k)), LO_and(ok, len, t, k, j)) : {P.LIT(q, len, t, _, j1) == Bool.and(ok, D.list_eq(D.slice(VW, n(j), 1n+m), k <> q)) : Bool}
      %Equal.sym(List<&2, U32>, D.slice(VW, n(j), 1n+m), y <> D.slice(VW, Nat.add(n(j), 1n), m), PSm.slice_cons(VW, n(j), m, y, G.get_of(len, t, d, j, m, h, hj))) :
        {P.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == Bool.and(ok, D.list_eq(_, k <> q)) : Bool}
      %G.inc_of(len, t, d, j, m, h, hj) :
        {P.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == Bool.and(ok, Bool.and(U32.is_eq(y, k), D.list_eq(D.slice(VW, _, m), q))) : Bool}
      %LS.and_assoc(ok, U32.is_eq(y, k), D.list_eq(S1, q)) :
        {P.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == _ : Bool}
      lit_v(q, len, t, d, Bool.and(ok, U32.is_eq(y, k)), j1, G.nx_of(len, t, d, j, m, h, hj), h)

def KB(i: Nat) -> List<&2, U32>:
  match i:
    case 0n:
      [67, 73, 71, 65, 82]
    case 1n:
      [72, 79, 77, 76, 69, 78]
    case 2n:
      [72, 79, 77, 83, 69, 81]
    case 1n+1n+1n+j:
      [65, 65]

def KS(i: Nat) -> String:
  match i:
    case 0n:
      "CIGAR"
    case 1n:
      "HOMLEN"
    case 2n:
      "HOMSEQ"
    case 1n+1n+1n+j:
      "AA"

def ks_kb(+i: Nat) -> {KS(i) == Norm.chars(KB(i)) : String}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 1n+1n+1n+j:
      {==}

def KL(i: Nat) -> U32:
  match i:
    case 0n:
      5
    case 1n:
      6
    case 2n:
      6
    case 1n+1n+1n+j:
      2

def KSL(+len: U32, +t: AT.Tree<U32>, +j: U32, +m: U32) -> List<&2, U32>:
  D.slice(Q.xs(len, t), n(j), n(m))

# What KEY false says of key i, when the key has i's length.
def KH(i: Nat, +len: U32, +t: AT.Tree<U32>, +j: U32) -> Type:
  {P.KEY(len, t, j, KL(i)) == False{} : Bool} -> {P.LIT(KB(i), len, t, True{}, j) == False{} : Bool}

def k6f(+b0: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32, +hb0: {P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == b0 : Bool},
  hk: {P.K6(b0, len, t, j) == False{} : Bool}) ->
  {P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == False{} : Bool} & {P.LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j) == False{} : Bool}:
  match b0:
    case True{}:
      Empty.absurd({P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == False{} : Bool} & {P.LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j) == False{} : Bool}, N.true_ne_false(hk))
    case False{}:
      (hb0, hk)

def K6P(+len: U32, +t: AT.Tree<U32>, +j: U32) -> Type:
  {P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == False{} : Bool} & {P.LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j) == False{} : Bool}

def k6p1(+len: U32, +t: AT.Tree<U32>, +j: U32, r: K6P(len, t, j)) -> {P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == False{} : Bool}:
  match r:
    case (a, b):
      a

def k6p2(+len: U32, +t: AT.Tree<U32>, +j: U32, r: K6P(len, t, j)) -> {P.LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j) == False{} : Bool}:
  match r:
    case (a, b):
      b

def k6a(+len: U32, +t: AT.Tree<U32>, +j: U32, hk: {P.K6(P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j), len, t, j) == False{} : Bool}) ->
  {P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j) == False{} : Bool}:
  k6p1(len, t, j, k6f(P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j), len, t, j, {==}, hk))

def k6b(+len: U32, +t: AT.Tree<U32>, +j: U32, hk: {P.K6(P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j), len, t, j) == False{} : Bool}) ->
  {P.LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j) == False{} : Bool}:
  k6p2(len, t, j, k6f(P.LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j), len, t, j, {==}, hk))

def kh(+i: Nat, +len: U32, +t: AT.Tree<U32>, +j: U32) -> KH(i, len, t, j):
  match i:
    case 0n:
      hk => hk
    case 1n:
      hk => k6a(len, t, j, hk)
    case 2n:
      hk => k6b(len, t, j, hk)
    case 1n+1n+1n+q:
      hk => hk

def len_kb(+i: Nat) -> {List.length(&2, U32, KB(i)) == n(KL(i)) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 1n+1n+1n+q:
      {==}

def kf.k(+b: Bool, +i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +m: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjm: {Nat.is_le(Nat.add(n(j), n(m)), n(len)) == True{} : Bool}, +hb: {U32.is_eq(m, KL(i)) == b : Bool},
  +hk: {P.KEY(len, t, j, m) == False{} : Bool}) ->
  {D.list_eq(KSL(len, t, j, m), KB(i)) == False{} : Bool}:
  match b:
    case True{}:
      +e = U.is_eq_true(m, KL(i), hb)
      +hk2 = AB.subst(U32, z => {P.KEY(len, t, j, z) == False{} : Bool}, m, KL(i), e, hk)
      +hjm2 = AB.subst(U32, z => {Nat.is_le(Nat.add(n(j), n(z)), n(len)) == True{} : Bool}, m, KL(i), e, hjm)
      %Equal.sym(U32, m, KL(i), e) : {D.list_eq(KSL(len, t, j, _), KB(i)) == False{} : Bool}
      %len_kb(i) : {D.list_eq(D.slice(Q.xs(len, t), n(j), _), KB(i)) == False{} : Bool}
      Equal.trans(Bool, D.list_eq(D.slice(Q.xs(len, t), n(j), List.length(&2, U32, KB(i))), KB(i)), P.LIT(KB(i), len, t, True{}, j), False{},
        Equal.sym(Bool, P.LIT(KB(i), len, t, True{}, j), D.list_eq(D.slice(Q.xs(len, t), n(j), List.length(&2, U32, KB(i))), KB(i)),
          lit_v(KB(i), len, t, d, True{}, j, AB.subst(Nat, z => {Nat.is_le(Nat.add(n(j), z), n(len)) == True{} : Bool}, n(KL(i)), List.length(&2, U32, KB(i)), Equal.sym(Nat, List.length(&2, U32, KB(i)), n(KL(i)), len_kb(i)), hjm2), h)),
        kh(i, len, t, j)(hk2))
    case False{}:
      +sl = LP.slice_len(Q.xs(len, t), n(j), n(m), AB.subst(Nat, z => {Nat.is_le(Nat.add(n(j), n(m)), z) == True{} : Bool}, n(len), List.length(&2, U32, Q.xs(len, t)), LP.len_x(len, t, d, h), hjm))
      LP.list_eq_len(KSL(len, t, j, m), KB(i),
        AB.subst(Nat, z => {Nat.is_eq(z, List.length(&2, U32, KB(i))) == False{} : Bool}, n(m), List.length(&2, U32, KSL(len, t, j, m)), Equal.sym(Nat, List.length(&2, U32, KSL(len, t, j, m)), n(m), sl),
          AB.subst(Nat, z => {Nat.is_eq(n(m), z) == False{} : Bool}, n(KL(i)), List.length(&2, U32, KB(i)), Equal.sym(Nat, List.length(&2, U32, KB(i)), n(KL(i)), len_kb(i)), Z.une(m, KL(i), hb))))

# A key the bytes test refused is none of the four.
def kfalse(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +m: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjm: {Nat.is_le(Nat.add(n(j), n(m)), n(len)) == True{} : Bool}, +hk: {P.KEY(len, t, j, m) == False{} : Bool}) ->
  {String.eq(Norm.chars(KSL(len, t, j, m)), KS(i)) == False{} : Bool}:
  %Equal.sym(String, KS(i), Norm.chars(KB(i)), ks_kb(i)) : {String.eq(Norm.chars(KSL(len, t, j, m)), _) == False{} : Bool}
  %Equal.sym(Bool, String.eq(Norm.chars(KSL(len, t, j, m)), Norm.chars(KB(i))), D.list_eq(KSL(len, t, j, m), KB(i)), L.seq(KSL(len, t, j, m), KB(i))) : {_ == False{} : Bool}
  kf.k(U32.is_eq(m, KL(i)), i, len, t, d, j, m, h, hjm, {==}, hk)

# ---------------------------------------------------------------------------
# The scan, entry by entry
# ---------------------------------------------------------------------------

# The entries from j on have none of key i.
def HG(+i: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> Type:
  {B.Info.has.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), n(j), Nat.sub(n(to), n(j))), 59)), KS(i)) == False{} : Bool}

def or_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, +hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, N.true_ne_false(Equal.sym(Bool, False{}, True{}, Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hb), h))))

def lt_no(+a: Nat, -G: Type, +h: {Nat.is_lt(a, a) == True{} : Bool}) -> G:
  Empty.absurd(G, LS.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, N.lt_irrefl(a)), h)))

def hlx(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: Nat, +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hx: {Nat.is_le(x, n(len)) == True{} : Bool}) ->
  {Nat.is_le(x, List.length(&2, U32, Q.xs(len, t))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, n(len), List.length(&2, U32, Q.xs(len, t)), LP.len_x(len, t, d, h), hx)

def KE(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> U32:
  P.KE(len, t, to, j)

def F2N(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> Nat:
  D.first2(Q.xs(len, t), n(j), n(to), 61, 59)

def nke(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {n(KE(len, t, to, j)) == F2N(len, t, to, j) : Nat}:
  M.f2_view(len, t, d, j, to, 61, 59, h, LP.le_u(j, to, hjt), hto, {==}, {==})

def kj(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {Nat.is_le(n(j), n(KE(len, t, to, j))) == True{} : Bool}:
  +f = F2N(len, t, to, j)
  AB.subst(Nat, z => {Nat.is_le(n(j), z) == True{} : Bool}, f, n(KE(len, t, to, j)), Equal.sym(Nat, n(KE(len, t, to, j)), f, nke(len, t, d, to, j, h, hto, hjt)),
    N.and_true_l(Nat.is_le(n(j), f), Nat.is_le(f, n(to)), PL.first2_range(Q.xs(len, t), n(j), n(to), 61, 59, hjt, hlx(len, t, d, n(to), h, hto))))

def kt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {Nat.is_le(n(KE(len, t, to, j)), n(to)) == True{} : Bool}:
  +f = F2N(len, t, to, j)
  AB.subst(Nat, z => {Nat.is_le(z, n(to)) == True{} : Bool}, f, n(KE(len, t, to, j)), Equal.sym(Nat, n(KE(len, t, to, j)), f, nke(len, t, d, to, j, h, hto, hjt)),
    N.and_true_r(Nat.is_le(n(j), f), Nat.is_le(f, n(to)), PL.first2_range(Q.xs(len, t), n(j), n(to), 61, 59, hjt, hlx(len, t, d, n(to), h, hto))))

def m2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +k: Nat, +a: {Nat.is_le(n(j), k) == True{} : Bool}, +b: {Nat.is_lt(k, n(KE(len, t, to, j))) == True{} : Bool}) ->
  {D.has2(Q.xs(len, t), k, 61, 59) == False{} : Bool}:
  PL.first2_miss(Q.xs(len, t), n(j), n(to), 61, 59, k, a,
    AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, n(KE(len, t, to, j)), F2N(len, t, to, j), nke(len, t, d, to, j, h, hto, hjt), b))

def m59(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +k: Nat, +a: {Nat.is_le(n(j), k) == True{} : Bool}, +b: {Nat.is_lt(k, n(KE(len, t, to, j))) == True{} : Bool}) ->
  {D.has(Q.xs(len, t), k, 59) == False{} : Bool}:
  Z.or_false_r(D.is_some(List.get(&2, U32, Q.xs(len, t), k), 61), D.is_some(List.get(&2, U32, Q.xs(len, t), k), 59), m2(len, t, d, to, j, h, hto, hjt, k, a, b))

def m61(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +k: Nat, +a: {Nat.is_le(n(j), k) == True{} : Bool}, +b: {Nat.is_lt(k, n(KE(len, t, to, j))) == True{} : Bool}) ->
  {D.has(Q.xs(len, t), k, 61) == False{} : Bool}:
  Z.or_false_l(D.is_some(List.get(&2, U32, Q.xs(len, t), k), 61), D.is_some(List.get(&2, U32, Q.xs(len, t), k), 59), m2(len, t, d, to, j, h, hto, hjt, k, a, b))

def hsum(+a: U32, +c: U32, +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}) -> {Nat.add(n(a), n((c - a : U32))) == n(c) : Nat}:
  Equal.trans(Nat, Nat.add(n(a), n((c - a : U32))), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
    Equal.cong(Nat, Nat, z => Nat.add(n(a), z), n((c - a : U32)), Nat.sub(n(c), n(a)), LP.sub_u(c, a, hac)), N.le_sub_add(n(a), n(c), hac))

# One entry (j .. s-1, the rest after it), its key ending at ke.
def ENT(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +s: Nat, +ke: U32, +rest: LL(),
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjk: {Nat.is_le(n(j), n(ke)) == True{} : Bool}, +hkl: {Nat.is_le(n(ke), n(len)) == True{} : Bool},
  +hfs: {D.first(Q.xs(len, t), n(j), n(to), 59) == s : Nat},
  +hrest: {LS.tsplit(D.slice(Q.xs(len, t), s, Nat.sub(n(to), s)), 59) == rest : LL()},
  +hfk: {D.first(Q.xs(len, t), n(j), s, 61) == n(ke) : Nat},
  +hK: {P.KEY(len, t, j, (ke - j : U32)) == False{} : Bool},
  +hR: {B.Info.has.go(AL.mapc(rest), KS(i)) == False{} : Bool}) ->
  HG(i, len, t, to, j):
  +X = Q.xs(len, t)
  +ent = D.slice(X, n(j), Nat.sub(s, n(j)))
  +f59 = D.first(X, n(j), n(to), 59)
  +f61 = D.first(X, n(j), s, 61)
  +hkey = Equal.trans(String, B.Info.key(Norm.chars(ent)), B.Rec.field(AL.mapc(FD.split(ent, 61)), 0n), Norm.chars(KSL(len, t, j, (ke - j : U32))),
    Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), String.split(Norm.chars(ent), '='), AL.mapc(FD.split(ent, 61)), csplit_g(ent, 61)),
    Equal.trans(String, B.Rec.field(AL.mapc(FD.split(ent, 61)), 0n), Norm.chars(D.slice(X, n(j), Nat.sub(f61, n(j)))), Norm.chars(KSL(len, t, j, (ke - j : U32))),
      Equal.cong(LL(), String, z => B.Rec.field(AL.mapc(z), 0n), FD.split(ent, 61), Con{D.slice(X, n(j), Nat.sub(f61, n(j))), LS.tsplit(D.slice(X, f61, Nat.sub(s, f61)), 61)}, LS.spl(X, n(j), s, 61)),
      Equal.cong(Nat, String, z => Norm.chars(D.slice(X, n(j), z)), Nat.sub(f61, n(j)), n((ke - j : U32)),
        Equal.trans(Nat, Nat.sub(f61, n(j)), Nat.sub(n(ke), n(j)), n((ke - j : U32)), Equal.cong(Nat, Nat, z => Nat.sub(z, n(j)), f61, n(ke), hfk), Equal.sym(Nat, n((ke - j : U32)), Nat.sub(n(ke), n(j)), LP.sub_u(ke, j, hjk))))))
  +hjm = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(ke), Nat.add(n(j), n((ke - j : U32))), Equal.sym(Nat, Nat.add(n(j), n((ke - j : U32))), n(ke), hsum(j, ke, hjk)), hkl)
  %Equal.sym(LL(), FD.split(D.slice(X, n(j), Nat.sub(n(to), n(j))), 59), Con{D.slice(X, n(j), Nat.sub(f59, n(j))), LS.tsplit(D.slice(X, f59, Nat.sub(n(to), f59)), 59)}, LS.spl(X, n(j), n(to), 59)) :
    {B.Info.has.go(AL.mapc(_), KS(i)) == False{} : Bool}
  %Equal.sym(Nat, f59, s, hfs) :
    {B.Info.has.go(AL.mapc(Con{D.slice(X, n(j), Nat.sub(_, n(j))), LS.tsplit(D.slice(X, _, Nat.sub(n(to), _)), 59)}), KS(i)) == False{} : Bool}
  %Equal.sym(LL(), LS.tsplit(D.slice(X, s, Nat.sub(n(to), s)), 59), rest, hrest) :
    {B.Info.has.go(AL.mapc(Con{ent, _}), KS(i)) == False{} : Bool}
  %Equal.sym(String, B.Info.key(Norm.chars(ent)), Norm.chars(KSL(len, t, j, (ke - j : U32))), hkey) :
    {Bool.or(String.eq(_, KS(i)), B.Info.has.go(AL.mapc(rest), KS(i))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(Norm.chars(KSL(len, t, j, (ke - j : U32))), KS(i)), False{}, kfalse(i, len, t, d, j, (ke - j : U32), h, hjm, hK)) :
    {Bool.or(_, B.Info.has.go(AL.mapc(rest), KS(i))) == False{} : Bool}
  hR

def kl(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {Nat.is_le(n(KE(len, t, to, j)), n(len)) == True{} : Bool}:
  N.le_trans(n(KE(len, t, to, j)), n(to), n(len), kt(len, t, d, to, j, h, hto, hjt), hto)

# INFO's end reached: one entry left, its key up to there.
def c_end(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == True{} : Bool},
  +hK: {P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)) == False{} : Bool}) ->
  HG(i, len, t, to, j):
  +ke = KE(len, t, to, j)
  +X = Q.xs(len, t)
  +ek = Equal.cong(U32, Nat, z => n(z), ke, to, U.is_eq_true(ke, to, hen))
  +hL = hlx(len, t, d, n(to), h, hto)
  +hfs = Z.unq(X, n(j), n(to), n(to), 59, hjt, N.le_refl(n(to)), hL, h0 => lt_no(n(to), {D.has(X, n(to), 59) == True{} : Bool}, h0),
    +k => a => b => m59(len, t, d, to, j, h, hto, hjt, k, a, AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, n(to), n(ke), Equal.sym(Nat, n(ke), n(to), ek), b)))
  +hfk = Z.unq(X, n(j), n(ke), n(to), 61, kj(len, t, d, to, j, h, hto, hjt), kt(len, t, d, to, j, h, hto, hjt), hL,
    h0 => lt_no(n(to), {D.has(X, n(ke), 61) == True{} : Bool}, AB.subst(Nat, z => {Nat.is_lt(z, n(to)) == True{} : Bool}, n(ke), n(to), ek, h0)),
    +k => a => b => m61(len, t, d, to, j, h, hto, hjt, k, a, b))
  ENT(i, len, t, d, to, j, n(to), ke, Nil{}, h, kj(len, t, d, to, j, h, hto, hjt), kl(len, t, d, to, j, h, hto, hjt), hfs, LS.ts_eq(X, n(to), 59), hfk, hK, {==})

def ke_lt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool}) -> {Nat.is_lt(n(KE(len, t, to, j)), n(to)) == True{} : Bool}:
  Z.le_ne_lt(n(KE(len, t, to, j)), n(to), kt(len, t, d, to, j, h, hto, hjt), Z.une(KE(len, t, to, j), to, hen))

def ke_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool}) -> {Nat.is_lt(n(KE(len, t, to, j)), n(len)) == True{} : Bool}:
  N.lt_le_trans(n(KE(len, t, to, j)), n(to), n(len), ke_lt(len, t, d, to, j, h, hto, hjt, hen), hto)

# The next entry after a ';' at c (c < to): HG there, at c + 1 as a word.
def hg_next(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hcl: {Nat.is_lt(n(c), n(len)) == True{} : Bool}, hR: HG(i, len, t, to, (c + 1 : U32))) ->
  {B.Info.has.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), Nat.add(n(c), 1n), Nat.sub(n(to), Nat.add(n(c), 1n))), 59)), KS(i)) == False{} : Bool}:
  AB.subst(Nat, z => {B.Info.has.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), z, Nat.sub(n(to), z)), 59)), KS(i)) == False{} : Bool}, n((c + 1 : U32)), Nat.add(n(c), 1n),
    LP.inc_len(len, t, d, c, h, hcl), hR)

def c1_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hcl: {Nat.is_lt(n(c), n(len)) == True{} : Bool}, +hct: {Nat.is_lt(n(c), n(to)) == True{} : Bool}) -> {Nat.is_le(n((c + 1 : U32)), n(to)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, n(to)) == True{} : Bool}, 1n+n(c), n((c + 1 : U32)),
    Equal.sym(Nat, n((c + 1 : U32)), 1n+n(c), Equal.trans(Nat, n((c + 1 : U32)), Nat.add(n(c), 1n), 1n+n(c), LP.inc_len(len, t, d, c, h, hcl), N.add_one(n(c)))),
    Equal.trans(Bool, Nat.is_le(1n+n(c), n(to)), Nat.is_lt(n(c), n(to)), True{}, N.le_succ_lt(n(c), n(to)), hct))

# A ';' ends the key: the entry ends there too.
def c_semi(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == True{} : Bool},
  +hK: {P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)) == False{} : Bool},
  hR: HG(i, len, t, to, (KE(len, t, to, j) + 1 : U32))) ->
  HG(i, len, t, to, j):
  +ke = KE(len, t, to, j)
  +X = Q.xs(len, t)
  +hL = hlx(len, t, d, n(to), h, hto)
  +lt = ke_lt(len, t, d, to, j, h, hto, hjt, hen)
  +lk = ke_len(len, t, d, to, j, h, hto, hjt, hen)
  +hg = Z.tabget(len, t, d, ke, 59, h, lk, hse)
  +hfs = Z.unq(X, n(j), n(ke), n(to), 59, kj(len, t, d, to, j, h, hto, hjt), kt(len, t, d, to, j, h, hto, hjt), hL,
    h0 => Z.has_get(X, n(ke), 59, 59, hg),
    +k => a => b => m59(len, t, d, to, j, h, hto, hjt, k, a, b))
  +hfk = Z.unq(X, n(j), n(ke), n(ke), 61, kj(len, t, d, to, j, h, hto, hjt), N.le_refl(n(ke)), hlx(len, t, d, n(ke), h, kl(len, t, d, to, j, h, hto, hjt)),
    h0 => lt_no(n(ke), {D.has(X, n(ke), 61) == True{} : Bool}, h0),
    +k => a => b => m61(len, t, d, to, j, h, hto, hjt, k, a, b))
  ENT(i, len, t, d, to, j, n(ke), ke, FD.split(D.slice(X, Nat.add(n(ke), 1n), Nat.sub(n(to), Nat.add(n(ke), 1n))), 59), h,
    kj(len, t, d, to, j, h, hto, hjt), kl(len, t, d, to, j, h, hto, hjt), hfs, LS.ts_lt(X, n(ke), n(to), 59, lt, hg), hfk, hK,
    hg_next(i, len, t, d, to, ke, h, lk, hR))

# After an '=' at ke: the next ';' from ke (or INFO's end).
def SM(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> U32:
  M.F1(len, t, KE(len, t, to, j), to, 59)

def F59(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> Nat:
  D.first(Q.xs(len, t), n(KE(len, t, to, j)), n(to), 59)

def nsm(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {n(SM(len, t, to, j)) == F59(len, t, to, j) : Nat}:
  M.f1_view(len, t, d, KE(len, t, to, j), to, 59, h, LP.le_u(KE(len, t, to, j), to, kt(len, t, d, to, j, h, hto, hjt)), hto, {==})

def ksm(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {Nat.is_le(n(KE(len, t, to, j)), F59(len, t, to, j)) == True{} : Bool}:
  N.and_true_l(Nat.is_le(n(KE(len, t, to, j)), F59(len, t, to, j)), Nat.is_le(F59(len, t, to, j), n(to)),
    PL.first_range(Q.xs(len, t), n(KE(len, t, to, j)), n(to), 59, kt(len, t, d, to, j, h, hto, hjt), hlx(len, t, d, n(to), h, hto)))

def smt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) -> {Nat.is_le(F59(len, t, to, j), n(to)) == True{} : Bool}:
  N.and_true_r(Nat.is_le(n(KE(len, t, to, j)), F59(len, t, to, j)), Nat.is_le(F59(len, t, to, j), n(to)),
    PL.first_range(Q.xs(len, t), n(KE(len, t, to, j)), n(to), 59, kt(len, t, d, to, j, h, hto, hjt), hlx(len, t, d, n(to), h, hto)))

def h59k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool}) -> {D.has(Q.xs(len, t), n(KE(len, t, to, j)), 59) == False{} : Bool}:
  +ke = KE(len, t, to, j)
  Equal.trans(Bool, D.has(Q.xs(len, t), n(ke), 59), U32.is_eq(C.AT(len, t, ke), 59), False{},
    Z.has_get(Q.xs(len, t), n(ke), C.AT(len, t, ke), 59, PF.step_get(len, t, d, ke, h, ke_len(len, t, d, to, j, h, hto, hjt, hen))), hse)

def h61k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool}) -> {D.has(Q.xs(len, t), n(KE(len, t, to, j)), 61) == True{} : Bool}:
  +ke = KE(len, t, to, j)
  +X = Q.xs(len, t)
  +ek = nke(len, t, d, to, j, h, hto, hjt)
  +h2 = AB.subst(Nat, z => {D.has2(X, z, 61, 59) == True{} : Bool}, F2N(len, t, to, j), n(ke), Equal.sym(Nat, n(ke), F2N(len, t, to, j), ek),
    PL.first2_hit(X, n(j), n(to), 61, 59, hjt, hlx(len, t, d, n(to), h, hto),
      AB.subst(Nat, z => {Nat.is_lt(z, n(to)) == True{} : Bool}, n(ke), F2N(len, t, to, j), ek, ke_lt(len, t, d, to, j, h, hto, hjt, hen))))
  or_l(D.is_some(List.get(&2, U32, X, n(ke)), 61), D.is_some(List.get(&2, U32, X, n(ke)), 59), h2, h59k(len, t, d, to, j, h, hto, hjt, hen, hse))

def miss3(+b1: Bool, +b2: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool},
  +k: Nat, +hb1: {Nat.is_lt(k, n(KE(len, t, to, j))) == b1 : Bool}, +hb2: {Nat.is_eq(n(KE(len, t, to, j)), k) == b2 : Bool},
  +a: {Nat.is_le(n(j), k) == True{} : Bool}, +b: {Nat.is_lt(k, F59(len, t, to, j)) == True{} : Bool}) ->
  {D.has(Q.xs(len, t), k, 59) == False{} : Bool}:
  match b1 b2:
    case True{} _:
      m59(len, t, d, to, j, h, hto, hjt, k, a, hb1)
    case False{} True{}:
      AB.subst(Nat, z => {D.has(Q.xs(len, t), z, 59) == False{} : Bool}, n(KE(len, t, to, j)), k, N.eq_sound(n(KE(len, t, to, j)), k, hb2), h59k(len, t, d, to, j, h, hto, hjt, hen, hse))
    case False{} False{}:
      PL.first_miss(Q.xs(len, t), n(KE(len, t, to, j)), n(to), 59, k, N.not_lt_le(k, n(KE(len, t, to, j)), hb1), b)

def hfs_e(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool}) ->
  {D.first(Q.xs(len, t), n(j), n(to), 59) == F59(len, t, to, j) : Nat}:
  +ke = KE(len, t, to, j)
  +lt = ke_lt(len, t, d, to, j, h, hto, hjt, hen)
  Z.unq(Q.xs(len, t), n(j), F59(len, t, to, j), n(to), 59,
    N.le_trans(n(j), n(ke), F59(len, t, to, j), kj(len, t, d, to, j, h, hto, hjt), ksm(len, t, d, to, j, h, hto, hjt)), smt(len, t, d, to, j, h, hto, hjt), hlx(len, t, d, n(to), h, hto),
    h0 => PL.first_hit(Q.xs(len, t), n(ke), n(to), 59, N.lt_to_le(n(ke), n(to), lt), hlx(len, t, d, n(to), h, hto), h0),
    +k => a => b => miss3(Nat.is_lt(k, n(ke)), Nat.is_eq(n(ke), k), len, t, d, to, j, h, hto, hjt, hen, hse, k, {==}, {==}, a, b))

def hfk_e(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool}) ->
  {D.first(Q.xs(len, t), n(j), F59(len, t, to, j), 61) == n(KE(len, t, to, j)) : Nat}:
  +ke = KE(len, t, to, j)
  Z.unq(Q.xs(len, t), n(j), n(ke), F59(len, t, to, j), 61, kj(len, t, d, to, j, h, hto, hjt), ksm(len, t, d, to, j, h, hto, hjt),
    hlx(len, t, d, F59(len, t, to, j), h, N.le_trans(F59(len, t, to, j), n(to), n(len), smt(len, t, d, to, j, h, hto, hjt), hto)),
    h0 => h61k(len, t, d, to, j, h, hto, hjt, hen, hse),
    +k => a => b => m61(len, t, d, to, j, h, hto, hjt, k, a, b))

# '=' then no ';' before INFO's end.
def c_eq_t(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool},
  +hK: {P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)) == False{} : Bool},
  +hb2: {U32.is_eq(SM(len, t, to, j), to) == True{} : Bool}) ->
  HG(i, len, t, to, j):
  +X = Q.xs(len, t)
  +f = F59(len, t, to, j)
  +ef = Equal.trans(Nat, f, n(SM(len, t, to, j)), n(to), Equal.sym(Nat, n(SM(len, t, to, j)), f, nsm(len, t, d, to, j, h, hto, hjt)),
    Equal.cong(U32, Nat, z => n(z), SM(len, t, to, j), to, U.is_eq_true(SM(len, t, to, j), to, hb2)))
  ENT(i, len, t, d, to, j, f, KE(len, t, to, j), Nil{}, h, kj(len, t, d, to, j, h, hto, hjt), kl(len, t, d, to, j, h, hto, hjt),
    hfs_e(len, t, d, to, j, h, hto, hjt, hen, hse),
    AB.subst(Nat, z => {LS.tsplit(D.slice(X, z, Nat.sub(n(to), z)), 59) == Nil{} : LL()}, n(to), f, Equal.sym(Nat, f, n(to), ef), LS.ts_eq(X, n(to), 59)),
    hfk_e(len, t, d, to, j, h, hto, hjt, hen, hse), hK, {==})

# '=' then a ';' before INFO's end: the next entry follows it.
def c_eq_f(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool},
  +hK: {P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)) == False{} : Bool},
  +hb2: {U32.is_eq(SM(len, t, to, j), to) == False{} : Bool},
  hR: HG(i, len, t, to, (SM(len, t, to, j) + 1 : U32))) ->
  HG(i, len, t, to, j):
  +X = Q.xs(len, t)
  +sm = SM(len, t, to, j)
  +f = F59(len, t, to, j)
  +es = nsm(len, t, d, to, j, h, hto, hjt)
  +lt2 = Z.le_ne_lt(f, n(to), smt(len, t, d, to, j, h, hto, hjt),
    AB.subst(Nat, z => {Nat.is_eq(z, n(to)) == False{} : Bool}, n(sm), f, es, Z.une(sm, to, hb2)))
  +ke = KE(len, t, to, j)
  +hit = PL.first_hit(X, n(ke), n(to), 59, kt(len, t, d, to, j, h, hto, hjt), hlx(len, t, d, n(to), h, hto), lt2)
  +hg2 = LP.has_get(X, f, 59, hit)
  +sml = AB.subst(Nat, z => {Nat.is_lt(z, n(len)) == True{} : Bool}, f, n(sm), Equal.sym(Nat, n(sm), f, es), N.lt_le_trans(f, n(to), n(len), lt2, hto))
  ENT(i, len, t, d, to, j, f, ke, FD.split(D.slice(X, Nat.add(f, 1n), Nat.sub(n(to), Nat.add(f, 1n))), 59), h,
    kj(len, t, d, to, j, h, hto, hjt), kl(len, t, d, to, j, h, hto, hjt),
    hfs_e(len, t, d, to, j, h, hto, hjt, hen, hse), LS.ts_lt(X, f, n(to), 59, lt2, hg2),
    hfk_e(len, t, d, to, j, h, hto, hjt, hen, hse), hK,
    AB.subst(Nat, z => {B.Info.has.go(AL.mapc(FD.split(D.slice(X, Nat.add(z, 1n), Nat.sub(n(to), Nat.add(z, 1n))), 59)), KS(i)) == False{} : Bool}, n(sm), f, es,
      hg_next(i, len, t, d, to, sm, h, sml, hR)))

# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------

def sg_false(+k: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> {P.SG(k, len, t, to, P.SD{j, False{}, False{}}) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      {==}

def sw_false(+b2: Bool, +k: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +sm: U32) -> {P.SG(k, len, t, to, P.SW(False{}, b2, sm)) == False{} : Bool}:
  match b2:
    case True{}:
      sg_false(k, len, t, to, sm)
    case False{}:
      sg_false(k, len, t, to, (sm + 1 : U32))

def se_false(+en: Bool, +se: Bool, +k: Nat, +len: U32, +t: AT.Tree<U32>, +ke: U32, +to: U32) ->
  {P.SG(k, len, t, to, P.SE(False{}, en, se, len, t, ke, to)) == False{} : Bool}:
  match en se:
    case True{} _:
      sg_false(k, len, t, to, ke)
    case False{} True{}:
      sg_false(k, len, t, to, (ke + 1 : U32))
    case False{} False{}:
      sw_false(U32.is_eq(M.F1(len, t, ke, to, 59), to), k, len, t, to, M.F1(len, t, ke, to, 59))

def IHT(+k: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32) -> Type:
  @jj: U32 -> {Nat.is_le(n(jj), n(to)) == True{} : Bool} -> {P.SG(k, len, t, to, P.SD{jj, True{}, True{}}) == True{} : Bool} -> HG(i, len, t, to, jj)

def sm_lt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hb2: {U32.is_eq(SM(len, t, to, j), to) == False{} : Bool}) -> {Nat.is_lt(n(SM(len, t, to, j)), n(to)) == True{} : Bool}:
  +es = nsm(len, t, d, to, j, h, hto, hjt)
  Z.le_ne_lt(n(SM(len, t, to, j)), n(to),
    AB.subst(Nat, z => {Nat.is_le(z, n(to)) == True{} : Bool}, F59(len, t, to, j), n(SM(len, t, to, j)), Equal.sym(Nat, n(SM(len, t, to, j)), F59(len, t, to, j), es), smt(len, t, d, to, j, h, hto, hjt)),
    Z.une(SM(len, t, to, j), to, hb2))

def c_eq2(+b2: Bool, +k: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == False{} : Bool},
  +hK: {P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)) == False{} : Bool},
  +hb2: {U32.is_eq(SM(len, t, to, j), to) == b2 : Bool},
  +hok: {P.SG(k, len, t, to, P.SW(True{}, b2, SM(len, t, to, j))) == True{} : Bool},
  ih: IHT(k, i, len, t, to)) ->
  HG(i, len, t, to, j):
  match b2:
    case True{}:
      c_eq_t(i, len, t, d, to, j, h, hto, hjt, hen, hse, hK, hb2)
    case False{}:
      +sm = SM(len, t, to, j)
      +lt = sm_lt(len, t, d, to, j, h, hto, hjt, hb2)
      c_eq_f(i, len, t, d, to, j, h, hto, hjt, hen, hse, hK, hb2,
        ih((sm + 1 : U32), c1_le(len, t, d, to, sm, h, N.lt_le_trans(n(sm), n(to), n(len), lt, hto), lt), hok))

def sstep(+nk: Bool, +en: Bool, +se: Bool, +k: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hnk: {Bool.not(P.KEY(len, t, j, (KE(len, t, to, j) - j : U32))) == nk : Bool},
  +hen: {U32.is_eq(KE(len, t, to, j), to) == en : Bool},
  +hse: {U32.is_eq(C.AT(len, t, KE(len, t, to, j)), 59) == se : Bool},
  +hok: {P.SG(k, len, t, to, P.SE(nk, en, se, len, t, KE(len, t, to, j), to)) == True{} : Bool},
  ih: IHT(k, i, len, t, to)) ->
  HG(i, len, t, to, j):
  match nk en se:
    case False{} _ _:
      Empty.absurd(HG(i, len, t, to, j), LS.ft(Equal.trans(Bool, False{}, P.SG(k, len, t, to, P.SE(False{}, en, se, len, t, KE(len, t, to, j), to)), True{},
        Equal.sym(Bool, P.SG(k, len, t, to, P.SE(False{}, en, se, len, t, KE(len, t, to, j), to)), False{}, se_false(en, se, k, len, t, KE(len, t, to, j), to)), hok)))
    case True{} True{} _:
      c_end(i, len, t, d, to, j, h, hto, hjt, hen, LS.not_t(P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)), hnk))
    case True{} False{} True{}:
      +ke = KE(len, t, to, j)
      c_semi(i, len, t, d, to, j, h, hto, hjt, hen, hse, LS.not_t(P.KEY(len, t, j, (ke - j : U32)), hnk),
        ih((ke + 1 : U32), c1_le(len, t, d, to, ke, h, ke_len(len, t, d, to, j, h, hto, hjt, hen), ke_lt(len, t, d, to, j, h, hto, hjt, hen)), hok))
    case True{} False{} False{}:
      c_eq2(U32.is_eq(SM(len, t, to, j), to), k, i, len, t, d, to, j, h, hto, hjt, hen, hse, LS.not_t(P.KEY(len, t, j, (KE(len, t, to, j) - j : U32)), hnk), {==}, hok, ih)

def sloop(+k: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hok: {P.SG(k, len, t, to, P.SD{j, True{}, True{}}) == True{} : Bool}) ->
  HG(i, len, t, to, j):
  match k:
    case 0n:
      Empty.absurd(HG(i, len, t, to, j), LS.ft(hok))
    case 1n+q:
      +ke = KE(len, t, to, j)
      sstep(Bool.not(P.KEY(len, t, j, (ke - j : U32))), U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), q, i, len, t, d, to, j, h, hto, hjt, {==}, {==}, {==}, hok,
        +jj => +a => +b => sloop(q, i, len, t, d, to, jj, h, hto, a, b))

# INFO (bytes e6 + 1 .. e7 - 1) passed NX.nostale: no entry with key i.
def info_key(+i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e6: U32, +e7: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h6: {Nat.is_lt(n(e6), n(len)) == True{} : Bool}, +h67: {Nat.is_le(n((e6 + 1 : U32)), n(e7)) == True{} : Bool}, +h7: {Nat.is_le(n(e7), n(len)) == True{} : Bool},
  +hn: {P.NOST(len, t, (e6 + 1 : U32), e7) == True{} : Bool}) ->
  {B.Info.has(Q.fld(Q.xs(len, t), Q.nx(e6), n(e7)), KS(i)) == False{} : Bool}:
  +X = Q.xs(len, t)
  +ys = D.slice(X, Nat.add(n(e6), 1n), Nat.sub(n(e7), Nat.add(n(e6), 1n)))
  %Equal.sym(List<&2, String>, String.split(Norm.chars(ys), ';'), AL.mapc(FD.split(ys, 59)), csplit_g(ys, 59)) :
    {B.Info.has.go(_, KS(i)) == False{} : Bool}
  AB.subst(Nat, z => {B.Info.has.go(AL.mapc(FD.split(D.slice(X, z, Nat.sub(n(e7), z)), 59)), KS(i)) == False{} : Bool}, n((e6 + 1 : U32)), Nat.add(n(e6), 1n),
    LP.inc_len(len, t, d, e6, h, h6), sloop(n((e7 - (e6 + 1 : U32) + 2 : U32)), i, len, t, d, e7, (e6 + 1 : U32), h, h7, h67, hn))
