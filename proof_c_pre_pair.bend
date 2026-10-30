import Base
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./proof_b_cut_pair.bend as M
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Every call NX.line makes on a buffer mirror C.BT(len, t) hands the mirror
# back, and what it answers is mirrored by a function on Data (len and t
# reusable): NX.line(BT, s) == Fr{BT, FX(len, t, s)}. The cut, POS and the
# END test are phase B's mirrors (proof_b_cut_pair.bend).

# ---------------------------------------------------------------------------
# Letters: lets
# ---------------------------------------------------------------------------

type L2 is Data:
  L2{ok: Bool, up: Bool}

def L2.ok(x: L2) -> Bool:
  match x:
    case L2{ok, up}:
      ok

def L2.up(x: L2) -> Bool:
  match x:
    case L2{ok, up}:
      up

# lets.go on the mirror: y is byte j.
def LG(n: Nat, +len: U32, +t: AT.Tree<U32>, +y: U32, +j: U32, ok: Bool, up: Bool) -> L2:
  match n:
    case 0n:
      L2{ok, up}
    case 1n+m:
      LG(m, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), ok && NX.isl(y), up && U32.is_lt(y, 97))

def lg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +y: U32, +j: U32, +ok: Bool, +up: Bool) ->
  {NX.lets.go(n, (C.BT(len, t), y), j, ok, up) == NX.Lv{C.BT(len, t), L2.ok(LG(n, len, t, y, j, ok, up)), L2.up(LG(n, len, t, y, j, ok, up))} : NX.Lv}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +j1 = (j + 1 : U32)
      +ok1 = ok && NX.isl(y)
      +up1 = up && U32.is_lt(y, 97)
      +z = C.AT(len, t, j1)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j1), (C.BT(len, t), z), C.at_pair_t(len, t, j1)) :
        {NX.lets.go(m, _, j1, ok1, up1) == NX.Lv{C.BT(len, t), L2.ok(LG(m, len, t, z, j1, ok1, up1)), L2.up(LG(m, len, t, z, j1, ok1, up1))} : NX.Lv}
      lg_t(m, len, t, z, j1, ok1, up1)

def LETS(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> L2:
  LG(U32.to_nat((to - from : U32)), len, t, C.AT(len, t, from), from, True{}, True{})

def lets_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) ->
  {NX.lets(C.BT(len, t), from, to) == NX.Lv{C.BT(len, t), L2.ok(LETS(len, t, from, to)), L2.up(LETS(len, t, from, to))} : NX.Lv}:
  +x = C.AT(len, t, from)
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), from), (C.BT(len, t), x), C.at_pair_t(len, t, from)) :
    {NX.lets.go(U32.to_nat((to - from : U32)), _, from, True{}, True{}) == NX.Lv{C.BT(len, t), L2.ok(LETS(len, t, from, to)), L2.up(LETS(len, t, from, to))} : NX.Lv}
  lg_t(U32.to_nat((to - from : U32)), len, t, x, from, True{}, True{})

# ---------------------------------------------------------------------------
# Alleles equal up to case: feq; distinct: dis.go
# ---------------------------------------------------------------------------

def at2_t(+len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32) ->
  {BY.at2(C.BT(len, t), i, j) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}:
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), i), (C.BT(len, t), C.AT(len, t, i)), C.at_pair_t(len, t, i)) :
    {BY.at2.fin(j, _) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
    {BY.at2.fin2(C.AT(len, t, i), _) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}
  {==}

# feq.go on the mirror: x, y are bytes i, j.
def FG(n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +y: U32, +i: U32, +j: U32, acc: Bool) -> Bool:
  match n:
    case 0n:
      acc
    case 1n+m:
      FG(m, len, t, C.AT(len, t, (i + 1 : U32)), C.AT(len, t, (j + 1 : U32)), (i + 1 : U32), (j + 1 : U32), acc && U32.is_zero(((x .^. y : U32) .&. 223 : U32)))

def fg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +y: U32, +i: U32, +j: U32, +acc: Bool) ->
  {NX.feq.go(n, (C.BT(len, t), (x, y)), i, j, acc) == (C.BT(len, t), FG(n, len, t, x, y, i, j, acc)) : D.Bytes & Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +i1 = (i + 1 : U32)
      +j1 = (j + 1 : U32)
      +acc1 = acc && U32.is_zero(((x .^. y : U32) .&. 223 : U32))
      +x1 = C.AT(len, t, i1)
      +y1 = C.AT(len, t, j1)
      %Equal.sym(D.Bytes & (U32 & U32), BY.at2(C.BT(len, t), i1, j1), (C.BT(len, t), (x1, y1)), at2_t(len, t, i1, j1)) :
        {NX.feq.go(m, _, i1, j1, acc1) == (C.BT(len, t), FG(m, len, t, x1, y1, i1, j1, acc1)) : D.Bytes & Bool}
      fg_t(m, len, t, x1, y1, i1, j1, acc1)

def FQI(same: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +n: U32) -> Bool:
  match same:
    case True{}:
      FG(U32.to_nat(n), len, t, C.AT(len, t, i), C.AT(len, t, j), i, j, True{})
    case False{}:
      False{}

def fqi_t(+same: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +n: U32) ->
  {NX.feq.if(same, C.BT(len, t), i, j, n) == (C.BT(len, t), FQI(same, len, t, i, j, n)) : D.Bytes & Bool}:
  match same:
    case True{}:
      %Equal.sym(D.Bytes & (U32 & U32), BY.at2(C.BT(len, t), i, j), (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))), at2_t(len, t, i, j)) :
        {NX.feq.go(U32.to_nat(n), _, i, j, True{}) == (C.BT(len, t), FG(U32.to_nat(n), len, t, C.AT(len, t, i), C.AT(len, t, j), i, j, True{})) : D.Bytes & Bool}
      fg_t(U32.to_nat(n), len, t, C.AT(len, t, i), C.AT(len, t, j), i, j, True{})
    case False{}:
      {==}

def FEQ(+len: U32, +t: AT.Tree<U32>, +x: NX.Ap, +y: NX.Ap) -> Bool:
  FQI(U32.is_eq(NX.Ap.ln(x), NX.Ap.ln(y)), len, t, NX.Ap.st(x), NX.Ap.st(y), NX.Ap.ln(x))

def feq_t(+len: U32, +t: AT.Tree<U32>, +x: NX.Ap, +y: NX.Ap) ->
  {NX.feq(C.BT(len, t), x, y) == (C.BT(len, t), FEQ(len, t, x, y)) : D.Bytes & Bool}:
  fqi_t(U32.is_eq(NX.Ap.ln(x), NX.Ap.ln(y)), len, t, NX.Ap.st(x), NX.Ap.st(y), NX.Ap.ln(x))

def DO(ok: Bool, +len: U32, +t: AT.Tree<U32>, +x: NX.Ap, +p: NX.Ap) -> Bool:
  match ok:
    case True{}:
      Bool.not(FEQ(len, t, x, p))
    case False{}:
      False{}

def do_t(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +x: NX.Ap, +p: NX.Ap) ->
  {NX.dis.one(ok, C.BT(len, t), x, p) == (C.BT(len, t), DO(ok, len, t, x, p)) : D.Bytes & Bool}:
  match ok:
    case True{}:
      %Equal.sym(D.Bytes & Bool, NX.feq(C.BT(len, t), x, p), (C.BT(len, t), FEQ(len, t, x, p)), feq_t(len, t, x, p)) :
        {NX.dis.neg(_) == (C.BT(len, t), Bool.not(FEQ(len, t, x, p))) : D.Bytes & Bool}
      {==}
    case False{}:
      {==}

# dis.go on the mirror.
def DG(ps: List<&2, NX.Ap>, +len: U32, +t: AT.Tree<U32>, ok: Bool, +x: NX.Ap) -> Bool:
  match ps:
    case Nil{}:
      ok
    case +p <> q:
      DG(q, len, t, DO(ok, len, t, x, p), x)

def dg_t(+ps: List<&2, NX.Ap>, +len: U32, +t: AT.Tree<U32>, +ok: Bool, +x: NX.Ap) ->
  {NX.dis.go(ps, (C.BT(len, t), ok), x) == (C.BT(len, t), DG(ps, len, t, ok, x)) : D.Bytes & Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +q:
      %Equal.sym(D.Bytes & Bool, NX.dis.one(ok, C.BT(len, t), x, p), (C.BT(len, t), DO(ok, len, t, x, p)), do_t(ok, len, t, x, p)) :
        {NX.dis.go(q, _, x) == (C.BT(len, t), DG(q, len, t, DO(ok, len, t, x, p), x)) : D.Bytes & Bool}
      dg_t(q, len, t, DO(ok, len, t, x, p), x)

# ---------------------------------------------------------------------------
# The ALT alleles: alts.go
# ---------------------------------------------------------------------------

# An Xs without its buffer (the ALT field's end e is fixed).
type XD is Data:
  XD{a: U32, ps: List<&2, NX.Ap>, ok: Bool, up: Bool, more: Bool}

def XD.ok(x: XD) -> Bool:
  match x:
    case XD{a, ps, ok, up, m}:
      ok

def XD.ps(x: XD) -> List<&2, NX.Ap>:
  match x:
    case XD{a, ps, ok, up, m}:
      ps

def XD.up(x: XD) -> Bool:
  match x:
    case XD{a, ps, ok, up, m}:
      up

def XR(+len: U32, +t: AT.Tree<U32>, +e: U32, x: XD) -> NX.Xs:
  match x:
    case XD{a, ps, ok, up, m}:
      NX.Xs{C.BT(len, t), a, e, ps, ok, up, m}

# alt.step on the mirror.
def XS(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, ok: Bool, up: Bool) -> XD:
  +c = M.F1(len, t, a, e, 44)
  +ap = {NX.Ap{a, (c - a : U32)} : NX.Ap}
  +ok2 = (ok && L2.ok(LETS(len, t, a, c)) && U32.is_lt(a, c)) && DG(ps, len, t, True{}, ap)
  XD{(c + 1 : U32), ap <> ps, ok2, up && L2.up(LETS(len, t, a, c)), ok2 && U32.is_lt(c, e)}

def xs_t(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +ps: List<&2, NX.Ap>, +ok: Bool, +up: Bool) ->
  {NX.alt.step(NX.Xs{C.BT(len, t), a, e, ps, ok, up, True{}}) == XR(len, t, e, XS(len, t, e, a, ps, ok, up)) : NX.Xs}:
  +c = M.F1(len, t, a, e, 44)
  +ap = {NX.Ap{a, (c - a : U32)} : NX.Ap}
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, e, 44), (C.BT(len, t), c), M.ff1(len, t, a, e, 44)) :
    {NX.alt.c(a, e, ps, ok, up, _) == XR(len, t, e, XS(len, t, e, a, ps, ok, up)) : NX.Xs}
  %Equal.sym(NX.Lv, NX.lets(C.BT(len, t), a, c), NX.Lv{C.BT(len, t), L2.ok(LETS(len, t, a, c)), L2.up(LETS(len, t, a, c))}, lets_t(len, t, a, c)) :
    {NX.alt.l(a, c, e, ps, ok, up, _) == XR(len, t, e, XS(len, t, e, a, ps, ok, up)) : NX.Xs}
  %Equal.sym(D.Bytes & Bool, NX.dis.go(ps, (C.BT(len, t), True{}), ap), (C.BT(len, t), DG(ps, len, t, True{}, ap)), dg_t(ps, len, t, True{}, ap)) :
    {NX.alt.d(ap, c, e, ps, ok && L2.ok(LETS(len, t, a, c)) && U32.is_lt(a, c), up && L2.up(LETS(len, t, a, c)), _) == XR(len, t, e, XS(len, t, e, a, ps, ok, up)) : NX.Xs}
  {==}

# alts.go on the mirror.
def XG(n: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, x: XD) -> XD:
  match n x:
    case 0n XD{a, ps, ok, up, m}:
      XD{a, ps, False{}, up, m}
    case 1n+k XD{a, ps, ok, up, False{}}:
      XD{a, ps, ok, up, False{}}
    case 1n+k XD{+a, +ps, ok, up, True{}}:
      XG(k, len, t, e, XS(len, t, e, a, ps, ok, up))

def xg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, +x: XD) ->
  {NX.alts.go(n, XR(len, t, e, x)) == XR(len, t, e, XG(n, len, t, e, x)) : NX.Xs}:
  match n x:
    case 0n XD{+a, +ps, +ok, +up, +m}:
      {==}
    case 1n+k XD{+a, +ps, +ok, +up, False{}}:
      {==}
    case 1n+k XD{+a, +ps, +ok, +up, True{}}:
      %Equal.sym(NX.Xs, NX.alt.step(NX.Xs{C.BT(len, t), a, e, ps, ok, up, True{}}), XR(len, t, e, XS(len, t, e, a, ps, ok, up)), xs_t(len, t, e, a, ps, ok, up)) :
        {NX.alts.go(k, _) == XR(len, t, e, XG(k, len, t, e, XS(len, t, e, a, ps, ok, up))) : NX.Xs}
      xg_t(k, len, t, e, XS(len, t, e, a, ps, ok, up))

# ---------------------------------------------------------------------------
# INFO's stale keys: nostale
# ---------------------------------------------------------------------------

def LO(ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) -> Bool:
  match ok:
    case True{}:
      U32.is_eq(C.AT(len, t, j), k)
    case False{}:
      False{}

def lo_t(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) ->
  {NX.lit.one(ok, C.BT(len, t), k, j) == (C.BT(len, t), LO(ok, len, t, k, j)) : D.Bytes & Bool}:
  match ok:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {NX.lit.eq(k, _) == (C.BT(len, t), U32.is_eq(C.AT(len, t, j), k)) : D.Bytes & Bool}
      {==}
    case False{}:
      {==}

# lit.go on the mirror.
def LIT(ks: List<&2, U32>, +len: U32, +t: AT.Tree<U32>, ok: Bool, +j: U32) -> Bool:
  match ks:
    case Nil{}:
      ok
    case +k <> q:
      LIT(q, len, t, LO(ok, len, t, k, j), (j + 1 : U32))

def lit_t(+ks: List<&2, U32>, +len: U32, +t: AT.Tree<U32>, +ok: Bool, +j: U32) ->
  {NX.lit.go(ks, (C.BT(len, t), ok), j) == (C.BT(len, t), LIT(ks, len, t, ok, j)) : D.Bytes & Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +q:
      %Equal.sym(D.Bytes & Bool, NX.lit.one(ok, C.BT(len, t), k, j), (C.BT(len, t), LO(ok, len, t, k, j)), lo_t(ok, len, t, k, j)) :
        {NX.lit.go(q, _, (j + 1 : U32)) == (C.BT(len, t), LIT(q, len, t, LO(ok, len, t, k, j), (j + 1 : U32))) : D.Bytes & Bool}
      lit_t(q, len, t, LO(ok, len, t, k, j), (j + 1 : U32))

def K6(hit: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      LIT([72, 79, 77, 83, 69, 81], len, t, True{}, j)

def k6_t(+hit: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) ->
  {NX.key6((C.BT(len, t), hit), j) == (C.BT(len, t), K6(hit, len, t, j)) : D.Bytes & Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      lit_t([72, 79, 77, 83, 69, 81], len, t, True{}, j)

def KIF(two: Bool, five: Bool, six: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) -> Bool:
  match two five six:
    case True{} _ _:
      LIT([65, 65], len, t, True{}, j)
    case False{} True{} _:
      LIT([67, 73, 71, 65, 82], len, t, True{}, j)
    case False{} False{} True{}:
      K6(LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j), len, t, j)
    case False{} False{} False{}:
      False{}

def kif_t(+two: Bool, +five: Bool, +six: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) ->
  {NX.key.if(two, five, six, C.BT(len, t), j) == (C.BT(len, t), KIF(two, five, six, len, t, j)) : D.Bytes & Bool}:
  match two five six:
    case True{} _ _:
      lit_t([65, 65], len, t, True{}, j)
    case False{} True{} _:
      lit_t([67, 73, 71, 65, 82], len, t, True{}, j)
    case False{} False{} True{}:
      +h = LIT([72, 79, 77, 76, 69, 78], len, t, True{}, j)
      %Equal.sym(D.Bytes & Bool, NX.lit.go([72, 79, 77, 76, 69, 78], (C.BT(len, t), True{}), j), (C.BT(len, t), h), lit_t([72, 79, 77, 76, 69, 78], len, t, True{}, j)) :
        {NX.key6(_, j) == (C.BT(len, t), K6(h, len, t, j)) : D.Bytes & Bool}
      k6_t(h, len, t, j)
    case False{} False{} False{}:
      {==}

# The n bytes from j are AA, CIGAR, HOMLEN or HOMSEQ.
def KEY(+len: U32, +t: AT.Tree<U32>, +j: U32, +n: U32) -> Bool:
  KIF(U32.is_eq(n, 2), U32.is_eq(n, 5), U32.is_eq(n, 6), len, t, j)

def key_t(+len: U32, +t: AT.Tree<U32>, +j: U32, +n: U32) ->
  {NX.key(C.BT(len, t), j, n) == (C.BT(len, t), KEY(len, t, j, n)) : D.Bytes & Bool}:
  kif_t(U32.is_eq(n, 2), U32.is_eq(n, 5), U32.is_eq(n, 6), len, t, j)

# An Sk without its buffer (INFO's end to is fixed).
type SD is Data:
  SD{j: U32, ok: Bool, more: Bool}

def SR(+len: U32, +t: AT.Tree<U32>, +to: U32, x: SD) -> NX.Sk:
  match x:
    case SD{j, ok, m}:
      NX.Sk{C.BT(len, t), j, to, ok, m}

def SW(+ok: Bool, end: Bool, +sm: U32) -> SD:
  match end:
    case True{}:
      SD{sm, ok, False{}}
    case False{}:
      SD{(sm + 1 : U32), ok, ok}

def sw_t(+ok: Bool, +end: Bool, +sm: U32, +len: U32, +t: AT.Tree<U32>, +to: U32) ->
  {NX.sk.w(ok, end, C.BT(len, t), sm, to) == SR(len, t, to, SW(ok, end, sm)) : NX.Sk}:
  match end:
    case True{}:
      {==}
    case False{}:
      {==}

def SE(+ok: Bool, end: Bool, semi: Bool, +len: U32, +t: AT.Tree<U32>, +ke: U32, +to: U32) -> SD:
  match end semi:
    case True{} _:
      SD{ke, ok, False{}}
    case False{} True{}:
      SD{(ke + 1 : U32), ok, ok}
    case False{} False{}:
      SW(ok, U32.is_eq(M.F1(len, t, ke, to, 59), to), M.F1(len, t, ke, to, 59))

def se_t(+ok: Bool, +end: Bool, +semi: Bool, +len: U32, +t: AT.Tree<U32>, +ke: U32, +to: U32) ->
  {NX.sk.e(ok, end, semi, C.BT(len, t), ke, to) == SR(len, t, to, SE(ok, end, semi, len, t, ke, to)) : NX.Sk}:
  match end semi:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +sm = M.F1(len, t, ke, to, 59)
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), ke, to, 59), (C.BT(len, t), sm), M.ff1(len, t, ke, to, 59)) :
        {NX.sk.v(ok, to, _) == SR(len, t, to, SW(ok, U32.is_eq(sm, to), sm)) : NX.Sk}
      sw_t(ok, U32.is_eq(sm, to), sm, len, t, to)

# The entry at j: its key ends at KE (the first '=' or ';' or INFO's end).
def KE(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> U32:
  M.F2(len, t, j, to, 61, 59)

# sk.step on the mirror.
def SS(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> SD:
  +ke = KE(len, t, to, j)
  SE(Bool.not(KEY(len, t, j, (ke - j : U32))), U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), len, t, ke, to)

def ss_t(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32, +ok: Bool, +m: Bool) ->
  {NX.sk.step(NX.Sk{C.BT(len, t), j, to, ok, m}) == SR(len, t, to, SS(len, t, to, j)) : NX.Sk}:
  +ke = KE(len, t, to, j)
  +k = KEY(len, t, j, (ke - j : U32))
  %Equal.sym(D.Bytes & U32, F.find2(C.BT(len, t), j, to, 61, 59), (C.BT(len, t), ke), M.ff2(len, t, j, to, 61, 59)) :
    {NX.sk.k(j, to, _) == SR(len, t, to, SS(len, t, to, j)) : NX.Sk}
  %Equal.sym(D.Bytes & Bool, NX.key(C.BT(len, t), j, (ke - j : U32)), (C.BT(len, t), k), key_t(len, t, j, (ke - j : U32))) :
    {NX.sk.h(ke, to, _) == SR(len, t, to, SS(len, t, to, j)) : NX.Sk}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), ke), (C.BT(len, t), C.AT(len, t, ke)), C.at_pair_t(len, t, ke)) :
    {NX.sk.n(Bool.not(k), ke, to, _) == SR(len, t, to, SS(len, t, to, j)) : NX.Sk}
  se_t(Bool.not(k), U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), len, t, ke, to)

# sk.go on the mirror.
def SG(n: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, x: SD) -> Bool:
  match n x:
    case 0n SD{j, ok, m}:
      False{}
    case 1n+k SD{j, ok, False{}}:
      ok
    case 1n+k SD{+j, ok, True{}}:
      SG(k, len, t, to, SS(len, t, to, j))

def sg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +x: SD) ->
  {NX.sk.go(n, SR(len, t, to, x)) == (C.BT(len, t), SG(n, len, t, to, x)) : D.Bytes & Bool}:
  match n x:
    case 0n SD{+j, +ok, +m}:
      {==}
    case 1n+k SD{+j, +ok, False{}}:
      {==}
    case 1n+k SD{+j, +ok, True{}}:
      %Equal.sym(NX.Sk, NX.sk.step(NX.Sk{C.BT(len, t), j, to, ok, True{}}), SR(len, t, to, SS(len, t, to, j)), ss_t(len, t, to, j, ok, True{})) :
        {NX.sk.go(k, _) == (C.BT(len, t), SG(k, len, t, to, SS(len, t, to, j))) : D.Bytes & Bool}
      sg_t(k, len, t, to, SS(len, t, to, j))

def NOST(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> Bool:
  SG(U32.to_nat((to - from + 2 : U32)), len, t, to, SD{from, True{}, True{}})

def nost_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) ->
  {NX.nostale(C.BT(len, t), from, to) == (C.BT(len, t), NOST(len, t, from, to)) : D.Bytes & Bool}:
  sg_t(U32.to_nat((to - from + 2 : U32)), len, t, to, SD{from, True{}, True{}})

# ---------------------------------------------------------------------------
# The tests: fx.*, and NX.line
# ---------------------------------------------------------------------------

def FIF(ok: Bool, +p: NX.Fp) -> NX.Fp:
  match ok:
    case True{}:
      p
    case False{}:
      NX.No{}

def fif_t(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +p: NX.Fp) ->
  {NX.fx.if(ok, C.BT(len, t), p) == NX.Fr{C.BT(len, t), FIF(ok, p)} : NX.Fr}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def FCR(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool) -> NX.Fp:
  FIF(Bool.not(U32.is_eq(NX.Cut.e7(c), NX.Cut.lf(c)) && U32.is_eq(C.AT(len, t, (NX.Cut.lf(c) - 1 : U32)), 13)), NX.Fix{pos, c, als, up})

def FST(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool, ok: Bool) -> NX.Fp:
  match ok:
    case True{}:
      FCR(len, t, pos, c, als, up)
    case False{}:
      NX.No{}

def fst_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool, +ok: Bool) ->
  {NX.fx.st(pos, c, als, up, (C.BT(len, t), ok)) == NX.Fr{C.BT(len, t), FST(len, t, pos, c, als, up, ok)} : NX.Fr}:
  match ok:
    case True{}:
      +i = (NX.Cut.lf(c) - 1 : U32)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), i), (C.BT(len, t), C.AT(len, t, i)), C.at_pair_t(len, t, i)) :
        {NX.fx.cr(pos, c, als, up, _) == NX.Fr{C.BT(len, t), FCR(len, t, pos, c, als, up)} : NX.Fr}
      fif_t(Bool.not(U32.is_eq(NX.Cut.e7(c), NX.Cut.lf(c)) && U32.is_eq(C.AT(len, t, i), 13)), len, t, NX.Fix{pos, c, als, up})
    case False{}:
      {==}

def FINFO(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool, ok: Bool) -> NX.Fp:
  match ok:
    case True{}:
      FST(len, t, pos, c, als, up, NOST(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c)))
    case False{}:
      NX.No{}

def finfo_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool, +ok: Bool) ->
  {NX.fx.info(pos, c, als, up, (C.BT(len, t), ok)) == NX.Fr{C.BT(len, t), FINFO(len, t, pos, c, als, up, ok)} : NX.Fr}:
  match ok:
    case True{}:
      +ns = NOST(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c))
      %Equal.sym(D.Bytes & Bool, NX.nostale(C.BT(len, t), (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c)), (C.BT(len, t), ns), nost_t(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c))) :
        {NX.fx.st(pos, c, als, up, _) == NX.Fr{C.BT(len, t), FST(len, t, pos, c, als, up, ns)} : NX.Fr}
      fst_t(len, t, pos, c, als, up, ns)
    case False{}:
      {==}

def FALTS(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, x: XD) -> NX.Fp:
  match x:
    case XD{a, ps, True{}, up, m}:
      FINFO(len, t, pos, c, NX.rev_ap(ps, Nil{}), up, M.NE(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c)))
    case XD{a, ps, False{}, up, m}:
      NX.No{}

def falts_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +e: U32, +x: XD) ->
  {NX.fx.alts(pos, c, XR(len, t, e, x)) == NX.Fr{C.BT(len, t), FALTS(len, t, pos, c, x)} : NX.Fr}:
  match x:
    case XD{+a, +ps, True{}, +up, +m}:
      +ne = M.NE(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c))
      +als = NX.rev_ap(ps, Nil{})
      %Equal.sym(D.Bytes & Bool, NF.noend(C.BT(len, t), (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c)), (C.BT(len, t), ne), M.noend_t(len, t, (NX.Cut.e6(c) + 1 : U32), NX.Cut.e7(c))) :
        {NX.fx.info(pos, c, als, up, _) == NX.Fr{C.BT(len, t), FINFO(len, t, pos, c, als, up, ne)} : NX.Fr}
      finfo_t(len, t, pos, c, als, up, ne)
    case XD{+a, +ps, False{}, +up, +m}:
      {==}

# The ALT loop's start: REF at s3 (to e3), the ALT field from e3 + 1 to e4.
def X0(+s3: U32, +e3: U32, +up: Bool) -> XD:
  XD{(e3 + 1 : U32), [NX.Ap{s3, (e3 - s3 : U32)}], True{}, up, True{}}

def FRIF(ok: Bool, +len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +s3: U32, +e3: U32, +e4: U32, +up: Bool) -> NX.Fp:
  match ok:
    case True{}:
      FALTS(len, t, pos, c, XG(17n, len, t, e4, X0(s3, e3, up)))
    case False{}:
      NX.No{}

def frif_t(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +s3: U32, +e3: U32, +e4: U32, +up: Bool) ->
  {NX.fx.ref.if(ok, pos, c, C.BT(len, t), s3, e3, e4, up) == NX.Fr{C.BT(len, t), FRIF(ok, len, t, pos, c, s3, e3, e4, up)} : NX.Fr}:
  match ok:
    case True{}:
      +x = XG(17n, len, t, e4, X0(s3, e3, up))
      %Equal.sym(NX.Xs, NX.alts.go(17n, XR(len, t, e4, X0(s3, e3, up))), XR(len, t, e4, x), xg_t(17n, len, t, e4, X0(s3, e3, up))) :
        {NX.fx.alts(pos, c, _) == NX.Fr{C.BT(len, t), FALTS(len, t, pos, c, x)} : NX.Fr}
      falts_t(len, t, pos, c, e4, x)
    case False{}:
      {==}

def FREF(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, ok: Bool, +up: Bool) -> NX.Fp:
  match c ok:
    case NF.Cut8{e0, e1, +e2, +e3, +e4, e5, e6, e7, lf} True{}:
      FRIF(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4), len, t, pos, c, (e2 + 1 : U32), e3, e4, up)
    case _ _:
      NX.No{}

def fref_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +c: NF.Cut, +ok: Bool, +up: Bool) ->
  {NX.fx.ref(pos, c, NX.Lv{C.BT(len, t), ok, up}) == NX.Fr{C.BT(len, t), FREF(len, t, pos, c, ok, up)} : NX.Fr}:
  match c ok:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf} True{}:
      frif_t(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4), len, t, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, (e2 + 1 : U32), e3, e4, up)
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf} False{}:
      {==}
    case NF.Short{} _:
      {==}
    case NF.Part{} _:
      {==}

def FPOS(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut, ok: Bool, +pos: U32) -> NX.Fp:
  match c ok:
    case NF.Cut8{e0, e1, +e2, +e3, e4, e5, e6, e7, lf} True{}:
      FREF(len, t, pos, c, L2.ok(LETS(len, t, (e2 + 1 : U32), e3)), L2.up(LETS(len, t, (e2 + 1 : U32), e3)))
    case _ _:
      NX.No{}

def fpos_t(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut, +ok: Bool, +pos: U32) ->
  {NX.fx.pos(c, NF.Bv{C.BT(len, t), ok, pos}) == NX.Fr{C.BT(len, t), FPOS(len, t, c, ok, pos)} : NX.Fr}:
  match c ok:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf} True{}:
      +lv = LETS(len, t, (e2 + 1 : U32), e3)
      +cc = {NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Cut}
      %Equal.sym(NX.Lv, NX.lets(C.BT(len, t), (e2 + 1 : U32), e3), NX.Lv{C.BT(len, t), L2.ok(lv), L2.up(lv)}, lets_t(len, t, (e2 + 1 : U32), e3)) :
        {NX.fx.ref(pos, cc, _) == NX.Fr{C.BT(len, t), FREF(len, t, pos, cc, L2.ok(lv), L2.up(lv))} : NX.Fr}
      fref_t(len, t, pos, cc, L2.ok(lv), L2.up(lv))
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf} False{}:
      {==}
    case NF.Short{} _:
      {==}
    case NF.Part{} _:
      {==}

def FCUT(+len: U32, +t: AT.Tree<U32>, c: NF.Cut) -> NX.Fp:
  match c:
    case NF.Cut8{+e0, +e1, e2, e3, e4, e5, e6, e7, lf}:
      FPOS(len, t, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)), M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)))
    case NF.Short{}:
      NX.No{}
    case NF.Part{}:
      NX.No{}

def fcut_t(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut) ->
  {NX.fx.cut(NF.Cr{C.BT(len, t), c}) == NX.Fr{C.BT(len, t), FCUT(len, t, c)} : NX.Fr}:
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      +nv = M.NUM(len, t, (e0 + 1 : U32), e1)
      +cc = {NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf} : NF.Cut}
      %Equal.sym(NF.Bv, NF.num(C.BT(len, t), (e0 + 1 : U32), e1), NF.Bv{C.BT(len, t), M.Nv.ok(nv), M.Nv.v(nv)}, M.num_t(len, t, (e0 + 1 : U32), e1)) :
        {NX.fx.pos(cc, _) == NX.Fr{C.BT(len, t), FPOS(len, t, cc, M.Nv.ok(nv), M.Nv.v(nv))} : NX.Fr}
      fpos_t(len, t, cc, M.Nv.ok(nv), M.Nv.v(nv))
    case NF.Short{}:
      {==}
    case NF.Part{}:
      {==}

def FX(+len: U32, +t: AT.Tree<U32>, +s: U32) -> NX.Fp:
  FCUT(len, t, M.MC(len, t, s))

def line_t(+len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {NX.line(C.BT(len, t), s) == NX.Fr{C.BT(len, t), FX(len, t, s)} : NX.Fr}:
  %Equal.sym(NF.Cr, NF.cut(C.BT(len, t), s), NF.Cr{C.BT(len, t), M.MC(len, t, s)}, M.cut_t(len, t, s)) :
    {NX.fx.cut(_) == NX.Fr{C.BT(len, t), FX(len, t, s)} : NX.Fr}
  fcut_t(len, t, M.MC(len, t, s))
