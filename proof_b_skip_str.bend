import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./proof_c_defs.bend as Q
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_c_pre_key.bend as K
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

# The out-of-scope tests on bytes (NF.letters, NF.oos) as the text's: REF's
# bytes all letters is B.Text.all_letters of REF's text; ALT passing oos is
# no empty allele and some allele not all letters (B.Text.any_empty and
# B.Text.any_not_letters of its comma pieces).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def LL() -> Data:
  List<&2, List<&2, U32>>

# ---------------------------------------------------------------------------
# Letters
# ---------------------------------------------------------------------------

# Every byte is a letter (as Char.is_alpha reads it).
def AA(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> r:
      Bool.and(NF.alpha(x), AA(r))

def aa_let(+xs: List<&2, U32>) -> {B.Text.all_letters(Norm.chars(xs)) == AA(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, B.Text.all_letters(Norm.chars(r)), AA(r), aa_let(r)) : {Bool.and(Char.is_alpha(Chr{x}), _) == Bool.and(NF.alpha(x), AA(r)) : Bool}
      {==}

# letters.go on the mirror: the bytes from j.
def lt_v(+m: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +ok: Bool,
  +hj: {Nat.is_le(Nat.add(n(j), m), n(len)) == True{} : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {M.LTG(m, len, t, C.AT(len, t, j), j, ok) == Bool.and(ok, AA(D.slice(Q.xs(len, t), n(j), m))) : Bool}:
  match m:
    case 0n:
      +Lz = List.drop(&2, U32, Q.xs(len, t), n(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Lz, 0n), Nil{}, SQ.take_zero(Lz)) : {ok == Bool.and(ok, AA(_)) : Bool}
      Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok))
    case 1n+k:
      +VW = Q.xs(len, t)
      +y = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +S1 = D.slice(VW, n(j1), k)
      +ok1 = Bool.and(ok, NF.alpha(y))
      %Equal.sym(List<&2, U32>, D.slice(VW, n(j), 1n+k), y <> D.slice(VW, Nat.add(n(j), 1n), k), PSm.slice_cons(VW, n(j), k, y, G.get_of(len, t, d, j, k, h, hj))) :
        {M.LTG(k, len, t, C.AT(len, t, j1), j1, ok1) == Bool.and(ok, AA(_)) : Bool}
      %G.inc_of(len, t, d, j, k, h, hj) :
        {M.LTG(k, len, t, C.AT(len, t, j1), j1, ok1) == Bool.and(ok, Bool.and(NF.alpha(y), AA(D.slice(VW, _, k)))) : Bool}
      %LS.and_assoc(ok, NF.alpha(y), AA(S1)) :
        {M.LTG(k, len, t, C.AT(len, t, j1), j1, ok1) == _ : Bool}
      lt_v(k, len, t, d, j1, ok1, G.nx_of(len, t, d, j, k, h, hj), h)

# Bytes a .. c-1: NF.letters.
def lett_v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_le(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {M.LETT(len, t, a, c) == AA(D.slice(Q.xs(len, t), n(a), n((c - a : U32)))) : Bool}:
  +hs = LP.sub_u(c, a, hac)
  +hj = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(c), Nat.add(n(a), n((c - a : U32))),
    Equal.sym(Nat, Nat.add(n(a), n((c - a : U32))), n(c), Equal.trans(Nat, Nat.add(n(a), n((c - a : U32))), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
      Equal.cong(Nat, Nat, z => Nat.add(n(a), z), n((c - a : U32)), Nat.sub(n(c), n(a)), hs), N.le_sub_add(n(a), n(c), hac))), hcl)
  lt_v(n((c - a : U32)), len, t, d, a, True{}, hj, h)

# The text of bytes a .. c-1 (a < c) is letters exactly when NF.letters
# passes on them.
def lett_s(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_lt(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {B.Text.is_letters(Q.fld(Q.xs(len, t), n(a), n(c))) == M.LETT(len, t, a, c) : Bool}:
  +X = Q.xs(len, t)
  +m = Nat.sub(n(c), Nat.add(n(a), 1n))
  +hle = N.lt_to_le(n(a), n(c), hac)
  +hs = LP.sub_u(c, a, hle)
  +hj = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(c), Nat.add(n(a), 1n+m),
    Equal.sym(Nat, Nat.add(n(a), 1n+m), n(c), Equal.trans(Nat, Nat.add(n(a), 1n+m), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
      Equal.cong(Nat, Nat, z => Nat.add(n(a), z), 1n+m, Nat.sub(n(c), n(a)), Equal.sym(Nat, Nat.sub(n(c), n(a)), 1n+m, LS.sub_lt(n(c), n(a), hac))),
      N.le_sub_add(n(a), n(c), hle))), hcl)
  %Equal.sym(Nat, Nat.sub(n(c), n(a)), 1n+m, LS.sub_lt(n(c), n(a), hac)) : {B.Text.is_letters(Norm.chars(D.slice(X, n(a), _))) == M.LETT(len, t, a, c) : Bool}
  %Equal.sym(List<&2, U32>, D.slice(X, n(a), 1n+m), C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m), PSm.slice_cons(X, n(a), m, C.AT(len, t, a), G.get_of(len, t, d, a, m, h, hj))) :
    {B.Text.is_letters(Norm.chars(_)) == M.LETT(len, t, a, c) : Bool}
  %Equal.sym(Bool, M.LETT(len, t, a, c), AA(D.slice(X, n(a), n((c - a : U32)))), lett_v(len, t, d, a, c, h, hle, hcl)) : {B.Text.all_letters(Norm.chars(C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m))) == _ : Bool}
  %Equal.sym(Nat, n((c - a : U32)), Nat.sub(n(c), n(a)), hs) : {B.Text.all_letters(Norm.chars(C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m))) == AA(D.slice(X, n(a), _)) : Bool}
  %Equal.sym(Nat, Nat.sub(n(c), n(a)), 1n+m, LS.sub_lt(n(c), n(a), hac)) : {B.Text.all_letters(Norm.chars(C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m))) == AA(D.slice(X, n(a), _)) : Bool}
  %Equal.sym(List<&2, U32>, D.slice(X, n(a), 1n+m), C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m), PSm.slice_cons(X, n(a), m, C.AT(len, t, a), G.get_of(len, t, d, a, m, h, hj))) :
    {B.Text.all_letters(Norm.chars(C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m))) == AA(_) : Bool}
  aa_let(C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m))

# ---------------------------------------------------------------------------
# The ALT alleles
# ---------------------------------------------------------------------------

# The comma pieces of bytes a .. e-1, as text.
def PS(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> List<&2, String>:
  AL.mapc(FD.split(D.slice(Q.xs(len, t), n(a), Nat.sub(n(e), n(a))), 44))

# What oos passing says of the pieces from a on (odd: one before a was not
# all letters).
def KH(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +odd: Bool) -> Type:
  {B.Text.any_empty(PS(len, t, e, a)) == False{} : Bool} & {Bool.or(odd, B.Text.any_not_letters(PS(len, t, e, a))) == True{} : Bool}

# The next comma from a (or e).
def CM(+len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32) -> U32:
  M.F1(len, t, a, e, 44)

def ncm(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}) ->
  {n(CM(len, t, e, a)) == D.first(Q.xs(len, t), n(a), n(e), 44) : Nat}:
  M.f1_view(len, t, d, a, e, 44, h, LP.le_u(a, e, hae), he, {==})

def cm_rg(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}) ->
  {Bool.and(Nat.is_le(n(a), n(CM(len, t, e, a))), Nat.is_le(n(CM(len, t, e, a)), n(e))) == True{} : Bool}:
  AB.subst(Nat, z => {Bool.and(Nat.is_le(n(a), z), Nat.is_le(z, n(e))) == True{} : Bool}, D.first(Q.xs(len, t), n(a), n(e), 44), n(CM(len, t, e, a)),
    Equal.sym(Nat, n(CM(len, t, e, a)), D.first(Q.xs(len, t), n(a), n(e), 44), ncm(len, t, d, e, a, h, he, hae)),
    PL.first_range(Q.xs(len, t), n(a), n(e), 44, hae, K.hlx(len, t, d, n(e), h, he)))

# The pieces from a: the first (a .. c-1), then the rest.
def pse(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool}) ->
  {PS(len, t, e, a) == Q.fld(Q.xs(len, t), n(a), n(CM(len, t, e, a))) <> AL.mapc(LS.tsplit(D.slice(Q.xs(len, t), n(CM(len, t, e, a)), Nat.sub(n(e), n(CM(len, t, e, a)))), 44)) : List<&2, String>}:
  +X = Q.xs(len, t)
  +f = D.first(X, n(a), n(e), 44)
  +sp = Equal.cong(LL(), List<&2, String>, z => AL.mapc(z), FD.split(D.slice(X, n(a), Nat.sub(n(e), n(a))), 44), Con{D.slice(X, n(a), Nat.sub(f, n(a))), LS.tsplit(D.slice(X, f, Nat.sub(n(e), f)), 44)}, LS.spl(X, n(a), n(e), 44))
  AB.subst(Nat, z => {PS(len, t, e, a) == Q.fld(X, n(a), z) <> AL.mapc(LS.tsplit(D.slice(X, z, Nat.sub(n(e), z)), 44)) : List<&2, String>}, f, n(CM(len, t, e, a)),
    Equal.sym(Nat, n(CM(len, t, e, a)), f, ncm(len, t, d, e, a, h, he, hae)), sp)

# A piece a .. c-1 with a < c is not empty.
def ne_fld(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hac: {Nat.is_lt(n(a), n(c)) == True{} : Bool}, +hcl: {Nat.is_le(n(c), n(len)) == True{} : Bool}) ->
  {String.is_empty(Q.fld(Q.xs(len, t), n(a), n(c))) == False{} : Bool}:
  +X = Q.xs(len, t)
  +m = Nat.sub(n(c), Nat.add(n(a), 1n))
  +hle = N.lt_to_le(n(a), n(c), hac)
  +hj = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(c), Nat.add(n(a), 1n+m),
    Equal.sym(Nat, Nat.add(n(a), 1n+m), n(c), Equal.trans(Nat, Nat.add(n(a), 1n+m), Nat.add(n(a), Nat.sub(n(c), n(a))), n(c),
      Equal.cong(Nat, Nat, z => Nat.add(n(a), z), 1n+m, Nat.sub(n(c), n(a)), Equal.sym(Nat, Nat.sub(n(c), n(a)), 1n+m, LS.sub_lt(n(c), n(a), hac))),
      N.le_sub_add(n(a), n(c), hle))), hcl)
  %Equal.sym(Nat, Nat.sub(n(c), n(a)), 1n+m, LS.sub_lt(n(c), n(a), hac)) : {String.is_empty(Norm.chars(D.slice(X, n(a), _))) == False{} : Bool}
  %Equal.sym(List<&2, U32>, D.slice(X, n(a), 1n+m), C.AT(len, t, a) <> D.slice(X, Nat.add(n(a), 1n), m), PSm.slice_cons(X, n(a), m, C.AT(len, t, a), G.get_of(len, t, d, a, m, h, hj))) :
    {String.is_empty(Norm.chars(_)) == False{} : Bool}
  {==}

def kd_false(+q: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +odd: Bool) -> {M.KG(q, len, t, e, M.KD{a, False{}, odd, False{}}) == False{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+k:
      {==}

def kg_end(+q: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32, +a: U32, +odd: Bool, +hk: {M.KG(q, len, t, e, M.KD{a, True{}, odd, False{}}) == True{} : Bool}) -> {odd == True{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({odd == True{} : Bool}, LS.ft(hk))
    case 1n+k:
      hk

def KIH(+q: Nat, +len: U32, +t: AT.Tree<U32>, +e: U32) -> Type:
  @aa: U32 -> @od: Bool -> {Nat.is_le(n(aa), n(e)) == True{} : Bool} -> {M.KG(q, len, t, e, M.KD{aa, True{}, od, True{}}) == True{} : Bool} -> KH(len, t, e, aa, od)

def or_ft(+a: Bool, +b: Bool, +c: Bool, +h: {Bool.or(Bool.or(a, b), c) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def or_f0(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, False{})) == True{} : Bool}:
  %Equal.sym(Bool, Bool.or(b, False{}), b, N.or_false_r(b)) : {Bool.or(a, _) == True{} : Bool}
  h

def not_eq(+x: Bool, +y: Bool, +h: {x == y : Bool}) -> {Bool.not(x) == Bool.not(y) : Bool}:
  Equal.cong(Bool, Bool, z => Bool.not(z), x, y, h)

# The allele at a, then the rest from the comma after it.
def kcons(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +odd: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(a), n(CM(len, t, e, a))) == True{} : Bool}, +hce2: {Nat.is_lt(n(CM(len, t, e, a)), n(e)) == True{} : Bool},
  r: KH(len, t, e, (CM(len, t, e, a) + 1 : U32), Bool.or(odd, Bool.not(M.LETT(len, t, a, CM(len, t, e, a)))))) ->
  KH(len, t, e, a, odd):
  match r:
    case (+hae2, +han2):
      +X = Q.xs(len, t)
      +c = CM(len, t, e, a)
      +rg = cm_rg(len, t, d, e, a, h, he, hae)
      +hcl = N.le_trans(n(c), n(e), n(len), N.and_true_r(Nat.is_le(n(a), n(c)), Nat.is_le(n(c), n(e)), rg), he)
      +hcl2 = N.lt_le_trans(n(c), n(e), n(len), hce2, he)
      +ef = ncm(len, t, d, e, a, h, he, hae)
      +hit = AB.subst(Nat, z => {D.has(X, z, 44) == True{} : Bool}, D.first(X, n(a), n(e), 44), n(c), Equal.sym(Nat, n(c), D.first(X, n(a), n(e), 44), ef),
        PL.first_hit(X, n(a), n(e), 44, hae, K.hlx(len, t, d, n(e), h, he), AB.subst(Nat, z => {Nat.is_lt(z, n(e)) == True{} : Bool}, n(c), D.first(X, n(a), n(e), 44), ef, hce2)))
      +hg = LP.has_get(X, n(c), 44, hit)
      +i1 = LP.inc_len(len, t, d, c, h, hcl2)
      +R = PS(len, t, e, (c + 1 : U32))
      +tl = Equal.trans(List<&2, String>, AL.mapc(LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44)), AL.mapc(FD.split(D.slice(X, Nat.add(n(c), 1n), Nat.sub(n(e), Nat.add(n(c), 1n))), 44)), R,
        Equal.cong(LL(), List<&2, String>, z => AL.mapc(z), LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44), FD.split(D.slice(X, Nat.add(n(c), 1n), Nat.sub(n(e), Nat.add(n(c), 1n))), 44), LS.ts_lt(X, n(c), n(e), 44, hce2, hg)),
        Equal.cong(Nat, List<&2, String>, z => AL.mapc(FD.split(D.slice(X, z, Nat.sub(n(e), z)), 44)), Nat.add(n(c), 1n), n((c + 1 : U32)), Equal.sym(Nat, n((c + 1 : U32)), Nat.add(n(c), 1n), i1)))
      +F = Q.fld(X, n(a), n(c))
      +eps = Equal.trans(List<&2, String>, PS(len, t, e, a), F <> AL.mapc(LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44)), F <> R,
        pse(len, t, d, e, a, h, he, hae), Equal.cong(List<&2, String>, List<&2, String>, z => F <> z, AL.mapc(LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44)), R, tl))
      +hne = ne_fld(len, t, d, a, c, h, hlt, hcl)
      +hle = lett_s(len, t, d, a, c, h, hlt, hcl)
      (AB.subst(List<&2, String>, z => {B.Text.any_empty(z) == False{} : Bool}, F <> R, PS(len, t, e, a), Equal.sym(List<&2, String>, PS(len, t, e, a), F <> R, eps),
         %Equal.sym(Bool, String.is_empty(F), False{}, hne) : {Bool.or(_, B.Text.any_empty(R)) == False{} : Bool}; hae2),
       AB.subst(List<&2, String>, z => {Bool.or(odd, B.Text.any_not_letters(z)) == True{} : Bool}, F <> R, PS(len, t, e, a), Equal.sym(List<&2, String>, PS(len, t, e, a), F <> R, eps),
         %Equal.sym(Bool, B.Text.is_letters(F), M.LETT(len, t, a, c), hle) : {Bool.or(odd, Bool.or(Bool.not(_), B.Text.any_not_letters(R))) == True{} : Bool}; or_ft(odd, Bool.not(M.LETT(len, t, a, c)), B.Text.any_not_letters(R), han2)))

# One step of oos from the allele at a (none empty so far).
def kstep(+ac: Bool, +ce: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +odd: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool},
  +hac: {U32.is_lt(a, CM(len, t, e, a)) == ac : Bool}, +hce: {U32.is_lt(CM(len, t, e, a), e) == ce : Bool},
  +hk: {M.KG(q, len, t, e, M.KD{(CM(len, t, e, a) + 1 : U32), ac, Bool.or(odd, Bool.not(M.LETT(len, t, a, CM(len, t, e, a)))), Bool.and(ac, ce)}) == True{} : Bool},
  ih: KIH(q, len, t, e)) ->
  KH(len, t, e, a, odd):
  match ac ce:
    case False{} _:
      Empty.absurd(KH(len, t, e, a, odd), LS.ft(Equal.trans(Bool, False{}, M.KG(q, len, t, e, M.KD{(CM(len, t, e, a) + 1 : U32), False{}, Bool.or(odd, Bool.not(M.LETT(len, t, a, CM(len, t, e, a)))), False{}}), True{},
        Equal.sym(Bool, M.KG(q, len, t, e, M.KD{(CM(len, t, e, a) + 1 : U32), False{}, Bool.or(odd, Bool.not(M.LETT(len, t, a, CM(len, t, e, a)))), False{}}), False{}, kd_false(q, len, t, e, (CM(len, t, e, a) + 1 : U32), Bool.or(odd, Bool.not(M.LETT(len, t, a, CM(len, t, e, a)))))), hk)))
    case True{} False{}:
      +X = Q.xs(len, t)
      +c = CM(len, t, e, a)
      +rg = cm_rg(len, t, d, e, a, h, he, hae)
      +hce2 = N.not_lt_le(n(c), n(e), Equal.trans(Bool, Nat.is_lt(n(c), n(e)), U32.is_lt(c, e), False{}, Equal.sym(Bool, U32.is_lt(c, e), Nat.is_lt(n(c), n(e)), U.is_lt_to_nat(c, e)), hce))
      +ec = Z.le_antisym(n(c), n(e), N.and_true_r(Nat.is_le(n(a), n(c)), Nat.is_le(n(c), n(e)), rg), hce2)
      +hlt = Equal.trans(Bool, Nat.is_lt(n(a), n(c)), U32.is_lt(a, c), True{}, Equal.sym(Bool, U32.is_lt(a, c), Nat.is_lt(n(a), n(c)), U.is_lt_to_nat(a, c)), hac)
      +hcl = N.le_trans(n(c), n(e), n(len), N.and_true_r(Nat.is_le(n(a), n(c)), Nat.is_le(n(c), n(e)), rg), he)
      +hod = kg_end(q, len, t, e, (c + 1 : U32), Bool.or(odd, Bool.not(M.LETT(len, t, a, c))), hk)
      +F = Q.fld(X, n(a), n(c))
      +tl = AB.subst(Nat, z => {AL.mapc(LS.tsplit(D.slice(X, z, Nat.sub(n(e), z)), 44)) == Nil{} : List<&2, String>}, n(e), n(c), Equal.sym(Nat, n(c), n(e), ec),
        Equal.cong(LL(), List<&2, String>, z => AL.mapc(z), LS.tsplit(D.slice(X, n(e), Nat.sub(n(e), n(e))), 44), Nil{}, LS.ts_eq(X, n(e), 44)))
      +eps = Equal.trans(List<&2, String>, PS(len, t, e, a), F <> AL.mapc(LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44)), F <> Nil{},
        pse(len, t, d, e, a, h, he, hae), Equal.cong(List<&2, String>, List<&2, String>, z => F <> z, AL.mapc(LS.tsplit(D.slice(X, n(c), Nat.sub(n(e), n(c))), 44)), Nil{}, tl))
      +hne = ne_fld(len, t, d, a, c, h, hlt, hcl)
      +hle = lett_s(len, t, d, a, c, h, hlt, hcl)
      (AB.subst(List<&2, String>, z => {B.Text.any_empty(z) == False{} : Bool}, F <> Nil{}, PS(len, t, e, a), Equal.sym(List<&2, String>, PS(len, t, e, a), F <> Nil{}, eps),
         %Equal.sym(Bool, String.is_empty(F), False{}, hne) : {Bool.or(_, False{}) == False{} : Bool}; {==}),
       AB.subst(List<&2, String>, z => {Bool.or(odd, B.Text.any_not_letters(z)) == True{} : Bool}, F <> Nil{}, PS(len, t, e, a), Equal.sym(List<&2, String>, PS(len, t, e, a), F <> Nil{}, eps),
         %Equal.sym(Bool, B.Text.is_letters(F), M.LETT(len, t, a, c), hle) : {Bool.or(odd, Bool.or(Bool.not(_), False{})) == True{} : Bool}; or_f0(odd, Bool.not(M.LETT(len, t, a, c)), hod)))
    case True{} True{}:
      +c = CM(len, t, e, a)
      +hlt = Equal.trans(Bool, Nat.is_lt(n(a), n(c)), U32.is_lt(a, c), True{}, Equal.sym(Bool, U32.is_lt(a, c), Nat.is_lt(n(a), n(c)), U.is_lt_to_nat(a, c)), hac)
      +hce2 = Equal.trans(Bool, Nat.is_lt(n(c), n(e)), U32.is_lt(c, e), True{}, Equal.sym(Bool, U32.is_lt(c, e), Nat.is_lt(n(c), n(e)), U.is_lt_to_nat(c, e)), hce)
      +hcl2 = N.lt_le_trans(n(c), n(e), n(len), hce2, he)
      +i1 = LP.inc_len(len, t, d, c, h, hcl2)
      +hc1 = AB.subst(Nat, z => {Nat.is_le(z, n(e)) == True{} : Bool}, 1n+n(c), n((c + 1 : U32)),
        Equal.sym(Nat, n((c + 1 : U32)), 1n+n(c), Equal.trans(Nat, n((c + 1 : U32)), Nat.add(n(c), 1n), 1n+n(c), i1, N.add_one(n(c)))),
        Equal.trans(Bool, Nat.is_le(1n+n(c), n(e)), Nat.is_lt(n(c), n(e)), True{}, N.le_succ_lt(n(c), n(e)), hce2))
      kcons(len, t, d, e, a, odd, h, he, hae, hlt, hce2, ih((c + 1 : U32), Bool.or(odd, Bool.not(M.LETT(len, t, a, c))), hc1, hk))

def kloop(+k: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +a: U32, +odd: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool},
  +hk: {M.KG(k, len, t, e, M.KD{a, True{}, odd, True{}}) == True{} : Bool}) ->
  KH(len, t, e, a, odd):
  match k:
    case 0n:
      Empty.absurd(KH(len, t, e, a, odd), LS.ft(hk))
    case 1n+q:
      +c = CM(len, t, e, a)
      kstep(U32.is_lt(a, c), U32.is_lt(c, e), q, len, t, d, e, a, odd, h, he, hae, {==}, {==}, hk,
        +aa => +od => +x => +y => kloop(q, len, t, d, e, aa, od, h, he, x, y))

# ALT (bytes a .. e-1) passed NF.oos: no allele is empty, and some allele is
# not all letters.
def oos_v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +e: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +he: {Nat.is_le(n(e), n(len)) == True{} : Bool}, +hae: {Nat.is_le(n(a), n(e)) == True{} : Bool},
  +hn: {M.OOS(len, t, a, e) == True{} : Bool}) -> KH(len, t, e, a, False{}):
  kloop(U32.to_nat((e - a + 2 : U32)), len, t, d, e, a, False{}, h, he, hae, hn)
