import Base
import ./types.bend as B
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_text.bend as TX
import ./proof_c_tan_lists.bend as TL
import ./proof_c_tan_num.bend as TN
import ./proof_c_tan_el.bend as TE
import ./proof_c_tan_alk.bend as TA
import ./proof_b_lit.bend as LT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_same.bend as BS
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C, area "txt": the letters NX writes for the closed form
# (proof_c_txt.bend's deliverables). One byte: NX.letter of NX.code is
# Base.letter of Base.of_fasta. One allele: TX.ALS walks R_k ++ a from byte
# d, el_get reads each byte. The ALTs: TX.ACC is String.join's text. POS:
# the word sum does not wrap (pos31, four_pow, sum32 as in proof_b_cache_hit.bend).

law lb:
  for b: B.Base
  {Chr{NX.letter(TL.bidx(b))} == B.Base.letter(b) : Char}

def lb(b):
  match b:
    case B.A{}:
      {==}
    case B.C{}:
      {==}
    case B.G{}:
      {==}
    case B.T{}:
      {==}
    case B.N{}:
      {==}

# The letter written for a byte.
law letter_bf:
  for +x: U32
  {Chr{NX.letter(NX.code(x))} == B.Base.letter(Q.bf(x)) : Char}

def letter_bf(x):
  %TL.code_idx(x) : {Chr{NX.letter(_)} == B.Base.letter(Q.bf(x)) : Char}
  lb(Q.bf(x))

law drop_all:
  for xs: List<&2, U32>
  for d: Nat
  for +h: {Nat.is_le(List.length(&2, U32, xs), d) == True{} : Bool}
  {List.drop(&2, U32, xs, d) == Nil{} : List<&2, U32>}

def drop_all(xs, d, h):
  match xs d:
    case Nil{} _:
      {==}
    case x <> t 0n:
      Empty.absurd({x <> t == Nil{} : List<&2, U32>}, N.false_ne_true(h))
    case x <> t 1n+p:
      drop_all(t, p, h)

law na_nat:
  for +ln: U32
  for +tr: U32
  for +d: Nat
  for +h: {Nat.is_lt(Nat.add(Q.n(tr), d), Q.n(ln)) == True{} : Bool}
  {Q.n(((ln - tr : U32) - U32.from_nat(d) : U32)) == Nat.sub(Nat.sub(Q.n(ln), Q.n(tr)), d) : Nat}

def na_nat(ln, tr, d, h):
  +l = Q.n(ln)
  +t = Q.n(tr)
  +lt = (ln - tr : U32)
  +E1 = TL.u_sub(ln, tr, N.le_trans(t, Nat.add(t, d), l, N.le_add_r(t, d), N.lt_to_le(Nat.add(t, d), l, h)))
  +Ed = TL.u_from(d, ln, N.le_lt_trans(d, Nat.add(t, d), l, N.le_add_l(d, t), h))
  +E2 = TL.u_sub(lt, U32.from_nat(d),
    %Equal.sym(Nat, Q.n(U32.from_nat(d)), d, Ed) : {Nat.is_le(_, Q.n(lt)) == True{} : Bool}
    %Equal.sym(Nat, Q.n(lt), Nat.sub(l, t), E1) : {Nat.is_le(d, _) == True{} : Bool}
    TL.le_sub(t, d, l, N.lt_to_le(Nat.add(t, d), l, h)))
  %Equal.sym(Nat, Q.n((lt - U32.from_nat(d) : U32)), Nat.sub(Q.n(lt), Q.n(U32.from_nat(d))), E2) : {_ == Nat.sub(Nat.sub(l, t), d) : Nat}
  %Equal.sym(Nat, Q.n(lt), Nat.sub(l, t), E1) : {Nat.sub(_, Q.n(U32.from_nat(d))) == Nat.sub(Nat.sub(l, t), d) : Nat}
  %Equal.sym(Nat, Q.n(U32.from_nat(d)), d, Ed) : {Nat.sub(Nat.sub(l, t), _) == Nat.sub(Nat.sub(l, t), d) : Nat}
  {==}

law hjn_step:
  for +j: U32
  for +ln: U32
  for +n1: Nat
  for +m: Nat
  for +hjl: {Nat.is_lt(Q.n(j), Q.n(ln)) == True{} : Bool}
  for +hjn: {Nat.add(Q.n(j), 1n+n1) == m : Nat}
  {Nat.add(Q.n((j + 1 : U32)), n1) == m : Nat}

def hjn_step(j, ln, n1, m, hjl, hjn):
  %Equal.sym(Nat, Q.n((j + 1 : U32)), Nat.add(Q.n(j), 1n), TL.u_inc(j, ln, hjl)) : {Nat.add(_, n1) == m : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Q.n(j), 1n), n1), Nat.add(Q.n(j), Nat.add(1n, n1)), N.add_assoc(Q.n(j), 1n, n1)) : {_ == m : Nat}
  hjn

# TX.ALS from byte j, n letters to the end of take(R_k ++ a, L - tr).
law als_show:
  for n: Nat
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
  for +j: U32
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool}
  for +hin: {Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), Q.n(NX.Ap.ln(a))), Q.n(bl)) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(Q.n(p0), 1n), Nat.add(Q.n(offu), Q.n(wl))) == True{} : Bool}
  for +hjn: {Nat.add(Q.n(j), n) == Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr)) : Nat}
  {TX.ALS(n, bl, bt, wl, wt, a, k, j, p0, offu) == B.Allele.show(Q.BF(List.drop(&2, U32, List.take(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr))), Q.n(j)))) : String}

def als_show(n, bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, j, hb, hw, hin, hk, ho, hjn):
  match n:
    case 0n:
      +m = Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr))
      +T = List.take(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr)))
      +nj = Q.n(j)
      +l = Q.n(NX.Ap.ln(a))
      +ejm = Equal.trans(Nat, nj, Nat.add(nj, 0n), m, Equal.sym(Nat, Nat.add(nj, 0n), nj, N.add_zero(nj)), hjn)
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, T, nj), Nil{}, drop_all(T, nj,
          %Equal.sym(Nat, List.length(&2, U32, T), m, TL.len_take(TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), m, TA.m_le(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, hb, hw, hin, hk, ho))) : {Nat.is_le(_, nj) == True{} : Bool}
          %Equal.sym(Nat, nj, m, ejm) : {Nat.is_le(m, _) == True{} : Bool}
          N.le_refl(m))) :
        {"" == B.Allele.show(Q.BF(_)) : String}
      {==}
    case 1n+(+n1):
      +m = Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr))
      +T = List.take(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr)))
      +nj = Q.n(j)
      +l = Q.n(NX.Ap.ln(a))
      +hjm = TL.le_succ_lt(nj, m,
        %hjn : {Nat.is_le(Nat.add(nj, 1n), _) == True{} : Bool}
        N.le_add_mono_l(nj, 1n, 1n+n1, N.le_zero_l(n1)))
      +hjl = N.lt_le_trans(nj, m, l, hjm, TN.sub_le_self(l, Q.n(tr)))
      +x = Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)
      +j1 = (j + 1 : U32)
      +Gt = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, T, nj), List.get(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), nj), Some{x}, TL.get_take(TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), m, nj, hjm), TA.el_get(bl, bt, bd, wl, wt, wd, a, p0, offu, k, j, hb, hw, hin, hk, ho, hjl))
      +LH = {SCon{Chr{NX.letter(NX.code(x))}, TX.ALS(n1, bl, bt, wl, wt, a, k, j1, p0, offu)} : String}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, T, nj), x <> List.drop(&2, U32, T, Nat.add(nj, 1n)), BS.drop_get(T, nj, x, Gt)) :
        {LH == B.Allele.show(Q.BF(_)) : String}
      %TL.u_inc(j, NX.Ap.ln(a), hjl) : {LH == B.Allele.show(Q.BF(x <> List.drop(&2, U32, T, _))) : String}
      %letter_bf(x) : {LH == SCon{_, B.Allele.show(Q.BF(List.drop(&2, U32, T, Q.n(j1))))} : String}
      %als_show(n1, bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, j1, hb, hw, hin, hk, ho, hjn_step(j, NX.Ap.ln(a), n1, m, hjl, hjn)) :
        {LH == SCon{Chr{NX.letter(NX.code(x))}, _} : String}
      {==}

law ala_show_t:
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
  for +hl: {Nat.is_lt(Nat.add(Q.n(tr), d), Q.n(NX.Ap.ln(a))) == True{} : Bool}
  {TX.ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu) == B.Allele.show(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) : String}

def ala_show_t(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hl):
  +m = Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr))
  +l = Q.n(NX.Ap.ln(a))
  +j = U32.from_nat(d)
  +Ed = TL.u_from(d, NX.Ap.ln(a), N.le_lt_trans(d, Nat.add(Q.n(tr), d), l, N.le_add_l(d, Q.n(tr)), hl))
  %Equal.sym(Nat, Q.n(TX.NA(a, tr, d)), Nat.sub(m, d), na_nat(NX.Ap.ln(a), tr, d, hl)) :
    {TX.ALS(_, bl, bt, wl, wt, a, k, j, p0, offu) == B.Allele.show(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d))) : String}
  %Ed : {TX.ALS(Nat.sub(m, d), bl, bt, wl, wt, a, k, j, p0, offu) == B.Allele.show(Q.BF(List.drop(&2, U32, List.take(&2, U32, TE.XA(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k), Nat.sub(Q.n(NX.Ap.ln(a)), Q.n(tr))), _))) : String}
  als_show(Nat.sub(m, d), bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, j, hb, hw, hin, hk, ho,
    %Equal.sym(Nat, Q.n(j), d, Ed) : {Nat.add(_, Nat.sub(m, d)) == m : Nat}
    N.le_sub_add(d, m, N.lt_to_le(d, m, TN.lt_sub(Q.n(tr), d, l, hl))))

# ---------------------------------------------------------------------------
# Commas between
# ---------------------------------------------------------------------------

# The text after the first string: a comma before each.
def JS(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case h <> t:
      String.append(",", String.append(h, JS(t)))

law str_assoc:
  for a: String
  for +b: String
  for +c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def str_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), str_assoc(t, b, c)) :
        {SCon{h, _} == SCon{h, String.append(t, String.append(b, c))} : String}
      {==}

law str_nil:
  for a: String
  {String.append(a, SNil{}) == a : String}

def str_nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, String.append(t, SNil{}), t, str_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

law join_go:
  for xs: List<&2, String>
  for +h: String
  {String.join.go(xs, h, ",") == String.append(h, JS(xs)) : String}

def join_go(xs, h):
  match xs:
    case Nil{}:
      Equal.sym(String, String.append(h, SNil{}), h, str_nil(h))
    case +h2 <> +t:
      %Equal.sym(String, String.join.go(t, h2, ","), String.append(h2, JS(t)), join_go(t, h2)) :
        {String.append(h, String.append(",", _)) == String.append(h, JS(h2 <> t)) : String}
      {==}

law acc_go:
  for als: List<&2, NX.Ap>
  for +acc: String
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
  {TX.ACC(als, acc, False{}, bl, bt, wl, wt, k, tr, d, p0, offu) == String.append(acc, JS(B.Alleles.show(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)))) : String}

def acc_go(als, acc, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      Equal.sym(String, String.append(acc, SNil{}), acc, str_nil(acc))
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +S = B.Allele.show(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d)))
      +JR = JS(B.Alleles.show(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d)))
      +RH = String.append(acc, String.append(",", String.append(S, JR)))
      %Equal.sym(String, TX.ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu), S, ala_show_t(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hkh)) :
        {TX.ACC(t, String.append(acc, String.append(",", _)), False{}, bl, bt, wl, wt, k, tr, d, p0, offu) == RH : String}
      %Equal.sym(String, TX.ACC(t, String.append(acc, String.append(",", S)), False{}, bl, bt, wl, wt, k, tr, d, p0, offu), String.append(String.append(acc, String.append(",", S)), JR),
          acc_go(t, String.append(acc, String.append(",", S)), bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, hat, hk, ho, hkt)) :
        {_ == RH : String}
      str_assoc(acc, String.append(",", S), JR)

law acc_join_t:
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
  {TX.ACC(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu) == String.join(B.Alleles.show(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, als, k, tr, d)), ",") : String}

def acc_join_t(als, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, ha, hk, ho, hkl):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +l = Q.n(NX.Ap.ln(a))
      +hin = TL.and_r(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl)), TL.and_l(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha))
      +hat = TL.and_r(Bool.and(Nat.is_le(1n, l), Nat.is_le(Nat.add(Q.n(NX.Ap.st(a)), l), Q.n(bl))), Q.ALS_IN(bl, t), ha)
      +hkh = TL.and_l(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +hkt = TL.and_r(Nat.is_lt(Nat.add(Q.n(tr), d), l), Q.KL(t, tr, d), hkl)
      +S = B.Allele.show(Q.BF(Q.ALK(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, a, k, tr, d)))
      +R = B.Alleles.show(Q.ALKS(Q.xs(bl, bt), Q.xs(wl, wt), p0, offu, t, k, tr, d))
      %Equal.sym(String, String.join.go(R, S, ","), String.append(S, JS(R)), join_go(R, S)) :
        {TX.ACC(a <> t, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu) == _ : String}
      %Equal.sym(String, TX.ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu), S, ala_show_t(bl, bt, bd, wl, wt, wd, a, p0, offu, k, tr, d, hb, hw, hin, hk, ho, hkh)) :
        {TX.ACC(t, _, False{}, bl, bt, wl, wt, k, tr, d, p0, offu) == String.append(S, JS(R)) : String}
      acc_go(t, S, bl, bt, bd, wl, wt, wd, p0, offu, k, tr, d, hb, hw, hat, hk, ho, hkt)

# ---------------------------------------------------------------------------
# POS
# ---------------------------------------------------------------------------

# Copied from proof_b_cache_hit.bend (its imports carry open TODOs).

# 4 * 2^d <= 2^e for 2 + d <= e (e kept a variable: the checker would
# expand a closed power it compares after unfolding).
def four_pow.g(+d: Nat, +e: Nat, +h: {Nat.is_le(Nat.add(2n, d), e) == True{} : Bool}) -> {Nat.is_le(Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, e)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, Nat.pow(2n, e)) == True{} : Bool}, Nat.pow(2n, Nat.add(2n, d)), Nat.mul(Nat.pow(2n, 2n), Nat.pow(2n, d)), N.pow_add(2n, 2n, d),
    N.pow_le(Nat.add(2n, d), e, h))

# 4 * 2^d <= 2^31 for d <= 29.
def four_pow(+d: Nat, +hd: {Nat.is_le(d, 29n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, 31n)) == True{} : Bool}:
  four_pow.g(d, 31n, hd)

# x < 2^31 and y <= 2^31: x + y < 2^32.
def sum32(+x: Nat, +y: Nat, +hx: {Nat.is_lt(x, Nat.pow(2n, 31n)) == True{} : Bool}, +hy: {Nat.is_le(y, Nat.pow(2n, 31n)) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(x, y), Nat.pow(2n, 32n)) == True{} : Bool}:
  +P = Nat.pow(2n, 31n)
  +h1 = N.lt_le_trans(Nat.add(x, y), Nat.add(P, y), Nat.add(P, P), N.lt_add_mono_r(y, x, P, hx), N.le_add_mono_l(P, y, P, hy))
  +e = Equal.trans(Nat, Nat.add(P, P), Nat.double(P), Nat.pow(2n, 1n+31n), Equal.sym(Nat, Nat.double(P), Nat.add(P, P), N.dbl_add(P)), Equal.sym(Nat, Nat.pow(2n, 1n+31n), Nat.double(P), N.pow2s(31n)))
  AB.subst(Nat, z => {Nat.is_lt(Nat.add(x, y), z) == True{} : Bool}, Nat.add(P, P), Nat.pow(2n, 32n), e, h1)

# A word below the word 10^9 reads below 2^31.
def pos31(+w: U32, +h: {U32.is_lt(w, 1000000000) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(w), Nat.pow(2n, 31n)) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(w), U32.to_nat(1000000000)), U32.is_lt(w, 1000000000), True{}, Equal.sym(Bool, U32.is_lt(w, 1000000000), Nat.is_lt(U32.to_nat(w), U32.to_nat(1000000000)), U.is_lt_to_nat(w, 1000000000)), h)
  +h2 = Equal.trans(Bool, Nat.is_lt(U32.to_nat(1000000000), U32.to_nat(2147483648)), U32.is_lt(1000000000, 2147483648), True{}, Equal.sym(Bool, U32.is_lt(1000000000, 2147483648), Nat.is_lt(U32.to_nat(1000000000), U32.to_nat(2147483648)), U.is_lt_to_nat(1000000000, 2147483648)), {==})
  AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(w), z) == True{} : Bool}, U32.to_nat(2147483648), Nat.pow(2n, 31n), LT.lit31w(),
    N.lt_trans(U32.to_nat(w), U32.to_nat(1000000000), U32.to_nat(2147483648), h1, h2))

law le_x:
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +hk: {Nat.is_le(Nat.add(Nat.add(U32.to_nat(k), U32.to_nat(offu)), 1n), U32.to_nat(p0)) == True{} : Bool}
  {Nat.is_le(U32.to_nat((p0 - k : U32)), U32.to_nat(p0)) == True{} : Bool}

def le_x(p0, offu, k, hk):
  %Equal.sym(Nat, U32.to_nat((p0 - k : U32)), Nat.sub(U32.to_nat(p0), U32.to_nat(k)), TL.u_sub(p0, k, TN.kok_le(U32.to_nat(k), U32.to_nat(offu), U32.to_nat(p0), hk))) : {Nat.is_le(_, U32.to_nat(p0)) == True{} : Bool}
  TN.sub_le_self(U32.to_nat(p0), U32.to_nat(k))

law le_y:
  for +d: Nat
  for +bl: U32
  for +hd: {Nat.is_lt(d, U32.to_nat(bl)) == True{} : Bool}
  {Nat.is_le(U32.to_nat(U32.from_nat(d)), U32.to_nat(bl)) == True{} : Bool}

def le_y(d, bl, hd):
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(d)), d, TL.u_from(d, bl, hd)) : {Nat.is_le(_, U32.to_nat(bl)) == True{} : Bool}
  N.lt_to_le(d, U32.to_nat(bl), hd)

law qq_pos_t:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +bd: Nat
  for +p0: U32
  for +offu: U32
  for +k: U32
  for +d: Nat
  for +hb: {D.ok(C.BT(bl, bt), bd) == True{} : Bool}
  for +hk: {Nat.is_le(Nat.add(Nat.add(Q.n(k), Q.n(offu)), 1n), Q.n(p0)) == True{} : Bool}
  for +hps: {U32.is_lt(p0, 1000000000) == True{} : Bool}
  for +hd: {Nat.is_lt(d, Q.n(bl)) == True{} : Bool}
  {TX.QQ(p0, k, d) == Nat.add(Nat.sub(Q.n(p0), Q.n(k)), d) : Nat}

def qq_pos_t(bl, bt, bd, p0, offu, k, d, hb, hk, hps, hd):
  +x = (p0 - k : U32)
  +y = U32.from_nat(d)
  %Equal.sym(Nat, U32.to_nat((x + y : U32)), Nat.add(U32.to_nat(x), U32.to_nat(y)), U.to_nat_add_fits_p(x, y, sum32(U32.to_nat(x), U32.to_nat(y),
      N.le_lt_trans(U32.to_nat(x), U32.to_nat(p0), Nat.pow(2n, 31n), le_x(p0, offu, k, hk), pos31(p0, hps)),
      N.le_trans(U32.to_nat(y), U32.to_nat(bl), Nat.pow(2n, 31n), le_y(d, bl, hd), N.le_trans(U32.to_nat(bl), Nat.mul(4n, Nat.pow(2n, bd)), Nat.pow(2n, 31n), C.ok_len(bl, bt, bd, hb), four_pow(bd, C.ok_d(bl, bt, bd, hb))))))) :
    {_ == Nat.add(Nat.sub(U32.to_nat(p0), U32.to_nat(k)), d) : Nat}
  %Equal.sym(Nat, U32.to_nat(x), Nat.sub(U32.to_nat(p0), U32.to_nat(k)), TL.u_sub(p0, k, TN.kok_le(U32.to_nat(k), U32.to_nat(offu), U32.to_nat(p0), hk))) :
    {Nat.add(_, U32.to_nat(y)) == Nat.add(Nat.sub(U32.to_nat(p0), U32.to_nat(k)), d) : Nat}
  %Equal.sym(Nat, U32.to_nat(y), d, TL.u_from(d, bl, hd)) : {Nat.add(Nat.sub(U32.to_nat(p0), U32.to_nat(k)), _) == Nat.add(Nat.sub(U32.to_nat(p0), U32.to_nat(k)), d) : Nat}
  {==}
