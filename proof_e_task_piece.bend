import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_lines.bend as LN
import ./proof_b_lines_str.bend as LSS
import ./proof_b_lines_lst.bend as LL
import ./proof_b_cut_str.bend as CS
import ./proof_b_cut_pair.bend as CPR
import ./proof_b_enc.bend as EN
import ./proof_e_defs.bend as SD
import ./proof_e_task_buf.bend as BUF
import ./proof_e_task_first.bend as FL
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_find.bend as FD
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase E, area D (task): one piece's plan, on its buffer C.BT(len, t) whose
# view is the piece's codes. K: its first LF; s1 = K + 1; E1: the LF of the
# first line after K; T1: that line's first tab.

def K(+len: U32, +t: AT.Tree<U32>) -> U32:
  CPR.F1(len, t, 0, len, 10)

def E1(+len: U32, +t: AT.Tree<U32>) -> U32:
  CPR.F1(len, t, (K(len, t) + 1 : U32), len, 10)

def T1(+len: U32, +t: AT.Tree<U32>) -> U32:
  CPR.F1(len, t, (K(len, t) + 1 : U32), E1(len, t), 9)

# The text after byte k (proof_e_task.bend's after, unfolded).
def aft(+c: String, +k: U32) -> String:
  NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat((k + 1 : U32))))

# ---------------------------------------------------------------------------
# Words
# ---------------------------------------------------------------------------

def ult_nat(+x: U32, +y: U32, +h: {U32.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(x), U32.to_nat(y)), U32.is_lt(x, y), True{}, Equal.sym(Bool, U32.is_lt(x, y), Nat.is_lt(U32.to_nat(x), U32.to_nat(y)), U.is_lt_to_nat(x, y)), h)

def nat_ule(+x: U32, +y: U32, +h: {Nat.is_le(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}) -> {U32.is_le(x, y) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(x, y), Nat.is_le(U32.to_nat(x), U32.to_nat(y)), True{}, U.is_le_to_nat(x, y), h)

def ult_le(+x: U32, +y: U32, +h: {U32.is_lt(x, y) == True{} : Bool}) -> {U32.is_le(x, y) == True{} : Bool}:
  nat_ule(x, y, N.lt_to_le(U32.to_nat(x), U32.to_nat(y), ult_nat(x, y, h)))

def u_le0(+y: U32) -> {U32.is_le(0, y) == True{} : Bool}:
  nat_ule(0, y, N.le_zero_l(U32.to_nat(y)))

# ---------------------------------------------------------------------------
# The prefix before the first LF
# ---------------------------------------------------------------------------

def pre.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String, +k: U32,
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  hsl: {P.srctext(P.SBP{len, t, d, 0}) == String.append(P.btext(len, t, 0, (k - 0 : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (k + 1 : U32)}))) : String}
    & ({P.nolf(P.btext(len, t, 0, (k - 0 : U32))) == True{} : Bool}
    & ({U32.is_le((k + 1 : U32), len) == True{} : Bool}
    & {E.is_bytes(P.btext(len, t, 0, (k - 0 : U32))) == True{} : Bool}))) ->
  &a: String -> ({c == String.append(a, String.append("\n", aft(c, k))) : String} & {P.nolf(a) == True{} : Bool}):
  (e1, r1) = hsl
  (hn, r2) = r1
  +V = D.view(C.BT(len, t))
  +A = P.btext(len, t, 0, (k - 0 : U32))
  +ec = {
    %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) : {NR.chars(_) == c : String}
    %Equal.sym(List<&2, U32>, V, E.codes(c), hv) : {NR.chars(_) == c : String}
    %LSS.chars_norm(E.codes(c)) : {_ == c : String}
    Pair.snd({E.chars(E.codes(c)) == c : String}, {Q.chars(E.codes(c)) == c : String}, EN.chars_codes(c)) :
      {P.srctext(P.SBP{len, t, d, 0}) == c : String}}
  +ea = Equal.cong(List<&2, U32>, String, z => NR.chars(List.drop(&2, U32, z, U32.to_nat((k + 1 : U32)))), V, E.codes(c), hv)
  +eq = Equal.trans(String, c, P.srctext(P.SBP{len, t, d, 0}), String.append(A, String.append("\n", aft(c, k))),
    Equal.sym(String, P.srctext(P.SBP{len, t, d, 0}), c, ec),
    %ea : {P.srctext(P.SBP{len, t, d, 0}) == String.append(A, String.append("\n", _)) : String}
    e1)
  (A, (eq, hn))

# c is its bytes before its first LF k, the LF, and the text after k.
def pre_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hk: {U32.is_lt(K(len, t), len) == True{} : Bool}) ->
  &a: String -> ({c == String.append(a, String.append("\n", aft(c, K(len, t)))) : String} & {P.nolf(a) == True{} : Bool}):
  +L = U32.to_nat(len)
  +fK = CPR.f1_view(len, t, d, 0, len, 10, hok, u_le0(len), N.le_refl(L), {==})
  pre.k(len, t, d, c, K(len, t), hv,
    LN.src_line(len, t, d, 0, K(len, t), hok, u_le0(len), Equal.sym(Nat, U32.to_nat(K(len, t)), D.first(D.view(C.BT(len, t)), 0n, L, 10), fK), ult_nat(K(len, t), len, hk)))

# ---------------------------------------------------------------------------
# The first line after K: its CHROM
# ---------------------------------------------------------------------------

def C0(+len: U32, +t: AT.Tree<U32>) -> String:
  BUF.CC(True{}, len, t, (K(len, t) + 1 : U32), T1(len, t))

def fc.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String, +s1: U32, +e1: U32, +c0: String, +X: String,
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  hsl: {P.srctext(P.SBP{len, t, d, s1}) == String.append(P.btext(len, t, s1, (e1 - s1 : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (e1 + 1 : U32)}))) : String}
    & ({P.nolf(P.btext(len, t, s1, (e1 - s1 : U32))) == True{} : Bool}
    & ({U32.is_le((e1 + 1 : U32), len) == True{} : Bool}
    & {E.is_bytes(P.btext(len, t, s1, (e1 - s1 : U32))) == True{} : Bool})),
  +hf: {B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(P.btext(len, t, s1, (e1 - s1 : U32))))), 0n) == c0 : String}) ->
  {SD.first_chrom(B.Text.lines(String.append(NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat(s1))), X))) == Some{c0} : Maybe<&2, String>}:
  (e1q, r1) = hsl
  (hn, r2) = r1
  +A = P.btext(len, t, s1, (e1 - s1 : U32))
  +R = P.srctext(P.SBP{len, t, d, (e1 + 1 : U32)})
  +ea = Equal.cong(List<&2, U32>, String, z => NR.chars(List.drop(&2, U32, z, U32.to_nat(s1))), E.codes(c), D.view(C.BT(len, t)), Equal.sym(List<&2, U32>, D.view(C.BT(len, t)), E.codes(c), hv))
  +eA = Equal.trans(String, NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat(s1))), P.srctext(P.SBP{len, t, d, s1}), String.append(A, String.append("\n", R)), ea, e1q)
  %Equal.sym(String, NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat(s1))), String.append(A, String.append("\n", R)), eA) :
    {SD.first_chrom(B.Text.lines(String.append(_, X))) == Some{c0} : Maybe<&2, String>}
  %Equal.sym(String, String.append(String.append(A, String.append("\n", R)), X), String.append(A, String.append(String.append("\n", R), X)), LSS.sassoc(A, String.append("\n", R), X)) :
    {SD.first_chrom(B.Text.lines(_)) == Some{c0} : Maybe<&2, String>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(A, String.append("\n", String.append(R, X)))), B.Text.line(A) <> B.Text.lines(String.append(R, X)), LN.lines_cons(A, String.append(R, X), hn)) :
    {SD.first_chrom(_) == Some{c0} : Maybe<&2, String>}
  Equal.cong(String, Maybe<&2, String>, z => Some{z}, B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(A))), 0n), c0, hf)

# The first line from s1 (LF at e1, first tab at tb): field 0 of its body is
# the text the plan reads from s1 to tb.
def fieldf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s1: U32, +e1: U32, +tb: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs1: {U32.is_le(s1, len) == True{} : Bool},
  +hf10: {U32.to_nat(e1) == D.first(D.view(C.BT(len, t)), U32.to_nat(s1), U32.to_nat(len), 10) : Nat},
  +hEL: {U32.is_lt(e1, len) == True{} : Bool},
  +hf9: {U32.to_nat(tb) == D.first(D.view(C.BT(len, t)), U32.to_nat(s1), U32.to_nat(e1), 9) : Nat},
  +hT: {U32.is_lt(tb, e1) == True{} : Bool}) ->
  {B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(P.btext(len, t, s1, (e1 - s1 : U32))))), 0n) == BUF.CC(True{}, len, t, s1, tb) : String}:
  +xs = D.view(C.BT(len, t))
  +a = U32.to_nat(s1)
  +b = U32.to_nat(e1)
  +tn = U32.to_nat(tb)
  +L = U32.to_nat(len)
  +hlen = O.view_size_t(len, t, d, hok)
  +hbL0 = ult_nat(e1, len, hEL)
  +hbL = AB.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, L, List.length(&2, U32, xs), Equal.sym(Nat, List.length(&2, U32, xs), L, hlen), N.lt_to_le(b, L, hbL0))
  +haL = Equal.trans(Bool, Nat.is_le(a, L), U32.is_le(s1, len), True{}, Equal.sym(Bool, U32.is_le(s1, len), Nat.is_le(a, L), U.is_le_to_nat(s1, len)), hs1)
  +hLl = AB.subst(Nat, z => {Nat.is_le(L, z) == True{} : Bool}, L, List.length(&2, U32, xs), Equal.sym(Nat, List.length(&2, U32, xs), L, hlen), N.le_refl(L))
  +r10 = BL.first_range(xs, a, L, 10, haL, hLl)
  +hab = AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, D.first(xs, a, L, 10), b, Equal.sym(Nat, b, D.first(xs, a, L, 10), hf10),
    BUF.andl(Nat.is_le(a, D.first(xs, a, L, 10)), Nat.is_le(D.first(xs, a, L, 10), L), r10))
  +r9 = BL.first_range(xs, a, b, 9, hab, hbL)
  +hat = AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, D.first(xs, a, b, 9), tn, Equal.sym(Nat, tn, D.first(xs, a, b, 9), hf9),
    BUF.andl(Nat.is_le(a, D.first(xs, a, b, 9)), Nat.is_le(D.first(xs, a, b, 9), b), r9))
  +htb = ult_nat(tb, e1, hT)
  +hlt9 = AB.subst(Nat, z => {Nat.is_lt(z, b) == True{} : Bool}, tn, D.first(xs, a, b, 9), hf9, htb)
  +hhit = AB.subst(Nat, z => {D.has(xs, z, 9) == True{} : Bool}, D.first(xs, a, b, 9), tn, Equal.sym(Nat, tn, D.first(xs, a, b, 9), hf9),
    BL.first_hit(xs, a, b, 9, hab, hbL, hlt9))
  +htab = LL.has_get(List.get(&2, U32, xs, tn), 9, hhit)
  +hF = FL.fld0(xs, a, tn, b, hat, htb, hbL, Equal.sym(Nat, tn, D.first(xs, a, b, 9), hf9), htab)
  +nE = U.to_nat_sub_le(e1, s1, nat_ule(s1, e1, hab))
  +nT = U.to_nat_sub_le(tb, s1, nat_ule(s1, tb, hat))
  +eAf = Equal.trans(String, P.btext(len, t, s1, (e1 - s1 : U32)), NR.chars(D.slice(xs, a, Nat.sub(b, a))), CS.fld(xs, a, b),
    Equal.cong(Nat, String, z => NR.chars(D.slice(xs, a, z)), U32.to_nat((e1 - s1 : U32)), Nat.sub(b, a), nE),
    Equal.sym(String, Q.chars(D.slice(xs, a, Nat.sub(b, a))), NR.chars(D.slice(xs, a, Nat.sub(b, a))), LSS.chars_norm(D.slice(xs, a, Nat.sub(b, a)))))
  +hsum = AB.subst(Nat, z => {Nat.is_le(z, L) == True{} : Bool}, tn, Nat.add(a, U32.to_nat((tb - s1 : U32))),
    Equal.sym(Nat, Nat.add(a, U32.to_nat((tb - s1 : U32))), tn,
      %Equal.sym(Nat, U32.to_nat((tb - s1 : U32)), Nat.sub(tn, a), nT) : {Nat.add(a, _) == tn : Nat}
      N.le_sub_add(a, tn, hat)),
    N.lt_to_le(tn, L, N.lt_trans(tn, b, L, htb, hbL0)))
  +eTY = SM.to_list_view_t(len, t, d, s1, (tb - s1 : U32), hok, hsum)
  +eC0 = Equal.trans(String, BUF.CC(True{}, len, t, s1, tb), Q.chars(D.slice(xs, a, U32.to_nat((tb - s1 : U32)))), CS.fld(xs, a, tn),
    Equal.cong(List<&2, U32>, String, z => Q.chars(z), BUF.TY(len, t, s1, (tb - s1 : U32)), D.slice(xs, a, U32.to_nat((tb - s1 : U32))), eTY),
    Equal.cong(Nat, String, z => Q.chars(D.slice(xs, a, z)), U32.to_nat((tb - s1 : U32)), Nat.sub(tn, a), nT))
  Equal.trans(String, B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(P.btext(len, t, s1, (e1 - s1 : U32))))), 0n),
    B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(CS.fld(xs, a, b)))), 0n), BUF.CC(True{}, len, t, s1, tb),
    Equal.cong(String, String, z => B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(z))), 0n), P.btext(len, t, s1, (e1 - s1 : U32)), CS.fld(xs, a, b), eAf),
    Equal.trans(String, B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(CS.fld(xs, a, b)))), 0n), CS.fld(xs, a, tn), BUF.CC(True{}, len, t, s1, tb),
      hF, Equal.sym(String, BUF.CC(True{}, len, t, s1, tb), CS.fld(xs, a, tn), eC0)))

# The first LF from s1 is not before s1.
def s1_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s1: U32, +e1: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs1: {U32.is_le(s1, len) == True{} : Bool},
  +hf10: {U32.to_nat(e1) == D.first(D.view(C.BT(len, t)), U32.to_nat(s1), U32.to_nat(len), 10) : Nat}) ->
  {Nat.is_le(U32.to_nat(s1), U32.to_nat(e1)) == True{} : Bool}:
  +xs = D.view(C.BT(len, t))
  +a = U32.to_nat(s1)
  +b = U32.to_nat(e1)
  +L = U32.to_nat(len)
  +hlen = O.view_size_t(len, t, d, hok)
  +haL = Equal.trans(Bool, Nat.is_le(a, L), U32.is_le(s1, len), True{}, Equal.sym(Bool, U32.is_le(s1, len), Nat.is_le(a, L), U.is_le_to_nat(s1, len)), hs1)
  +hLl = AB.subst(Nat, z => {Nat.is_le(L, z) == True{} : Bool}, L, List.length(&2, U32, xs), Equal.sym(Nat, List.length(&2, U32, xs), L, hlen), N.le_refl(L))
  +r10 = BL.first_range(xs, a, L, 10, haL, hLl)
  AB.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, D.first(xs, a, L, 10), b, Equal.sym(Nat, b, D.first(xs, a, L, 10), hf10),
    BUF.andl(Nat.is_le(a, D.first(xs, a, L, 10)), Nat.is_le(D.first(xs, a, L, 10), L), r10))

# The first CHROM after K, whatever follows the piece.
def first_c0(+len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_lt((K(len, t) + 1 : U32), len) == True{} : Bool},
  +hE: {U32.is_lt(E1(len, t), len) == True{} : Bool},
  +hT: {U32.is_lt(T1(len, t), E1(len, t)) == True{} : Bool},
  +X: String) ->
  {SD.first_chrom(B.Text.lines(String.append(aft(c, K(len, t)), X))) == Some{C0(len, t)} : Maybe<&2, String>}:
  +s1 = (K(len, t) + 1 : U32)
  +e1 = E1(len, t)
  +hs1 = ult_le(s1, len, hk1)
  +L = U32.to_nat(len)
  +f10 = CPR.f1_view(len, t, d, s1, len, 10, hok, hs1, N.le_refl(L), {==})
  +hs1e = nat_ule(s1, e1, s1_le(len, t, d, s1, e1, hok, hs1, f10))
  +f9 = CPR.f1_view(len, t, d, s1, e1, 9, hok, hs1e, N.lt_to_le(U32.to_nat(e1), L, ult_nat(e1, len, hE)), {==})
  fc.k(len, t, d, c, s1, e1, C0(len, t), X, hv,
    LN.src_line(len, t, d, s1, e1, hok, hs1, Equal.sym(Nat, U32.to_nat(e1), D.first(D.view(C.BT(len, t)), U32.to_nat(s1), L, 10), f10), ult_nat(e1, len, hE)),
    fieldf(len, t, d, s1, e1, T1(len, t), hok, hs1, f10, hE, f9, hT))

# ---------------------------------------------------------------------------
# One piece
# ---------------------------------------------------------------------------

# proof_e_task.bend's PcOK, with this file's copies (rs_ok2, two2, aft).
def POK(+c: String, +len: U32, +rs: List<&2, Pr.Req>, +ok: Bool, +k: U32, +c0: String) -> Type:
  match ok:
    case True{}:
      {Bool.and(BUF.rs_ok2(rs), BUF.two2(rs)) == True{} : Bool}
        & ({E.is_bytes(c0) == True{} : Bool}
        & ((@X: String -> {SD.first_chrom(B.Text.lines(String.append(aft(c, k), X))) == Some{c0} : Maybe<&2, String>})
        & ({U32.is_lt((k + 1 : U32), len) == True{} : Bool}
        & (&a: String -> ({c == String.append(a, String.append("\n", aft(c, k))) : String} & {P.nolf(a) == True{} : Bool})))))
    case False{}:
      {rs == Nil{} : List<&2, Pr.Req>}

def PieceG(+len: U32, +t: AT.Tree<U32>, +c: String, -pl: W.Pl) -> Type:
  &rs: List<&2, Pr.Req> -> &ok: Bool -> &k: U32 -> &c0: String -> &l: Nat ->
    ({pl == W.Pl{C.BT(len, t), rs, ok, k, c0, l} : W.Pl} & ({BUF.rs_ok2(rs) == True{} : Bool} & POK(c, len, rs, ok, k, c0)))

def P1(+len: U32, +t: AT.Tree<U32>) -> Nat:
  BUF.CP(True{}, len, t, T1(len, t), E1(len, t))

def g3(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hK: {U32.is_lt(K(len, t), len) == True{} : Bool},
  +hk1: {U32.is_lt((K(len, t) + 1 : U32), len) == True{} : Bool},
  +hE: {U32.is_lt(E1(len, t), len) == True{} : Bool},
  +hg: {U32.is_lt(T1(len, t), E1(len, t)) == g : Bool}) ->
  PieceG(len, t, c, W.plan.first(len, K(len, t), (K(len, t) + 1 : U32), W.Cp{C.BT(len, t), g, BUF.CC(g, len, t, (K(len, t) + 1 : U32), T1(len, t)), BUF.CP(g, len, t, T1(len, t), E1(len, t))})):
  match g:
    case False{}:
      (Nil{}, (False{}, (K(len, t), ("", (0n, ({==}, ({==}, {==})))))))
    case True{}:
      +s1 = (K(len, t) + 1 : U32)
      +k = K(len, t)
      +rs = BUF.LRS(len, t, C0(len, t), P1(len, t), s1)
      +hrs = BUF.last_ok(C0(len, t), P1(len, t), s1, len, t, BUF.cc_bytes(True{}, len, t, s1, T1(len, t)))
      (rs, (True{}, (k, (C0(len, t), (P1(len, t),
        (BUF.last_b(k, C0(len, t), P1(len, t), s1, len, t),
        (BUF.andl(BUF.rs_ok2(rs), BUF.two2(rs), hrs),
        (hrs, (BUF.cc_bytes(True{}, len, t, s1, T1(len, t)), (X => first_c0(len, t, d, c, hok, hv, hk1, hE, hg, X), (hk1, pre_lf(len, t, d, c, hok, hv, hK))))))))))))

def g2(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hK: {U32.is_lt(K(len, t), len) == True{} : Bool},
  +hk1: {U32.is_lt((K(len, t) + 1 : U32), len) == True{} : Bool},
  +hg: {U32.is_lt(E1(len, t), len) == g : Bool}) ->
  PieceG(len, t, c, W.plan.e1.if(g, len, K(len, t), E1(len, t), C.BT(len, t))):
  match g:
    case False{}:
      (Nil{}, (False{}, (K(len, t), ("", (0n, ({==}, ({==}, {==})))))))
    case True{}:
      +s1 = (K(len, t) + 1 : U32)
      %Equal.sym(W.Cp, W.cp(C.BT(len, t), s1, E1(len, t)),
        W.Cp{C.BT(len, t), U32.is_lt(T1(len, t), E1(len, t)), BUF.CC(U32.is_lt(T1(len, t), E1(len, t)), len, t, s1, T1(len, t)), BUF.CP(U32.is_lt(T1(len, t), E1(len, t)), len, t, T1(len, t), E1(len, t))},
        BUF.cp_b(len, t, s1, E1(len, t))) :
        PieceG(len, t, c, W.plan.first(len, K(len, t), s1, _))
      g3(U32.is_lt(T1(len, t), E1(len, t)), len, t, d, c, hok, hv, hK, hk1, hg, {==})

def G1(+len: U32, +t: AT.Tree<U32>) -> Bool:
  U32.is_le(W.minp(), len) && U32.is_lt(K(len, t), len) && U32.is_lt((K(len, t) + 1 : U32), len)

def g1(+g: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>},
  +hg: {G1(len, t) == g : Bool}) ->
  PieceG(len, t, c, W.plan.k.if(g, len, K(len, t), C.BT(len, t))):
  match g:
    case False{}:
      (Nil{}, (False{}, (K(len, t), ("", (0n, ({==}, ({==}, {==})))))))
    case True{}:
      +s1 = (K(len, t) + 1 : U32)
      +hT = hg
      +hk1 = BUF.andr(Bool.and(U32.is_le(W.minp(), len), U32.is_lt(K(len, t), len)), U32.is_lt(s1, len), hT)
      +hK = BUF.andr(U32.is_le(W.minp(), len), U32.is_lt(K(len, t), len), BUF.andl(Bool.and(U32.is_le(W.minp(), len), U32.is_lt(K(len, t), len)), U32.is_lt(s1, len), hT))
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s1, len, 10), (C.BT(len, t), E1(len, t)), CPR.ff1(len, t, s1, len, 10)) :
        PieceG(len, t, c, W.plan.e1(len, K(len, t), _))
      g2(U32.is_lt(E1(len, t), len), len, t, d, c, hok, hv, hK, hk1, {==})

# One piece's plan, on a buffer holding the piece's bytes.
def piece_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +c: String,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  PieceG(len, t, c, W.plan.piece(C.BT(len, t))):
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), 0, len, 10), (C.BT(len, t), K(len, t)), CPR.ff1(len, t, 0, len, 10)) :
    PieceG(len, t, c, W.plan.k(len, _))
  g1(G1(len, t), len, t, d, c, hok, hv, {==})
