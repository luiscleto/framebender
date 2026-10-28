import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fix.bend as NX
import ./proof_c_defs.bend as Q
import ./proof_c_pre_pair.bend as P
import ./proof_c_pre_inv.bend as I
import ./proof_c_pre_let.bend as L
import ./proof_c_pre_lp.bend as G
import ./proof_c_pre_alt.bend as A
import ./proof_b_alleles.bend as AL
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import ./proof_b_alleles_spec.bend as SP
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# fix_als from the line's tests: the allele list is REF then the ALT loop's
# alleles (A.XN), whose facts A.aloop gives.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def RF(+e2: U32, +e3: U32) -> NX.Ap:
  NX.Ap{(e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)}

def G6(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool) -> Type:
  {als == RF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), RF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))

# ---------------------------------------------------------------------------
# Lists
# ---------------------------------------------------------------------------

def strs_m(+xs: List<&2, U32>, +ns: List<&2, NX.Ap>) -> {Q.STRS(xs, ns) == AL.mapc(A.MSL(xs, ns)) : List<&2, String>}:
  match ns:
    case Nil{}:
      {==}
    case +p <> +q:
      %Equal.sym(List<&2, String>, Q.STRS(xs, q), AL.mapc(A.MSL(xs, q)), strs_m(xs, q)) : {Norm.chars(Q.SL(xs, p)) <> _ == Norm.chars(Q.SL(xs, p)) <> AL.mapc(A.MSL(xs, q)) : List<&2, String>}
      {==}

def gd_l(+len: U32, +t: AT.Tree<U32>, +ns: List<&2, NX.Ap>, +hg: {G.GD(len, t, ns) == True{} : Bool}) -> {Q.ALS_L(Q.xs(len, t), ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +p <> +q:
      +a = Bool.and(G.INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p)))
      SP.and_tt(Q.lets(Q.SL(Q.xs(len, t), p)), Q.ALS_L(Q.xs(len, t), q),
        LS.and_r(G.INB(len, p), Q.lets(Q.SL(Q.xs(len, t), p)), LS.and_l(a, G.GD(len, t, q), hg)), gd_l(len, t, q, LS.and_r(a, G.GD(len, t, q), hg)))

def als_w(+a: U32, +b: U32, +ns: List<&2, NX.Ap>, +h: {Q.ALS_IN(a, ns) == True{} : Bool}, +hab: {Nat.is_le(n(a), n(b)) == True{} : Bool}) ->
  {Q.ALS_IN(b, ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +p <> +q:
      +o = Nat.is_le(1n, n(NX.Ap.ln(p)))
      +i = Nat.is_le(Nat.add(n(NX.Ap.st(p)), n(NX.Ap.ln(p))), n(a))
      +hp = LS.and_l(Bool.and(o, i), Q.ALS_IN(a, q), h)
      SP.and_tt(Bool.and(o, Nat.is_le(Nat.add(n(NX.Ap.st(p)), n(NX.Ap.ln(p))), n(b))), Q.ALS_IN(b, q),
        SP.and_tt(o, Nat.is_le(Nat.add(n(NX.Ap.st(p)), n(NX.Ap.ln(p))), n(b)), LS.and_l(o, i, hp),
          N.le_trans(Nat.add(n(NX.Ap.st(p)), n(NX.Ap.ln(p))), n(a), n(b), LS.and_r(o, i, hp), hab)),
        als_w(a, b, q, LS.and_r(Bool.and(o, i), Q.ALS_IN(a, q), h), hab))

# ---------------------------------------------------------------------------
# The ALT alleles written back, joined by commas
# ---------------------------------------------------------------------------

def SH(+xs: List<&2, U32>, ns: List<&2, NX.Ap>) -> List<&2, String>:
  B.Alleles.show(Q.BFS(xs, ns))

def jgo(+xs: List<&2, U32>, +ns: List<&2, NX.Ap>, +p: NX.Ap, +hp: {Q.lets(Q.SL(xs, p)) == True{} : Bool}, +hl: {Q.ALS_L(xs, ns) == True{} : Bool}) ->
  {String.eq(String.join.go(SH(xs, ns), B.Allele.show(Q.BF(Q.SL(xs, p))), ","), String.join.go(AL.mapc(A.MSL(xs, ns)), Norm.chars(Q.SL(xs, p)), ",")) == Bool.and(L.UPA(Q.SL(xs, p)), A.UPS(xs, ns)) : Bool}:
  match ns:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(L.UPA(Q.SL(xs, p)), True{}), L.UPA(Q.SL(xs, p)), LS.and_true(L.UPA(Q.SL(xs, p)))) :
        {String.eq(B.Allele.show(Q.BF(Q.SL(xs, p))), Norm.chars(Q.SL(xs, p))) == _ : Bool}
      L.up_ref(Q.SL(xs, p), hp)
    case +q <> +r:
      +S = Q.SL(xs, p)
      +J1 = String.join.go(SH(xs, r), B.Allele.show(Q.BF(Q.SL(xs, q))), ",")
      +J2 = String.join.go(AL.mapc(A.MSL(xs, r)), Norm.chars(Q.SL(xs, q)), ",")
      +hq = LS.and_l(Q.lets(Q.SL(xs, q)), Q.ALS_L(xs, r), hl)
      +hr = LS.and_r(Q.lets(Q.SL(xs, q)), Q.ALS_L(xs, r), hl)
      %Equal.sym(String, B.Allele.show(Q.BF(S)), Norm.chars(L.UPB(S)), L.show_upb(S)) :
        {String.eq(_ ++ ("," ++ J1), Norm.chars(S) ++ ("," ++ J2)) == Bool.and(L.UPA(S), Bool.and(L.UPA(Q.SL(xs, q)), A.UPS(xs, r))) : Bool}
      %Equal.sym(Bool, String.eq(Norm.chars(L.UPB(S)) ++ ("," ++ J1), Norm.chars(S) ++ ("," ++ J2)), Bool.and(D.list_eq(L.UPB(S), S), String.eq("," ++ J1, "," ++ J2)), L.sapp(L.UPB(S), S, "," ++ J1, "," ++ J2, L.len_upb(S))) :
        {_ == Bool.and(L.UPA(S), Bool.and(L.UPA(Q.SL(xs, q)), A.UPS(xs, r))) : Bool}
      %Equal.sym(Bool, D.list_eq(L.UPB(S), S), L.UPA(S), L.upb_eq(S, hp)) :
        {Bool.and(_, String.eq("," ++ J1, "," ++ J2)) == Bool.and(L.UPA(S), Bool.and(L.UPA(Q.SL(xs, q)), A.UPS(xs, r))) : Bool}
      %Equal.sym(Bool, String.eq(J1, J2), Bool.and(L.UPA(Q.SL(xs, q)), A.UPS(xs, r)), jgo(xs, r, q, hq, hr)) :
        {Bool.and(L.UPA(S), _) == Bool.and(L.UPA(S), Bool.and(L.UPA(Q.SL(xs, q)), A.UPS(xs, r))) : Bool}
      {==}

def jq(+xs: List<&2, U32>, +ns: List<&2, NX.Ap>, +hl: {Q.ALS_L(xs, ns) == True{} : Bool}) ->
  {String.eq(String.join(SH(xs, ns), ","), String.join(AL.mapc(A.MSL(xs, ns)), ",")) == A.UPS(xs, ns) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +p <> +q:
      jgo(xs, q, p, LS.and_l(Q.lets(Q.SL(xs, p)), Q.ALS_L(xs, q), hl), LS.and_r(Q.lets(Q.SL(xs, p)), Q.ALS_L(xs, q), hl))

# ---------------------------------------------------------------------------
# REF and ALT as text
# ---------------------------------------------------------------------------

def tref(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e2: U32, +e3: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl2: {Nat.is_lt(n(e2), n(len)) == True{} : Bool}, +hac: {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}) ->
  {Q.fld(Q.xs(len, t), Q.nx(e2), n(e3)) == Norm.chars(Q.SL(Q.xs(len, t), RF(e2, e3))) : String}:
  +xs = Q.xs(len, t)
  %Equal.sym(Nat, n((e3 - (e2 + 1 : U32) : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))), LP.sub_u(e3, (e2 + 1 : U32), hac)) :
    {Q.fld(xs, Q.nx(e2), n(e3)) == Norm.chars(D.slice(xs, n((e2 + 1 : U32)), _)) : String}
  %Equal.sym(Nat, n((e2 + 1 : U32)), Nat.add(n(e2), 1n), LP.inc_len(len, t, d, e2, h, hl2)) :
    {Q.fld(xs, Q.nx(e2), n(e3)) == Norm.chars(D.slice(xs, _, Nat.sub(n(e3), _))) : String}
  {==}

def talt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e3: U32, +e4: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl3: {Nat.is_lt(n(e3), n(len)) == True{} : Bool}) ->
  {Q.fld(Q.xs(len, t), Q.nx(e3), n(e4)) == Norm.chars(LP.BS(len, t, (e3 + 1 : U32), e4)) : String}:
  %Equal.sym(Nat, n((e3 + 1 : U32)), Nat.add(n(e3), 1n), LP.inc_len(len, t, d, e3, h, hl3)) :
    {Q.fld(Q.xs(len, t), Q.nx(e3), n(e4)) == Norm.chars(D.slice(Q.xs(len, t), _, Nat.sub(n(e4), _))) : String}
  {==}

# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------

def UPR(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32) -> Bool:
  P.L2.up(P.LETS(len, t, (e2 + 1 : U32), e3))

def NS(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32) -> List<&2, NX.Ap>:
  A.XN(17n, len, t, e4, A.X1((e3 + 1 : U32), [RF(e2, e3)], UPR(len, t, e2, e3)))

def als_k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl2: {Nat.is_lt(n(e2), n(len)) == True{} : Bool}, +hl3: {Nat.is_lt(n(e3), n(len)) == True{} : Bool},
  +h4l: {Nat.is_le(n(e4), n(lf)) == True{} : Bool},
  +hac: {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}, +n23: {Nat.is_lt(n((e2 + 1 : U32)), n(e3)) == True{} : Bool},
  +n34: {Nat.is_lt(n((e3 + 1 : U32)), n(e4)) == True{} : Bool},
  +lr: {Q.lets(Q.SL(Q.xs(len, t), RF(e2, e3))) == True{} : Bool},
  +g7: {P.XD.up(I.XGR(len, t, e2, e3, e4)) == up : Bool},
  +f1: {A.MSL(Q.xs(len, t), NS(len, t, e2, e3, e4)) == LP.PS(len, t, (e3 + 1 : U32), e4) : List<&2, List<&2, U32>>},
  +f2: {G.GD(len, t, NS(len, t, e2, e3, e4)) == True{} : Bool},
  +f3: {Q.ALS_IN(e4, NS(len, t, e2, e3, e4)) == True{} : Bool},
  +f4: {Bool.and(B.Alleles.distinct(Q.BFS(Q.xs(len, t), NS(len, t, e2, e3, e4))), A.NOTIN(Q.BFS(Q.xs(len, t), [RF(e2, e3)]), Q.BFS(Q.xs(len, t), NS(len, t, e2, e3, e4)))) == True{} : Bool},
  +f5: {P.XD.up(I.XGR(len, t, e2, e3, e4)) == Bool.and(UPR(len, t, e2, e3), A.UPS(Q.xs(len, t), NS(len, t, e2, e3, e4))) : Bool}) ->
  G6(len, t, e2, e3, e4, lf, RF(e2, e3) <> NS(len, t, e2, e3, e4), up):
  +xs = Q.xs(len, t)
  +Nn = NS(len, t, e2, e3, e4)
  +R = RF(e2, e3)
  +BSa = LP.BS(len, t, (e3 + 1 : U32), e4)
  +tA = talt(len, t, d, e3, e4, h, hl3)
  +hsp = Equal.trans(List<&2, String>, String.split(Q.fld(xs, Q.nx(e3), n(e4)), ','), String.split(Norm.chars(BSa), ','), Q.STRS(xs, Nn),
    Equal.cong(String, List<&2, String>, z => String.split(z, ','), Q.fld(xs, Q.nx(e3), n(e4)), Norm.chars(BSa), tA),
    Equal.trans(List<&2, String>, String.split(Norm.chars(BSa), ','), AL.mapc(LP.PS(len, t, (e3 + 1 : U32), e4)), Q.STRS(xs, Nn), AL.csplit(BSa),
      Equal.trans(List<&2, String>, AL.mapc(LP.PS(len, t, (e3 + 1 : U32), e4)), AL.mapc(A.MSL(xs, Nn)), Q.STRS(xs, Nn),
        Equal.cong(List<&2, List<&2, U32>>, List<&2, String>, z => AL.mapc(z), LP.PS(len, t, (e3 + 1 : U32), e4), A.MSL(xs, Nn), Equal.sym(List<&2, List<&2, U32>>, A.MSL(xs, Nn), LP.PS(len, t, (e3 + 1 : U32), e4), f1)),
        Equal.sym(List<&2, String>, Q.STRS(xs, Nn), AL.mapc(A.MSL(xs, Nn)), strs_m(xs, Nn)))))
  +s2 = LP.sub_u(e3, (e2 + 1 : U32), hac)
  +one = AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.sub(n(e3), n((e2 + 1 : U32))), n((e3 - (e2 + 1 : U32) : U32)),
    Equal.sym(Nat, n((e3 - (e2 + 1 : U32) : U32)), Nat.sub(n(e3), n((e2 + 1 : U32))), s2), A.sub_pos(n((e2 + 1 : U32)), n(e3), n23))
  +i3 = LP.inc_len(len, t, d, e3, h, hl3)
  +n3e4 = N.le_lt_trans(n(e3), n((e3 + 1 : U32)), n(e4),
    AB.subst(Nat, z => {Nat.is_le(n(e3), z) == True{} : Bool}, Nat.add(n(e3), 1n), n((e3 + 1 : U32)), Equal.sym(Nat, n((e3 + 1 : U32)), Nat.add(n(e3), 1n), i3), N.le_add_r(n(e3), 1n)), n34)
  +e3lf = N.lt_to_le(n(e3), n(lf), N.lt_le_trans(n(e3), n(e4), n(lf), n3e4, h4l))
  +sum = AB.subst(Nat, z => {Nat.is_le(z, n(lf)) == True{} : Bool}, n(e3), Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))),
    Equal.sym(Nat, Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))), n(e3), A.hsum((e2 + 1 : U32), e3, hac)), e3lf)
  +X = Q.BF(Q.SL(xs, R))
  +BN = Q.BFS(xs, Nn)
  +nt = LS.and_r(B.Alleles.distinct(BN), A.NOTIN([X], BN), f4)
  +c1 = Equal.trans(Bool, String.eq(B.Allele.show(X), Q.fld(xs, Q.nx(e2), n(e3))), L.UPA(Q.SL(xs, R)), UPR(len, t, e2, e3),
    Equal.trans(Bool, String.eq(B.Allele.show(X), Q.fld(xs, Q.nx(e2), n(e3))), String.eq(B.Allele.show(X), Norm.chars(Q.SL(xs, R))), L.UPA(Q.SL(xs, R)),
      Equal.cong(String, Bool, z => String.eq(B.Allele.show(X), z), Q.fld(xs, Q.nx(e2), n(e3)), Norm.chars(Q.SL(xs, R)), tref(len, t, d, e2, e3, h, hl2, hac)),
      L.up_ref(Q.SL(xs, R), lr)),
    Equal.sym(Bool, UPR(len, t, e2, e3), L.UPA(Q.SL(xs, R)), A.lets_up(len, t, d, (e2 + 1 : U32), e3, h, hac, N.lt_to_le(n(e3), n(len), hl3))))
  +JS = String.join(SH(xs, Nn), ",")
  +c2 = Equal.trans(Bool, String.eq(JS, Q.fld(xs, Q.nx(e3), n(e4))), String.eq(JS, Norm.chars(BSa)), A.UPS(xs, Nn),
    Equal.cong(String, Bool, z => String.eq(JS, z), Q.fld(xs, Q.nx(e3), n(e4)), Norm.chars(BSa), tA),
    Equal.trans(Bool, String.eq(JS, Norm.chars(BSa)), String.eq(JS, AL.JG(A.MSL(xs, Nn))), A.UPS(xs, Nn),
      Equal.cong(String, Bool, z => String.eq(JS, z), Norm.chars(BSa), AL.JG(A.MSL(xs, Nn)),
        Equal.trans(String, Norm.chars(BSa), AL.JG(LP.PS(len, t, (e3 + 1 : U32), e4)), AL.JG(A.MSL(xs, Nn)),
          Equal.sym(String, AL.JG(LP.PS(len, t, (e3 + 1 : U32), e4)), Norm.chars(BSa), AL.jsplit(BSa)),
          Equal.cong(List<&2, List<&2, U32>>, String, z => AL.JG(z), LP.PS(len, t, (e3 + 1 : U32), e4), A.MSL(xs, Nn), Equal.sym(List<&2, List<&2, U32>>, A.MSL(xs, Nn), LP.PS(len, t, (e3 + 1 : U32), e4), f1)))),
      jq(xs, Nn, gd_l(len, t, Nn, f2))))
  ({==},
   (hsp,
   (SP.and_tt(Bool.and(Nat.is_le(1n, n((e3 - (e2 + 1 : U32) : U32))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))), n(lf))), Q.ALS_IN(lf, Nn),
      SP.and_tt(Nat.is_le(1n, n((e3 - (e2 + 1 : U32) : U32))), Nat.is_le(Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))), n(lf)), one, sum),
      als_w(e4, lf, Nn, f3, h4l)),
   (SP.and_tt(Q.lets(Q.SL(xs, R)), Q.ALS_L(xs, Nn), lr, gd_l(len, t, Nn, f2)),
   (SP.and_tt(Bool.not(B.Alleles.member(X, BN)), B.Alleles.distinct(BN), LS.and_l(Bool.not(B.Alleles.member(X, BN)), True{}, nt), LS.and_l(B.Alleles.distinct(BN), A.NOTIN([X], BN), f4)),
   %Equal.sym(Bool, String.eq(B.Allele.show(X), Q.fld(xs, Q.nx(e2), n(e3))), UPR(len, t, e2, e3), c1) :
     {Bool.and(_, String.eq(JS, Q.fld(xs, Q.nx(e3), n(e4)))) == up : Bool}
   %Equal.sym(Bool, String.eq(JS, Q.fld(xs, Q.nx(e3), n(e4))), A.UPS(xs, Nn), c2) :
     {Bool.and(UPR(len, t, e2, e3), _) == up : Bool}
   Equal.trans(Bool, Bool.and(UPR(len, t, e2, e3), A.UPS(xs, Nn)), P.XD.up(I.XGR(len, t, e2, e3, e4)), up, Equal.sym(Bool, P.XD.up(I.XGR(len, t, e2, e3, e4)), Bool.and(UPR(len, t, e2, e3), A.UPS(xs, Nn)), f5), g7))))))

def als_d(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl2: {Nat.is_lt(n(e2), n(len)) == True{} : Bool}, +hl3: {Nat.is_lt(n(e3), n(len)) == True{} : Bool},
  +h4l: {Nat.is_le(n(e4), n(lf)) == True{} : Bool},
  +hac: {Nat.is_le(n((e2 + 1 : U32)), n(e3)) == True{} : Bool}, +n23: {Nat.is_lt(n((e2 + 1 : U32)), n(e3)) == True{} : Bool},
  +n34: {Nat.is_lt(n((e3 + 1 : U32)), n(e4)) == True{} : Bool},
  +lr: {Q.lets(Q.SL(Q.xs(len, t), RF(e2, e3))) == True{} : Bool},
  +g7: {P.XD.up(I.XGR(len, t, e2, e3, e4)) == up : Bool},
  r: A.ALC(len, t, e4, (e3 + 1 : U32), [RF(e2, e3)], UPR(len, t, e2, e3), NS(len, t, e2, e3, e4), P.XD.up(I.XGR(len, t, e2, e3, e4)))) ->
  G6(len, t, e2, e3, e4, lf, RF(e2, e3) <> NS(len, t, e2, e3, e4), up):
  match r:
    case (f1, r2):
      match r2:
        case (f2, r3):
          match r3:
            case (f3, r4):
              match r4:
                case (f4, f5):
                  als_k(len, t, d, e2, e3, e4, lf, up, h, hl2, hl3, h4l, hac, n23, n34, lr, g7, f1, f2, f3, f4, f5)

def als_core(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hl2: {Nat.is_lt(n(e2), n(len)) == True{} : Bool}, +hl3: {Nat.is_lt(n(e3), n(len)) == True{} : Bool},
  +h4l: {Nat.is_le(n(e4), n(lf)) == True{} : Bool}, +hll: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +g3: {P.L2.ok(P.LETS(len, t, (e2 + 1 : U32), e3)) == True{} : Bool},
  +g4: {(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4)) == True{} : Bool},
  +g5: {P.XD.ok(I.XGR(len, t, e2, e3, e4)) == True{} : Bool},
  +g6: {NX.rev_ap(P.XD.ps(I.XGR(len, t, e2, e3, e4)), Nil{}) == als : List<&2, NX.Ap>},
  +g7: {P.XD.up(I.XGR(len, t, e2, e3, e4)) == up : Bool}) ->
  G6(len, t, e2, e3, e4, lf, als, up):
  +R = RF(e2, e3)
  +Nn = NS(len, t, e2, e3, e4)
  +X1 = A.X1((e3 + 1 : U32), [R], UPR(len, t, e2, e3))
  +hRl = LS.and_l(U32.is_lt((e2 + 1 : U32), e3), U32.is_lt((e3 + 1 : U32), e4), g4)
  +h34u = LS.and_r(U32.is_lt((e2 + 1 : U32), e3), U32.is_lt((e3 + 1 : U32), e4), g4)
  +n23 = A.LTN((e2 + 1 : U32), e3, hRl)
  +hac = N.lt_to_le(n((e2 + 1 : U32)), n(e3), n23)
  +n34 = A.LTN((e3 + 1 : U32), e4, h34u)
  +e3len = N.lt_to_le(n(e3), n(len), hl3)
  +e4len = N.le_trans(n(e4), n(lf), n(len), h4l, N.lt_to_le(n(lf), n(len), hll))
  +lr = Equal.trans(Bool, Q.lets(Q.SL(Q.xs(len, t), R)), P.L2.ok(P.LETS(len, t, (e2 + 1 : U32), e3)), True{},
    Equal.sym(Bool, P.L2.ok(P.LETS(len, t, (e2 + 1 : U32), e3)), Q.lets(Q.SL(Q.xs(len, t), R)), A.lets_ok(len, t, d, (e2 + 1 : U32), e3, h, hac, e3len)), g3)
  +inb = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(e3), Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))),
    Equal.sym(Nat, Nat.add(n((e2 + 1 : U32)), n((e3 - (e2 + 1 : U32) : U32))), n(e3), A.hsum((e2 + 1 : U32), e3, hac)), e3len)
  +hg0 = SP.and_tt(Bool.and(G.INB(len, R), Q.lets(Q.SL(Q.xs(len, t), R))), True{}, SP.and_tt(G.INB(len, R), Q.lets(Q.SL(Q.xs(len, t), R)), inb, lr), {==})
  +hals = Equal.trans(List<&2, NX.Ap>, als, NX.rev_ap(P.XD.ps(I.XGR(len, t, e2, e3, e4)), Nil{}), R <> Nn,
    Equal.sym(List<&2, NX.Ap>, NX.rev_ap(P.XD.ps(I.XGR(len, t, e2, e3, e4)), Nil{}), als, g6),
    Equal.trans(List<&2, NX.Ap>, NX.rev_ap(P.XD.ps(I.XGR(len, t, e2, e3, e4)), Nil{}), NX.rev_ap(NX.rev_ap(Nn, [R]), Nil{}), R <> Nn,
      Equal.cong(List<&2, NX.Ap>, List<&2, NX.Ap>, z => NX.rev_ap(z, Nil{}), P.XD.ps(I.XGR(len, t, e2, e3, e4)), NX.rev_ap(Nn, [R]), A.xp_rev(17n, len, t, e4, X1)),
      A.rr(Nn, [R])))
  AB.subst(List<&2, NX.Ap>, z => G6(len, t, e2, e3, e4, lf, z, up), R <> Nn, als, Equal.sym(List<&2, NX.Ap>, als, R <> Nn, hals),
    als_d(len, t, d, e2, e3, e4, lf, up, h, hl2, hl3, h4l, hac, n23, n34, lr, g7,
      A.aloop(17n, len, t, d, e4, (e3 + 1 : U32), [R], UPR(len, t, e2, e3), h, N.lt_to_le(n((e3 + 1 : U32)), n(e4), n34), e4len, hg0, g5)))
