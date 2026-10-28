import Base
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import ./proof_c_pre_pair.bend as P
import ../lawful-arrays/proof_tree.bend as AT

# What a line that passes NX.line's tests is made of: from
# P.FX(len, t, s) == Fix{pos, Cut8{e0 .. lf}, als, up}, the cut (M.MC is
# Cut8{e0 .. lf}, so phase B's V.i0 gives the flags of every search) and the
# tests passed (TT).

def isF(p: NX.Fp) -> Type:
  match p:
    case NX.Fix{pos, c, als, up}:
      Unit
    case NX.No{}:
      Empty

def f_no(+p: NX.Fp, +k: NX.Fp, +h: {p == k : NX.Fp}, u: isF(k)) -> isF(p):
  %Equal.sym(NX.Fp, p, k, h) : isF(_)
  u

# The ALT loop's answer for the line's REF (e2 + 1 .. e3) and ALT (to e4).
def XGR(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32) -> P.XD:
  P.XG(17n, len, t, e4, P.X0((e2 + 1 : U32), e3, P.L2.up(P.LETS(len, t, (e2 + 1 : U32), e3))))

# The tests passed.
def TT(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool) -> Type:
  {M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)) == True{} : Bool}
  & ({M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)) == pos : U32}
  & ({P.L2.ok(P.LETS(len, t, (e2 + 1 : U32), e3)) == True{} : Bool}
  & ({(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4)) == True{} : Bool}
  & ({P.XD.ok(XGR(len, t, e2, e3, e4)) == True{} : Bool}
  & ({NX.rev_ap(P.XD.ps(XGR(len, t, e2, e3, e4)), Nil{}) == als : List<&2, NX.Ap>}
  & ({P.XD.up(XGR(len, t, e2, e3, e4)) == up : Bool}
  & ({M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool}
  & ({P.NOST(len, t, (e6 + 1 : U32), e7) == True{} : Bool}
  & {M.CRT(len, t, e7, lf) == True{} : Bool}))))))))

def TTk(+len: U32, +t: AT.Tree<U32>, k: NX.Fp) -> Type:
  match k:
    case NX.Fix{+pos, c, +als, +up}:
      match c:
        case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
          TT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)
        case NF.Short{}:
          Unit
        case NF.Part{}:
          Unit
    case NX.No{}:
      Unit

def FCut(k: NX.Fp) -> NF.Cut:
  match k:
    case NX.Fix{pos, c, als, up}:
      c
    case NX.No{}:
      NF.Short{}

# ---------------------------------------------------------------------------
# Level by level
# ---------------------------------------------------------------------------

def jif(+ok: Bool, +p: NX.Fp, +k: NX.Fp, u: isF(k), +h: {P.FIF(ok, p) == k : NX.Fp}) ->
  {ok == True{} : Bool} & {p == k : NX.Fp}:
  match ok:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {p == k : NX.Fp}, f_no(NX.No{}, k, h, u))

def JST(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e7: U32, +lf: U32, +c: NF.Cut, +als: List<&2, NX.Ap>, +up: Bool, +k: NX.Fp) -> Type:
  {M.CRT(len, t, e7, lf) == True{} : Bool} & {NX.Fix{pos, c, als, up} == k : NX.Fp}

def jst(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +als: List<&2, NX.Ap>, +up: Bool, +ok: Bool, +k: NX.Fp, u: isF(k),
  +h: {P.FST(len, t, pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up, ok) == k : NX.Fp}) ->
  {ok == True{} : Bool} & JST(len, t, pos, a7, alf, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up, k):
  match ok:
    case True{}:
      ({==}, jif(M.CRT(len, t, a7, alf), NX.Fix{pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up}, k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & JST(len, t, pos, a7, alf, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up, k), f_no(NX.No{}, k, h, u))

def JIN(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +als: List<&2, NX.Ap>, +up: Bool, +k: NX.Fp) -> Type:
  {P.NOST(len, t, (a6 + 1 : U32), a7) == True{} : Bool} & JST(len, t, pos, a7, alf, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up, k)

def jinfo(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +als: List<&2, NX.Ap>, +up: Bool, +ok: Bool, +k: NX.Fp, u: isF(k),
  +h: {P.FINFO(len, t, pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, als, up, ok) == k : NX.Fp}) ->
  {ok == True{} : Bool} & JIN(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, als, up, k):
  match ok:
    case True{}:
      ({==}, jst(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, als, up, P.NOST(len, t, (a6 + 1 : U32), a7), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & JIN(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, als, up, k), f_no(NX.No{}, k, h, u))

def JAL(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +x: P.XD, +k: NX.Fp) -> Type:
  {P.XD.ok(x) == True{} : Bool} & ({M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool} & JIN(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, NX.rev_ap(P.XD.ps(x), Nil{}), P.XD.up(x), k))

def jalts(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +x: P.XD, +k: NX.Fp, u: isF(k),
  +h: {P.FALTS(len, t, pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, x) == k : NX.Fp}) ->
  JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, x, k):
  match x:
    case P.XD{+a, +ps, True{}, +up, +m}:
      ({==}, jinfo(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, NX.rev_ap(ps, Nil{}), up, M.NE(len, t, (a6 + 1 : U32), a7), k, u, h))
    case P.XD{+a, +ps, False{}, +up, +m}:
      Empty.absurd(JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, P.XD{a, ps, False{}, up, m}, k), f_no(NX.No{}, k, h, u))

def JRF(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +up: Bool, +k: NX.Fp) -> Type:
  JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, P.XG(17n, len, t, a4, P.X0((a2 + 1 : U32), a3, up)), k)

def jrif(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +up: Bool, +ok: Bool, +k: NX.Fp, u: isF(k),
  +h: {P.FRIF(ok, len, t, pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, (a2 + 1 : U32), a3, a4, up) == k : NX.Fp}) ->
  {ok == True{} : Bool} & JRF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, k):
  match ok:
    case True{}:
      ({==}, jalts(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, P.XG(17n, len, t, a4, P.X0((a2 + 1 : U32), a3, up)), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & JRF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, k), f_no(NX.No{}, k, h, u))

def JREF(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +up: Bool, +k: NX.Fp) -> Type:
  {(U32.is_lt((a2 + 1 : U32), a3) && U32.is_lt((a3 + 1 : U32), a4)) == True{} : Bool} & JRF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, k)

def jref(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +up: Bool, +k: NX.Fp, u: isF(k),
  +h: {P.FREF(len, t, pos, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, ok, up) == k : NX.Fp}) ->
  {ok == True{} : Bool} & JREF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, k):
  match ok:
    case True{}:
      ({==}, jrif(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, U32.is_lt((a2 + 1 : U32), a3) && U32.is_lt((a3 + 1 : U32), a4), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & JREF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, up, k), f_no(NX.No{}, k, h, u))

def JPOS(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NX.Fp) -> Type:
  {P.L2.ok(P.LETS(len, t, (a2 + 1 : U32), a3)) == True{} : Bool} & JREF(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, P.L2.up(P.LETS(len, t, (a2 + 1 : U32), a3)), k)

def jpos(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +pos: U32, +k: NX.Fp, u: isF(k),
  +h: {P.FPOS(len, t, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, ok, pos) == k : NX.Fp}) ->
  {ok == True{} : Bool} & JPOS(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, k):
  match ok:
    case True{}:
      +lv = P.LETS(len, t, (a2 + 1 : U32), a3)
      ({==}, jref(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, P.L2.ok(lv), P.L2.up(lv), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & JPOS(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, k), f_no(NX.No{}, k, h, u))

# ---------------------------------------------------------------------------
# The facts, moved onto k
# ---------------------------------------------------------------------------

def kk(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NX.Fp,
  +hk: {NX.Fix{M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, NX.rev_ap(P.XD.ps(XGR(len, t, a2, a3, a4)), Nil{}), P.XD.up(XGR(len, t, a2, a3, a4))} == k : NX.Fp},
  +h1: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool},
  +h3: {P.L2.ok(P.LETS(len, t, (a2 + 1 : U32), a3)) == True{} : Bool},
  +h4: {(U32.is_lt((a2 + 1 : U32), a3) && U32.is_lt((a3 + 1 : U32), a4)) == True{} : Bool},
  +h5: {P.XD.ok(XGR(len, t, a2, a3, a4)) == True{} : Bool},
  +h8: {M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool},
  +h9: {P.NOST(len, t, (a6 + 1 : U32), a7) == True{} : Bool},
  +h10: {M.CRT(len, t, a7, alf) == True{} : Bool}) ->
  {NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf} == FCut(k) : NF.Cut} & TTk(len, t, k):
  +v = M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1))
  +X = XGR(len, t, a2, a3, a4)
  (Equal.cong(NX.Fp, NF.Cut, p => FCut(p), NX.Fix{v, NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf}, NX.rev_ap(P.XD.ps(X), Nil{}), P.XD.up(X)}, k, hk),
    %hk : TTk(len, t, _)
    (h1, ({==}, (h3, (h4, (h5, ({==}, ({==}, (h8, (h9, h10))))))))))

def kc(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NX.Fp,
  r: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool} & JPOS(len, t, M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf, k)) ->
  {NF.Cut8{a0, a1, a2, a3, a4, a5, a6, a7, alf} == FCut(k) : NF.Cut} & TTk(len, t, k):
  match r:
    case (h1, r2):
      match r2:
        case (h3, r3):
          match r3:
            case (h4, r4):
              match r4:
                case (h5, r5):
                  match r5:
                    case (h8, r6):
                      match r6:
                        case (h9, r7):
                          match r7:
                            case (h10, hk):
                              kk(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, hk, h1, h3, h4, h5, h8, h9, h10)

def jcut(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut, +k: NX.Fp, u: isF(k), +h: {P.FCUT(len, t, c) == k : NX.Fp}) ->
  {c == FCut(k) : NF.Cut} & TTk(len, t, k):
  match c:
    case NF.Cut8{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +alf}:
      +nv = M.NUM(len, t, (a0 + 1 : U32), a1)
      kc(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, jpos(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.Nv.ok(nv), M.Nv.v(nv), k, u, h))
    case NF.Short{}:
      Empty.absurd({NF.Short{} == FCut(k) : NF.Cut} & TTk(len, t, k), f_no(NX.No{}, k, h, u))
    case NF.Part{}:
      Empty.absurd({NF.Part{} == FCut(k) : NF.Cut} & TTk(len, t, k), f_no(NX.No{}, k, h, u))

# Everything a passed line is made of.
def INV(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool) -> Type:
  V.FI0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf) & TT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)

def inv_k(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  r: {M.MC(len, t, s) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & TT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up):
  match r:
    case (hc, htt):
      (V.i0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf, hc), htt)

def inv(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: {P.FX(len, t, s) == NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up} : NX.Fp}) ->
  INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up):
  inv_k(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up,
    jcut(len, t, M.MC(len, t, s), NX.Fix{pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, als, up}, Unit{}, hp))

# The facts of INV, handed to k one by one.
def dst(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, -G: Type,
  r: INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  k: {M.TP(len, t, s) == False{} : Bool} -> {M.TT(len, t, s) == True{} : Bool} -> {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool} -> {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} -> {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool} -> TT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up) -> G) -> G:
  match r:
    case (c, pt):
      match c:
        case (h0, c0):
          match c0:
            case (h1, c1):
              match c1:
                case (h2, c2):
                  match c2:
                    case (h3, c3):
                      match c3:
                        case (h4, c4):
                          match c4:
                            case (h5, c5):
                              match c5:
                                case (h6, c6):
                                  match c6:
                                    case (h7, c7):
                                      match c7:
                                        case (h8, c8):
                                          match c8:
                                            case (h9, c9):
                                              match c9:
                                                case (h10, c10):
                                                  match c10:
                                                    case (h11, c11):
                                                      match c11:
                                                        case (h12, c12):
                                                          match c12:
                                                            case (h13, c13):
                                                              match c13:
                                                                case (h14, c14):
                                                                  match c14:
                                                                    case (h15, h16):
                                                                      k(h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, pt)

# The tests, handed to k one by one.
def dtt(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, -G: Type,
  r: TT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  k: {M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)) == True{} : Bool} -> {M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)) == pos : U32} -> {P.L2.ok(P.LETS(len, t, (e2 + 1 : U32), e3)) == True{} : Bool} -> {(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4)) == True{} : Bool} -> {P.XD.ok(XGR(len, t, e2, e3, e4)) == True{} : Bool} -> {NX.rev_ap(P.XD.ps(XGR(len, t, e2, e3, e4)), Nil{}) == als : List<&2, NX.Ap>} -> {P.XD.up(XGR(len, t, e2, e3, e4)) == up : Bool} -> {M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool} -> {P.NOST(len, t, (e6 + 1 : U32), e7) == True{} : Bool} -> {M.CRT(len, t, e7, lf) == True{} : Bool} -> G) -> G:
  match r:
    case (g1, r1):
      match r1:
        case (g2, r2):
          match r2:
            case (g3, r3):
              match r3:
                case (g4, r4):
                  match r4:
                    case (g5, r5):
                      match r5:
                        case (g6, r6):
                          match r6:
                            case (g7, r7):
                              match r7:
                                case (g8, r8):
                                  match r8:
                                    case (g9, g10):
                                      k(g1, g2, g3, g4, g5, g6, g7, g8, g9, g10)
