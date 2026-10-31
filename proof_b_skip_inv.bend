import Base
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_inv.bend as V
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# What an out-of-scope line NF.line found is made of: from
# PRE(len, t, s) == Skip{pos, e0 .. lf}, the cut (as proof_b_cut_inv.bend's
# inv), and the tests passed (POS, REF's letters, ALT's alleles, CR).

def S10(+pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> NF.Pre:
  NF.Skip{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}

def isS(p: NF.Pre) -> Type:
  match p:
    case NF.Skip{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      Unit
    case NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      Empty
    case NF.Slow{}:
      Empty
    case NF.Incomplete{}:
      Empty

def s_no(+p: NF.Pre, +k: NF.Pre, +h: {p == k : NF.Pre}, u: isS(k)) -> isS(p):
  %Equal.sym(NF.Pre, p, k, h) : isS(_)
  u

def PTS(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +nv = M.NUM(len, t, (e0 + 1 : U32), e1)
  {M.Nv.ok(nv) == True{} : Bool} & ({M.Nv.v(nv) == pos : U32}
  & ({(U32.is_lt((e2 + 1 : U32), e3) && M.LETT(len, t, (e2 + 1 : U32), e3)) == True{} : Bool}
  & ({M.OOS(len, t, (e3 + 1 : U32), e4) == True{} : Bool}
  & {M.CRT(len, t, e7, lf) == True{} : Bool})))

def PTSp(+len: U32, +t: AT.Tree<U32>, p: NF.Pre) -> Type:
  match p:
    case NF.Skip{+pos, +e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      PTS(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
    case NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      Unit
    case NF.Slow{}:
      Unit
    case NF.Incomplete{}:
      Unit

def SCut(p: NF.Pre) -> NF.Cut:
  match p:
    case NF.Skip{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}
    case NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      NF.Short{}
    case NF.Slow{}:
      NF.Short{}
    case NF.Incomplete{}:
      NF.Short{}

def jif(+pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.SIf(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}:
  match ok:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}, s_no(NF.Slow{}, k, h, u))

def jalt(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.SAlt(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}):
  match ok:
    case True{}:
      ({==}, jif(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.CRT(len, t, a7, alf), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}), s_no(NF.Slow{}, k, h, u))

def jref(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.SRef(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & ({M.OOS(len, t, (a3 + 1 : U32), a4) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})):
  match ok:
    case True{}:
      ({==}, jalt(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.OOS(len, t, (a3 + 1 : U32), a4), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & ({M.OOS(len, t, (a3 + 1 : U32), a4) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})), s_no(NF.Slow{}, k, h, u))

# The fast path's own tests never give Skip.
def jpif_no(+pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.PIf(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) -> Empty:
  match ok:
    case True{}:
      s_no(NF.Pass{pos, a0, a1, a2, a3, a4, a5, a6, a7, alf}, k, h, u)
    case False{}:
      s_no(NF.Slow{}, k, h, u)

def jinfo_no(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.PInfo(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) -> Empty:
  match ok:
    case True{}:
      jpif_no(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.CRT(len, t, a7, alf), k, u, h)
    case False{}:
      s_no(NF.Slow{}, k, h, u)

def JAL(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre) -> Type:
  {ok == False{} : Bool} & ({(U32.is_lt((a2 + 1 : U32), a3) && M.LETT(len, t, (a2 + 1 : U32), a3)) == True{} : Bool} & ({M.OOS(len, t, (a3 + 1 : U32), a4) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {S10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})))

def jal(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isS(k),
  +h: {M.PAl(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) -> JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok, k):
  match ok:
    case True{}:
      Empty.absurd(JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, True{}, k), jinfo_no(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.EK(len, t, (a6 + 1 : U32), a7, pos, (a3 - a2 - 1 : U32)), k, u, h))
    case False{}:
      ({==}, jref(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, (U32.is_lt((a2 + 1 : U32), a3) && M.LETT(len, t, (a2 + 1 : U32), a3)), k, u, h))

def JPOS(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +pos: U32, +k: NF.Pre) -> Type:
  {ok == True{} : Bool} & JAL(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4), k)

def jpos(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +pos: U32, +k: NF.Pre, u: isS(k),
  +h: {M.PPos(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok, pos) == k : NF.Pre}) -> JPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok, pos, k):
  match ok:
    case True{}:
      ({==}, jal(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4), k, u, h))
    case False{}:
      Empty.absurd(JPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, False{}, pos, k), s_no(NF.Slow{}, k, h, u))

def jptp_k(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  +hk: {S10(M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre},
  hok: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool},
  hlt: {(U32.is_lt((a2 + 1 : U32), a3) && M.LETT(len, t, (a2 + 1 : U32), a3)) == True{} : Bool},
  hoo: {M.OOS(len, t, (a3 + 1 : U32), a4) == True{} : Bool},
  hcr: {M.CRT(len, t, a7, alf) == True{} : Bool}) -> PTSp(len, t, k):
  %hk : PTSp(len, t, _)
  (hok, ({==}, (hlt, (hoo, hcr))))

def jpc_j(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  +hk: {S10(M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre},
  hok: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool},
  hlt: {(U32.is_lt((a2 + 1 : U32), a3) && M.LETT(len, t, (a2 + 1 : U32), a3)) == True{} : Bool},
  hoo: {M.OOS(len, t, (a3 + 1 : U32), a4) == True{} : Bool},
  hcr: {M.CRT(len, t, a7, alf) == True{} : Bool}) ->
  {V.K8(a0, a1, a2, a3, a4, a5, a6, a7, alf) == SCut(k) : NF.Cut} & PTSp(len, t, k):
  (Equal.cong(NF.Pre, NF.Cut, p => SCut(p), S10(M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf), k, hk), jptp_k(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, hk, hok, hlt, hoo, hcr))

def jpc_k(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  r: JPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)), M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), k)) ->
  {V.K8(a0, a1, a2, a3, a4, a5, a6, a7, alf) == SCut(k) : NF.Cut} & PTSp(len, t, k):
  match r:
    case (hok, r2):
      match r2:
        case (hal, r3):
          match r3:
            case (hlt, r4):
              match r4:
                case (hoo, r5):
                  match r5:
                    case (hcr, hk):
                      jpc_j(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, hk, hok, hlt, hoo, hcr)

def jpc(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut, +k: NF.Pre, u: isS(k), +h: {M.PC(len, t, c) == k : NF.Pre}) ->
  {c == SCut(k) : NF.Cut} & PTSp(len, t, k):
  match c:
    case NF.Cut8{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +alf}:
      +nv = M.NUM(len, t, (a0 + 1 : U32), a1)
      jpc_k(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, jpos(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.Nv.ok(nv), M.Nv.v(nv), k, u, h))
    case NF.Short{}:
      Empty.absurd({NF.Short{} == SCut(k) : NF.Cut} & PTSp(len, t, k), s_no(NF.Slow{}, k, h, u))
    case NF.Part{}:
      Empty.absurd({NF.Part{} == SCut(k) : NF.Cut} & PTSp(len, t, k), s_no(NF.Incomplete{}, k, h, u))

# Everything an out-of-scope line is made of.
def INVS(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  V.FI0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf) & PTS(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)

def invs_k(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  r: {M.MC(len, t, s) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & PTS(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) -> INVS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match r:
    case (hc, hpt):
      (V.i0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf, hc), hpt)

def invs(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: {M.PRE(len, t, s) == S10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Pre}) -> INVS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  invs_k(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, jpc(len, t, M.MC(len, t, s), S10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf), Unit{}, hp))

# The facts of INVS, handed to k one by one.
def dsts(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, -G: Type,
  r: INVS(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  k: {M.TP(len, t, s) == False{} : Bool} -> {M.TT(len, t, s) == True{} : Bool} -> {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool} -> {V.ME(len, t, s, V.LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == V.K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} -> {V.LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool} -> {M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)) == True{} : Bool} -> {M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)) == pos : U32} -> {(U32.is_lt((e2 + 1 : U32), e3) && M.LETT(len, t, (e2 + 1 : U32), e3)) == True{} : Bool} -> {M.OOS(len, t, (e3 + 1 : U32), e4) == True{} : Bool} -> {M.CRT(len, t, e7, lf) == True{} : Bool} -> G) -> G:
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
                                                                      match pt:
                                                                        case (h17, p17):
                                                                          match p17:
                                                                            case (h18, p18):
                                                                              match p18:
                                                                                case (h19, p19):
                                                                                  match p19:
                                                                                    case (h20, h21):
                                                                                      k(h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21)
