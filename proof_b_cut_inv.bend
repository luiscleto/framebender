import Base
import ./norm_fast.bend as NF
import ./proof_b_cut_pair.bend as M
import ../lawful-arrays/proof_tree.bend as AT

# What a line that passes NF.line's tests is made of: from
# PRE(len, t, s) == Pass{pos, e0 .. lf}, the cut's flags (each field ends
# at a tab, INFO at a tab or the LF), the field ends as M.E0 .. M.E7, and
# the tests passed (POS, alleles, INFO, CR).

def K8(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> NF.Cut:
  NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}

def P10(+pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> NF.Pre:
  NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}

def isc8(c: NF.Cut) -> Type:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      Unit
    case NF.Short{}:
      Empty
    case NF.Part{}:
      Empty

def c8_no(+c: NF.Cut, +k: NF.Cut, +h: {c == k : NF.Cut}, u: isc8(k)) -> isc8(c):
  %Equal.sym(NF.Cut, c, k, h) : isc8(_)
  u

def isP(p: NF.Pre) -> Type:
  match p:
    case NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      Unit
    case NF.Slow{}:
      Empty
    case NF.Incomplete{}:
      Empty

def p_no(+p: NF.Pre, +k: NF.Pre, +h: {p == k : NF.Pre}, u: isP(k)) -> isP(p):
  %Equal.sym(NF.Pre, p, k, h) : isP(_)
  u

# ---------------------------------------------------------------------------
# The cut
# ---------------------------------------------------------------------------

# The line's LF: INFO's end (INFO ends at the LF) or the first LF after it.
def LFm(+len: U32, +t: AT.Tree<U32>, +s: U32, tab: Bool) -> U32:
  match tab:
    case False{}:
      M.E7(len, t, s)
    case True{}:
      M.LF1(len, t, s)

def LPm(+len: U32, +t: AT.Tree<U32>, +s: U32, tab: Bool) -> Bool:
  match tab:
    case False{}:
      False{}
    case True{}:
      M.LP(len, t, s)

def ME(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> NF.Cut:
  NF.Cut8{M.E0(len, t, s), M.E1(len, t, s), M.E2(len, t, s), M.E3(len, t, s), M.E4(len, t, s), M.E5(len, t, s), M.E6(len, t, s), M.E7(len, t, s), lf}

def FI7(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  {part == False{} : Bool} & ({ME(len, t, s, LFm(len, t, s, tab)) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & {LPm(len, t, s, tab) == False{} : Bool})

def i8(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c8(len, t, s, part) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  {ME(len, t, s, M.LF1(len, t, s)) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & {part == False{} : Bool}:
  match part:
    case True{}:
      Empty.absurd({ME(len, t, s, M.LF1(len, t, s)) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & {True{} == False{} : Bool},
        c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{}:
      (h, {==})

def i7(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c7(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI7(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI7(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      ({==}, (h, {==}))
    case False{} True{}:
      ({==}, i8(len, t, s, M.LP(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf, h))

def FI6(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E6(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI7(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i6(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c6(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI6(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI6(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI6(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E6(len, t, s) + 1 : U32)
      ({==}, ({==}, i7(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI5(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E5(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI6(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i5(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c5(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI5(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI5(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI5(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E5(len, t, s) + 1 : U32)
      ({==}, ({==}, i6(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI4(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E4(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI5(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i4(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c4(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI4(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI4(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI4(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E4(len, t, s) + 1 : U32)
      ({==}, ({==}, i5(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI3(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E3(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI4(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i3(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c3(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI3(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI3(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI3(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E3(len, t, s) + 1 : U32)
      ({==}, ({==}, i4(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI2(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E2(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI3(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i2(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c2(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI2(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI2(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI2(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E2(len, t, s) + 1 : U32)
      ({==}, ({==}, i3(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI1(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E1(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI2(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i1(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c1(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI1(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI1(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI1(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E1(len, t, s) + 1 : U32)
      ({==}, ({==}, i2(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

def FI0(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +a = (M.E0(len, t, s) + 1 : U32)
  {part == False{} : Bool} & ({tab == True{} : Bool} & FI1(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf))

def i0(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +h: {M.c0(len, t, s, part, tab) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut}) ->
  FI0(len, t, s, part, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match part tab:
    case True{} _:
      Empty.absurd(FI0(len, t, s, True{}, tab, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Part{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} False{}:
      Empty.absurd(FI0(len, t, s, False{}, False{}, e0, e1, e2, e3, e4, e5, e6, e7, lf), c8_no(NF.Short{}, K8(e0, e1, e2, e3, e4, e5, e6, e7, lf), h, Unit{}))
    case False{} True{}:
      +a = (M.E0(len, t, s) + 1 : U32)
      ({==}, ({==}, i1(len, t, s, M.TP(len, t, a), M.TT(len, t, a), e0, e1, e2, e3, e4, e5, e6, e7, lf, h)))

# ---------------------------------------------------------------------------
# The tests
# ---------------------------------------------------------------------------

def PT(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  +nv = M.NUM(len, t, (e0 + 1 : U32), e1)
  {M.Nv.ok(nv) == True{} : Bool} & ({M.Nv.v(nv) == pos : U32}
  & ({M.AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == True{} : Bool}
  & ({M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool}
  & {M.CRT(len, t, e7, lf) == True{} : Bool})))

def PTp(+len: U32, +t: AT.Tree<U32>, p: NF.Pre) -> Type:
  match p:
    case NF.Pass{+pos, +e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      PT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
    case NF.Slow{}:
      Unit
    case NF.Incomplete{}:
      Unit

def PCut(p: NF.Pre) -> NF.Cut:
  match p:
    case NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}
    case NF.Slow{}:
      NF.Short{}
    case NF.Incomplete{}:
      NF.Short{}

def iif(+pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isP(k),
  +h: {M.PIf(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}:
  match ok:
    case True{}:
      ({==}, h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}, p_no(NF.Slow{}, k, h, u))

def iinfo(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isP(k),
  +h: {M.PInfo(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}):
  match ok:
    case True{}:
      ({==}, iif(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.CRT(len, t, a7, alf), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre}), p_no(NF.Slow{}, k, h, u))

def ial(+len: U32, +t: AT.Tree<U32>, +pos: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +k: NF.Pre, u: isP(k),
  +h: {M.PAl(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok) == k : NF.Pre}) ->
  {ok == True{} : Bool} & ({M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})):
  match ok:
    case True{}:
      ({==}, iinfo(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.NE(len, t, (a6 + 1 : U32), a7), k, u, h))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & ({M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})), p_no(NF.Slow{}, k, h, u))

def IPOS(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +pos: U32, +k: NF.Pre) -> Type:
  {ok == True{} : Bool} & ({M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4) == True{} : Bool} & ({M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool} & ({M.CRT(len, t, a7, alf) == True{} : Bool} & {P10(pos, a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre})))

def ipos(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +ok: Bool, +pos: U32, +k: NF.Pre, u: isP(k),
  +h: {M.PPos(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok, pos) == k : NF.Pre}) -> IPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, ok, pos, k):
  match ok:
    case True{}:
      ({==}, ial(len, t, pos, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4), k, u, h))
    case False{}:
      Empty.absurd(IPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, False{}, pos, k), p_no(NF.Slow{}, k, h, u))

def ptp_k(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  +hk: {P10(M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre},
  hok: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool},
  hal: {M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4) == True{} : Bool},
  hne: {M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool},
  hcr: {M.CRT(len, t, a7, alf) == True{} : Bool}) -> PTp(len, t, k):
  %hk : PTp(len, t, _)
  (hok, ({==}, (hal, (hne, hcr))))

def ipc_j(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  +hk: {P10(M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), a0, a1, a2, a3, a4, a5, a6, a7, alf) == k : NF.Pre},
  hok: {M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)) == True{} : Bool},
  hal: {M.AL(len, t, (a2 + 1 : U32), a3, (a3 + 1 : U32), a4) == True{} : Bool},
  hne: {M.NE(len, t, (a6 + 1 : U32), a7) == True{} : Bool},
  hcr: {M.CRT(len, t, a7, alf) == True{} : Bool}) ->
  {K8(a0, a1, a2, a3, a4, a5, a6, a7, alf) == PCut(k) : NF.Cut} & PTp(len, t, k):
  +v = M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1))
  (Equal.cong(NF.Pre, NF.Cut, p => PCut(p), P10(v, a0, a1, a2, a3, a4, a5, a6, a7, alf), k, hk), ptp_k(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, hk, hok, hal, hne, hcr))

def ipc_k(+len: U32, +t: AT.Tree<U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +alf: U32, +k: NF.Pre,
  r: IPOS(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.Nv.ok(M.NUM(len, t, (a0 + 1 : U32), a1)), M.Nv.v(M.NUM(len, t, (a0 + 1 : U32), a1)), k)) ->
  {K8(a0, a1, a2, a3, a4, a5, a6, a7, alf) == PCut(k) : NF.Cut} & PTp(len, t, k):
  match r:
    case (hok, r2):
      match r2:
        case (hal, r3):
          match r3:
            case (hne, r4):
              match r4:
                case (hcr, hk):
                  ipc_j(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, hk, hok, hal, hne, hcr)

def ipc(+len: U32, +t: AT.Tree<U32>, +c: NF.Cut, +k: NF.Pre, u: isP(k), +h: {M.PC(len, t, c) == k : NF.Pre}) ->
  {c == PCut(k) : NF.Cut} & PTp(len, t, k):
  match c:
    case NF.Cut8{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +alf}:
      +nv = M.NUM(len, t, (a0 + 1 : U32), a1)
      ipc_k(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, k, ipos(len, t, a0, a1, a2, a3, a4, a5, a6, a7, alf, M.Nv.ok(nv), M.Nv.v(nv), k, u, h))
    case NF.Short{}:
      Empty.absurd({NF.Short{} == PCut(k) : NF.Cut} & PTp(len, t, k), p_no(NF.Slow{}, k, h, u))
    case NF.Part{}:
      Empty.absurd({NF.Part{} == PCut(k) : NF.Cut} & PTp(len, t, k), p_no(NF.Incomplete{}, k, h, u))

# Everything a passed line is made of.
def INV(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  FI0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf) & PT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)

def inv_k(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  r: {M.MC(len, t, s) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} & PT(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) -> INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  match r:
    case (hc, hpt):
      (i0(len, t, s, M.TP(len, t, s), M.TT(len, t, s), e0, e1, e2, e3, e4, e5, e6, e7, lf, hc), hpt)

def inv(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: {M.PRE(len, t, s) == P10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Pre}) -> INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf):
  inv_k(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ipc(len, t, M.MC(len, t, s), P10(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf), Unit{}, hp))

# The facts of INV, handed to k one by one.
def dst(+len: U32, +t: AT.Tree<U32>, +s: U32, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, -G: Type,
  r: INV(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  k: {M.TP(len, t, s) == False{} : Bool} -> {M.TT(len, t, s) == True{} : Bool} -> {M.TP(len, t, (M.E0(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E0(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E1(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E1(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E2(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E2(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E3(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E3(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E4(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E4(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E5(len, t, s) + 1 : U32)) == False{} : Bool} -> {M.TT(len, t, (M.E5(len, t, s) + 1 : U32)) == True{} : Bool} -> {M.TP(len, t, (M.E6(len, t, s) + 1 : U32)) == False{} : Bool} -> {ME(len, t, s, LFm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32)))) == K8(e0, e1, e2, e3, e4, e5, e6, e7, lf) : NF.Cut} -> {LPm(len, t, s, M.TT(len, t, (M.E6(len, t, s) + 1 : U32))) == False{} : Bool} -> {M.Nv.ok(M.NUM(len, t, (e0 + 1 : U32), e1)) == True{} : Bool} -> {M.Nv.v(M.NUM(len, t, (e0 + 1 : U32), e1)) == pos : U32} -> {M.AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == True{} : Bool} -> {M.NE(len, t, (e6 + 1 : U32), e7) == True{} : Bool} -> {M.CRT(len, t, e7, lf) == True{} : Bool} -> G) -> G:
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
