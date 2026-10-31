import Base
import ./norm_fast.bend as NF
import ./proof_b_fasteq.bend as FE
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-bytes@0.1.0.0/proof_same.bend as PS
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Every call NF.line makes on a buffer mirror C.BT(len, t) hands the mirror
# back, and what it answers is mirrored by a function on Data (len and t
# reusable). NF.line(BT, s) == Pr{BT, PRE(len, t, s)}.

# ---------------------------------------------------------------------------
# The searches
# ---------------------------------------------------------------------------

def F1(+len: U32, +t: AT.Tree<U32>, +a: U32, +to: U32, +c: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), a, to, c))

def F2(+len: U32, +t: AT.Tree<U32>, +a: U32, +to: U32, +c1: U32, +c2: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find2(C.BT(len, t), a, to, c1, c2))

def ff1(+len: U32, +t: AT.Tree<U32>, +a: U32, +to: U32, +c: U32) ->
  {F.find(C.BT(len, t), a, to, c) == (C.BT(len, t), F1(len, t, a, to, c)) : D.Bytes & U32}:
  FE.find_pair(C.BT(len, t), a, to, c)

def ff2(+len: U32, +t: AT.Tree<U32>, +a: U32, +to: U32, +c1: U32, +c2: U32) ->
  {F.find2(C.BT(len, t), a, to, c1, c2) == (C.BT(len, t), F2(len, t, a, to, c1, c2)) : D.Bytes & U32}:
  FE.find2_pair(C.BT(len, t), a, to, c1, c2)

# What the searches answer, on a well-formed buffer, a range within it and
# byte values (through bytes.bend's find: FE.find_eq, PF.find_view_t).
def f1_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +to: U32, +c: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hft: {U32.is_le(a, to) == True{} : Bool},
  +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {U32.to_nat(F1(len, t, a, to, c)) == D.first(D.view(C.BT(len, t)), U32.to_nat(a), U32.to_nat(to), c) : Nat}:
  Equal.trans(Nat, U32.to_nat(F1(len, t, a, to, c)), U32.to_nat(Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), a, to, c))), D.first(D.view(C.BT(len, t)), U32.to_nat(a), U32.to_nat(to), c),
    Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), F.find(C.BT(len, t), a, to, c), BY.find(C.BT(len, t), a, to, c), FE.find_eq(C.BT(len, t), d, a, to, c, hok, hft, ht, hc)),
    PF.find_view_t(len, t, d, a, to, c, hok, hft, ht, hc))

def f2_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +to: U32, +c1: U32, +c2: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hft: {U32.is_le(a, to) == True{} : Bool},
  +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool},
  +hc1: {U32.is_lt(c1, 256) == True{} : Bool},
  +hc2: {U32.is_lt(c2, 256) == True{} : Bool}) ->
  {U32.to_nat(F2(len, t, a, to, c1, c2)) == D.first2(D.view(C.BT(len, t)), U32.to_nat(a), U32.to_nat(to), c1, c2) : Nat}:
  Equal.trans(Nat, U32.to_nat(F2(len, t, a, to, c1, c2)), U32.to_nat(Pair.snd(D.Bytes, U32, BY.find2(C.BT(len, t), a, to, c1, c2))), D.first2(D.view(C.BT(len, t)), U32.to_nat(a), U32.to_nat(to), c1, c2),
    Equal.cong(D.Bytes & U32, Nat, r => U32.to_nat(Pair.snd(D.Bytes, U32, r)), F.find2(C.BT(len, t), a, to, c1, c2), BY.find2(C.BT(len, t), a, to, c1, c2), FE.find2_eq(C.BT(len, t), d, a, to, c1, c2, hok, hft, ht, hc1, hc2)),
    PF.find2_view_t(len, t, d, a, to, c1, c2, hok, hft, ht, hc1, hc2))

# The first tab or LF from a (TJ), and its flags: none before the end (TP),
# a tab (TT). The first LF from a (LJ).
def TJ(+len: U32, +t: AT.Tree<U32>, +a: U32) -> U32:
  F2(len, t, a, len, 9, 10)

def TP(+len: U32, +t: AT.Tree<U32>, +a: U32) -> Bool:
  U32.is_eq(TJ(len, t, a), len)

def TT(+len: U32, +t: AT.Tree<U32>, +a: U32) -> Bool:
  U32.is_eq(C.AT(len, t, TJ(len, t, a)), 9)

def LJ(+len: U32, +t: AT.Tree<U32>, +a: U32) -> U32:
  F1(len, t, a, len, 10)

def tab_t(+len: U32, +t: AT.Tree<U32>, +a: U32) ->
  {NF.tab(C.BT(len, t), a) == NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)} : NF.Tb}:
  +j = TJ(len, t, a)
  %Equal.sym(D.Bytes & U32, F.find2(C.BT(len, t), a, len, 9, 10), (C.BT(len, t), j), ff2(len, t, a, len, 9, 10)) :
    {NF.tab.k(len, _) == NF.Tb{C.BT(len, t), j, TP(len, t, a), TT(len, t, a)} : NF.Tb}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
    {NF.tab.fin(j, len, _) == NF.Tb{C.BT(len, t), j, TP(len, t, a), TT(len, t, a)} : NF.Tb}
  {==}

def lf_t(+len: U32, +t: AT.Tree<U32>, +a: U32) ->
  {NF.lf(C.BT(len, t), a) == NF.Tb{C.BT(len, t), LJ(len, t, a), U32.is_eq(LJ(len, t, a), len), False{}} : NF.Tb}:
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, len, 10), (C.BT(len, t), LJ(len, t, a)), ff1(len, t, a, len, 10)) :
    {NF.lf.k(len, _) == NF.Tb{C.BT(len, t), LJ(len, t, a), U32.is_eq(LJ(len, t, a), len), False{}} : NF.Tb}
  {==}

# ---------------------------------------------------------------------------
# The cut: field ends E0 .. E7 of the line at s, and the LF after a tab
# ending INFO (LF1)
# ---------------------------------------------------------------------------

def E0(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, s)

def E1(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E0(len, t, s) + 1 : U32))

def E2(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E1(len, t, s) + 1 : U32))

def E3(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E2(len, t, s) + 1 : U32))

def E4(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E3(len, t, s) + 1 : U32))

def E5(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E4(len, t, s) + 1 : U32))

def E6(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E5(len, t, s) + 1 : U32))

def E7(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  TJ(len, t, (E6(len, t, s) + 1 : U32))

def LF1(+len: U32, +t: AT.Tree<U32>, +s: U32) -> U32:
  LJ(len, t, (E7(len, t, s) + 1 : U32))

def LP(+len: U32, +t: AT.Tree<U32>, +s: U32) -> Bool:
  U32.is_eq(LF1(len, t, s), len)

def c8(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool) -> NF.Cut:
  match part:
    case True{}:
      NF.Part{}
    case False{}:
      NF.Cut8{E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), E7(len, t, s), LF1(len, t, s)}

def c7(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Cut8{E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), E7(len, t, s), E7(len, t, s)}
    case False{} True{}:
      c8(len, t, s, LP(len, t, s))

def c6(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c7(len, t, s, TP(len, t, (E6(len, t, s) + 1 : U32)), TT(len, t, (E6(len, t, s) + 1 : U32)))

def c5(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c6(len, t, s, TP(len, t, (E5(len, t, s) + 1 : U32)), TT(len, t, (E5(len, t, s) + 1 : U32)))

def c4(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c5(len, t, s, TP(len, t, (E4(len, t, s) + 1 : U32)), TT(len, t, (E4(len, t, s) + 1 : U32)))

def c3(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c4(len, t, s, TP(len, t, (E3(len, t, s) + 1 : U32)), TT(len, t, (E3(len, t, s) + 1 : U32)))

def c2(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c3(len, t, s, TP(len, t, (E2(len, t, s) + 1 : U32)), TT(len, t, (E2(len, t, s) + 1 : U32)))

def c1(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c2(len, t, s, TP(len, t, (E1(len, t, s) + 1 : U32)), TT(len, t, (E1(len, t, s) + 1 : U32)))

def c0(+len: U32, +t: AT.Tree<U32>, +s: U32, part: Bool, tab: Bool) -> NF.Cut:
  match part tab:
    case True{} _:
      NF.Part{}
    case False{} False{}:
      NF.Short{}
    case False{} True{}:
      c1(len, t, s, TP(len, t, (E0(len, t, s) + 1 : U32)), TT(len, t, (E0(len, t, s) + 1 : U32)))

def MC(+len: U32, +t: AT.Tree<U32>, +s: U32) -> NF.Cut:
  c0(len, t, s, TP(len, t, s), TT(len, t, s))

def k8_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +x: Bool) ->
  {NF.k8(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), E7(len, t, s), NF.Tb{C.BT(len, t), LF1(len, t, s), part, x})
    == NF.Cr{C.BT(len, t), c8(len, t, s, part)} : NF.Cr}:
  match part:
    case True{}:
      {==}
    case False{}:
      {==}

def k7_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k7(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), NF.Tb{C.BT(len, t), E7(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c7(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E7(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), a), NF.Tb{C.BT(len, t), LJ(len, t, a), U32.is_eq(LJ(len, t, a), len), False{}}, lf_t(len, t, a)) :
        {NF.k8(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), E7(len, t, s), _)
          == NF.Cr{C.BT(len, t), c8(len, t, s, LP(len, t, s))} : NF.Cr}
      k8_t(len, t, s, LP(len, t, s), False{})

def k6_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k6(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), NF.Tb{C.BT(len, t), E6(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c6(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E6(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k7(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), E6(len, t, s), _)
          == NF.Cr{C.BT(len, t), c7(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k7_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k5_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k5(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), NF.Tb{C.BT(len, t), E5(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c5(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E5(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k6(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), E5(len, t, s), _)
          == NF.Cr{C.BT(len, t), c6(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k6_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k4_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k4(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), NF.Tb{C.BT(len, t), E4(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c4(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E4(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k5(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), E4(len, t, s), _)
          == NF.Cr{C.BT(len, t), c5(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k5_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k3_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k3(E0(len, t, s), E1(len, t, s), E2(len, t, s), NF.Tb{C.BT(len, t), E3(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c3(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E3(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k4(E0(len, t, s), E1(len, t, s), E2(len, t, s), E3(len, t, s), _)
          == NF.Cr{C.BT(len, t), c4(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k4_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k2_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k2(E0(len, t, s), E1(len, t, s), NF.Tb{C.BT(len, t), E2(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c2(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E2(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k3(E0(len, t, s), E1(len, t, s), E2(len, t, s), _)
          == NF.Cr{C.BT(len, t), c3(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k3_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k1_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k1(E0(len, t, s), NF.Tb{C.BT(len, t), E1(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c1(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E1(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k2(E0(len, t, s), E1(len, t, s), _)
          == NF.Cr{C.BT(len, t), c2(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k2_t(len, t, s, TP(len, t, a), TT(len, t, a))

def k0_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +part: Bool, +tab: Bool) ->
  {NF.k0(NF.Tb{C.BT(len, t), E0(len, t, s), part, tab})
    == NF.Cr{C.BT(len, t), c0(len, t, s, part, tab)} : NF.Cr}:
  match part tab:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      +a = (E0(len, t, s) + 1 : U32)
      %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), a), NF.Tb{C.BT(len, t), TJ(len, t, a), TP(len, t, a), TT(len, t, a)}, tab_t(len, t, a)) :
        {NF.k1(E0(len, t, s), _)
          == NF.Cr{C.BT(len, t), c1(len, t, s, TP(len, t, a), TT(len, t, a))} : NF.Cr}
      k1_t(len, t, s, TP(len, t, a), TT(len, t, a))

def cut_t(+len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {NF.cut(C.BT(len, t), s) == NF.Cr{C.BT(len, t), MC(len, t, s)} : NF.Cr}:
  %Equal.sym(NF.Tb, NF.tab(C.BT(len, t), s), NF.Tb{C.BT(len, t), TJ(len, t, s), TP(len, t, s), TT(len, t, s)}, tab_t(len, t, s)) :
    {NF.k0(_) == NF.Cr{C.BT(len, t), MC(len, t, s)} : NF.Cr}
  k0_t(len, t, s, TP(len, t, s), TT(len, t, s))

# ---------------------------------------------------------------------------
# POS: num
# ---------------------------------------------------------------------------

type Nv is Data:
  Nv{ok: Bool, v: U32}

def Nv.ok(x: Nv) -> Bool:
  match x:
    case Nv{ok, v}:
      ok

def Nv.v(x: Nv) -> U32:
  match x:
    case Nv{ok, v}:
      v

# num.go on the mirror: x is byte j.
def NG(n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +j: U32, +acc: U32, ok: Bool) -> Nv:
  match n:
    case 0n:
      Nv{ok, acc}
    case 1n+m:
      NG(m, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), ((acc * 10 : U32) + (x - 48 : U32) : U32), ok && NF.is_digit(x))

def ng_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +j: U32, +acc: U32, +ok: Bool) ->
  {NF.num.go(n, (C.BT(len, t), x), j, acc, ok) == NF.Bv{C.BT(len, t), Nv.ok(NG(n, len, t, x, j, acc, ok)), Nv.v(NG(n, len, t, x, j, acc, ok))} : NF.Bv}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +j1 = (j + 1 : U32)
      +acc1 = ((acc * 10 : U32) + (x - 48 : U32) : U32)
      +ok1 = ok && NF.is_digit(x)
      +y = C.AT(len, t, j1)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j1), (C.BT(len, t), y), C.at_pair_t(len, t, j1)) :
        {NF.num.go(m, _, j1, acc1, ok1) == NF.Bv{C.BT(len, t), Nv.ok(NG(m, len, t, y, j1, acc1, ok1)), Nv.v(NG(m, len, t, y, j1, acc1, ok1))} : NF.Bv}
      ng_t(m, len, t, y, j1, acc1, ok1)

def NUM(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> Nv:
  +n = (to - from : U32)
  +x = C.AT(len, t, from)
  NG(U32.to_nat(U32.min(n, 10)), len, t, x, from, 0, U32.is_le(1, n) && U32.is_le(n, 9) && Bool.not(U32.is_eq(x, 48)))

def num_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) ->
  {NF.num(C.BT(len, t), from, to) == NF.Bv{C.BT(len, t), Nv.ok(NUM(len, t, from, to)), Nv.v(NUM(len, t, from, to))} : NF.Bv}:
  +n = (to - from : U32)
  +x = C.AT(len, t, from)
  +ok0 = U32.is_le(1, n) && U32.is_le(n, 9) && Bool.not(U32.is_eq(x, 48))
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), from), (C.BT(len, t), x), C.at_pair_t(len, t, from)) :
    {NF.num.k(from, n, _) == NF.Bv{C.BT(len, t), Nv.ok(NUM(len, t, from, to)), Nv.v(NUM(len, t, from, to))} : NF.Bv}
  ng_t(U32.to_nat(U32.min(n, 10)), len, t, x, from, 0, ok0)

# ---------------------------------------------------------------------------
# The alleles (only that the buffer comes back)
# ---------------------------------------------------------------------------

def BGm(n: Nat, +len: U32, +t: AT.Tree<U32>, +y: U32, +j: U32, ok: Bool, +x: U32) -> Nv:
  match n:
    case 0n:
      Nv{ok, x}
    case 1n+m:
      BGm(m, len, t, C.AT(len, t, (j + 1 : U32)), (j + 1 : U32), ok && NF.is_base(y), y)

def bg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +y: U32, +j: U32, +ok: Bool, +x: U32) ->
  {NF.bases.go(n, (C.BT(len, t), y), j, ok, x) == NF.Bv{C.BT(len, t), Nv.ok(BGm(n, len, t, y, j, ok, x)), Nv.v(BGm(n, len, t, y, j, ok, x))} : NF.Bv}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +j1 = (j + 1 : U32)
      +ok1 = ok && NF.is_base(y)
      +z = C.AT(len, t, j1)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j1), (C.BT(len, t), z), C.at_pair_t(len, t, j1)) :
        {NF.bases.go(m, _, j1, ok1, y) == NF.Bv{C.BT(len, t), Nv.ok(BGm(m, len, t, z, j1, ok1, y)), Nv.v(BGm(m, len, t, z, j1, ok1, y))} : NF.Bv}
      bg_t(m, len, t, z, j1, ok1, y)

def BAS(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> Nv:
  BGm(U32.to_nat((to - from : U32)), len, t, C.AT(len, t, from), from, True{}, 0)

def bases_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) ->
  {NF.bases(C.BT(len, t), from, to) == NF.Bv{C.BT(len, t), Nv.ok(BAS(len, t, from, to)), Nv.v(BAS(len, t, from, to))} : NF.Bv}:
  +x = C.AT(len, t, from)
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), from), (C.BT(len, t), x), C.at_pair_t(len, t, from)) :
    {NF.bases.go(U32.to_nat((to - from : U32)), _, from, True{}, 0) == NF.Bv{C.BT(len, t), Nv.ok(BAS(len, t, from, to)), Nv.v(BAS(len, t, from, to))} : NF.Bv}
  bg_t(U32.to_nat((to - from : U32)), len, t, x, from, True{}, 0)

def EQ(+len: U32, +t: AT.Tree<U32>, +i: U32, +n: U32, +j: U32, +m: U32) -> Bool:
  Pair.snd(D.Bytes, Bool, NF.eqa(C.BT(len, t), i, n, j, m))

def eqif_t(+q: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32, +j: U32, +n: U32) ->
  {NF.eqa.if(q, C.BT(len, t), i, j, n) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, NF.eqa.if(q, C.BT(len, t), i, j, n))) : D.Bytes & Bool}:
  match q:
    case True{}:
      PS.same1_pair_t(len, t, i, j, n)
    case False{}:
      {==}

def eqa_t(+len: U32, +t: AT.Tree<U32>, +i: U32, +n: U32, +j: U32, +m: U32) ->
  {NF.eqa(C.BT(len, t), i, n, j, m) == (C.BT(len, t), EQ(len, t, i, n, j, m)) : D.Bytes & Bool}:
  eqif_t(U32.is_eq(n, m), len, t, i, j, n)

def DGm(n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +lx: U32, +a: U32, +e: U32, f: Bool, more: Bool) -> Bool:
  match n more:
    case 0n _:
      f
    case 1n+k False{}:
      f
    case 1n+k True{}:
      +c = F1(len, t, a, e, 44)
      +eq = EQ(len, t, x, lx, a, (c - a : U32))
      DGm(k, len, t, x, lx, (c + 1 : U32), e, eq, Bool.not(eq) && U32.is_lt(c, e))

def dstep_t(+len: U32, +t: AT.Tree<U32>, +x: U32, +lx: U32, +a: U32, +e: U32, +f: Bool, +m: Bool) ->
  {NF.dup.step(NF.Dp{C.BT(len, t), x, lx, a, e, f, m})
    == NF.Dp{C.BT(len, t), x, lx, (F1(len, t, a, e, 44) + 1 : U32), e, EQ(len, t, x, lx, a, (F1(len, t, a, e, 44) - a : U32)),
      Bool.not(EQ(len, t, x, lx, a, (F1(len, t, a, e, 44) - a : U32))) && U32.is_lt(F1(len, t, a, e, 44), e)} : NF.Dp}:
  +c = F1(len, t, a, e, 44)
  +eq = EQ(len, t, x, lx, a, (c - a : U32))
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, e, 44), (C.BT(len, t), c), ff1(len, t, a, e, 44)) :
    {NF.dup.c(x, lx, a, e, _) == NF.Dp{C.BT(len, t), x, lx, (c + 1 : U32), e, eq, Bool.not(eq) && U32.is_lt(c, e)} : NF.Dp}
  %Equal.sym(D.Bytes & Bool, NF.eqa(C.BT(len, t), x, lx, a, (c - a : U32)), (C.BT(len, t), eq), eqa_t(len, t, x, lx, a, (c - a : U32))) :
    {NF.dup.eq(x, lx, e, c, _) == NF.Dp{C.BT(len, t), x, lx, (c + 1 : U32), e, eq, Bool.not(eq) && U32.is_lt(c, e)} : NF.Dp}
  {==}

def dg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +x: U32, +lx: U32, +a: U32, +e: U32, +f: Bool, +more: Bool) ->
  {NF.dup.go(n, NF.Dp{C.BT(len, t), x, lx, a, e, f, more}) == (C.BT(len, t), DGm(n, len, t, x, lx, a, e, f, more)) : D.Bytes & Bool}:
  match n more:
    case 0n _:
      {==}
    case 1n+k False{}:
      {==}
    case 1n+k True{}:
      +c = F1(len, t, a, e, 44)
      +eq = EQ(len, t, x, lx, a, (c - a : U32))
      +m2 = Bool.not(eq) && U32.is_lt(c, e)
      %Equal.sym(NF.Dp, NF.dup.step(NF.Dp{C.BT(len, t), x, lx, a, e, f, True{}}), NF.Dp{C.BT(len, t), x, lx, (c + 1 : U32), e, eq, m2}, dstep_t(len, t, x, lx, a, e, f, True{})) :
        {NF.dup.go(k, _) == (C.BT(len, t), DGm(k, len, t, x, lx, (c + 1 : U32), e, eq, m2)) : D.Bytes & Bool}
      dg_t(k, len, t, x, lx, (c + 1 : U32), e, eq, m2)

def DUP(+len: U32, +t: AT.Tree<U32>, +more: Bool, +x: U32, +lx: U32, +a: U32, +e: U32) -> Bool:
  DGm(16n, len, t, x, lx, a, e, False{}, more)

def dup_t(+len: U32, +t: AT.Tree<U32>, +more: Bool, +x: U32, +lx: U32, +a: U32, +e: U32) ->
  {NF.dup(more, C.BT(len, t), x, lx, a, e) == (C.BT(len, t), DUP(len, t, more, x, lx, a, e)) : D.Bytes & Bool}:
  dg_t(16n, len, t, x, lx, a, e, False{}, more)

type A4 is Data:
  A4{ok: Bool, lasts: Bool, firsts: Bool, long: Bool}

def A4.ok(r: A4) -> Bool:
  match r:
    case A4{ok, l, f, g}:
      ok

def A4.lasts(r: A4) -> Bool:
  match r:
    case A4{ok, l, f, g}:
      l

def A4.firsts(r: A4) -> Bool:
  match r:
    case A4{ok, l, f, g}:
      f

def A4.long(r: A4) -> Bool:
  match r:
    case A4{ok, l, f, g}:
      g

def ALT(+len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +c: U32, ls: Bool, fs: Bool, lg: Bool) -> A4:
  +f0 = C.AT(len, t, a)
  +bv = BAS(len, t, a, c)
  +ok1 = Nv.ok(bv) && U32.is_lt(a, c)
  +eqref = EQ(len, t, a, (c - a : U32), NF.Al.s3(al), NF.Al.l3(al))
  +dp = DUP(len, t, U32.is_lt(NF.Al.s4(al), a), a, (c - a : U32), NF.Al.s4(al), (a - 1 : U32))
  A4{(ok1 && Bool.not(eqref)) && Bool.not(dp), ls && U32.is_eq(Nv.v(bv), NF.Al.z3(al)), fs && U32.is_eq(f0, NF.Al.f3(al)), lg && U32.is_le(2, (c - a : U32))}

def ALTR(+len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +c: U32, +ls: Bool, +fs: Bool, +lg: Bool) -> NF.Ab:
  +r = ALT(len, t, al, a, c, ls, fs, lg)
  NF.Ab{C.BT(len, t), A4.ok(r), A4.lasts(r), A4.firsts(r), A4.long(r)}

def alt_t(+len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +c: U32, +ls: Bool, +fs: Bool, +lg: Bool) ->
  {NF.alt(al, a, c, ls, fs, lg, C.BT(len, t)) == ALTR(len, t, al, a, c, ls, fs, lg) : NF.Ab}:
  +f0 = C.AT(len, t, a)
  +bv = BAS(len, t, a, c)
  +ok1 = Nv.ok(bv) && U32.is_lt(a, c)
  +eqref = EQ(len, t, a, (c - a : U32), NF.Al.s3(al), NF.Al.l3(al))
  +mo = U32.is_lt(NF.Al.s4(al), a)
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), a), (C.BT(len, t), f0), C.at_pair_t(len, t, a)) :
    {NF.alt.first(al, a, c, ls, fs, lg, _) == ALTR(len, t, al, a, c, ls, fs, lg) : NF.Ab}
  %Equal.sym(NF.Bv, NF.bases(C.BT(len, t), a, c), NF.Bv{C.BT(len, t), Nv.ok(bv), Nv.v(bv)}, bases_t(len, t, a, c)) :
    {NF.alt.bases(al, a, c, f0, ls, fs, lg, _) == ALTR(len, t, al, a, c, ls, fs, lg) : NF.Ab}
  %Equal.sym(D.Bytes & Bool, NF.eqa(C.BT(len, t), a, (c - a : U32), NF.Al.s3(al), NF.Al.l3(al)), (C.BT(len, t), eqref), eqa_t(len, t, a, (c - a : U32), NF.Al.s3(al), NF.Al.l3(al))) :
    {NF.alt.dup(al, a, c, ok1, f0, Nv.v(bv), ls, fs, lg, _) == ALTR(len, t, al, a, c, ls, fs, lg) : NF.Ab}
  %Equal.sym(D.Bytes & Bool, NF.dup(mo, C.BT(len, t), a, (c - a : U32), NF.Al.s4(al), (a - 1 : U32)), (C.BT(len, t), DUP(len, t, mo, a, (c - a : U32), NF.Al.s4(al), (a - 1 : U32))),
    dup_t(len, t, mo, a, (c - a : U32), NF.Al.s4(al), (a - 1 : U32))) :
    {NF.alt.fin(al, a, c, ok1 && Bool.not(eqref), f0, Nv.v(bv), ls, fs, lg, _) == ALTR(len, t, al, a, c, ls, fs, lg) : NF.Ab}
  {==}

def AGm(n: Nat, +len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, ok: Bool, ls: Bool, fs: Bool, lg: Bool, more: Bool) -> Bool:
  match n more:
    case 0n _:
      False{}
    case 1n+k False{}:
      ok && Bool.not(ls) && Bool.not(fs && lg)
    case 1n+k True{}:
      +c = F1(len, t, a, NF.Al.e4(al), 44)
      +r = ALT(len, t, al, a, c, ls, fs, lg)
      AGm(k, len, t, al, (c + 1 : U32), A4.ok(r), A4.lasts(r), A4.firsts(r), A4.long(r), A4.ok(r) && U32.is_lt(c, NF.Al.e4(al)))

def ASR(+len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +ls: Bool, +fs: Bool, +lg: Bool) -> NF.As:
  +c = F1(len, t, a, NF.Al.e4(al), 44)
  +r = ALT(len, t, al, a, c, ls, fs, lg)
  NF.As{C.BT(len, t), al, (c + 1 : U32), A4.ok(r), A4.lasts(r), A4.firsts(r), A4.long(r), A4.ok(r) && U32.is_lt(c, NF.Al.e4(al))}

def astep_t(+len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +ok: Bool, +ls: Bool, +fs: Bool, +lg: Bool, +m: Bool) ->
  {NF.alts.step(NF.As{C.BT(len, t), al, a, ok, ls, fs, lg, m}) == ASR(len, t, al, a, ls, fs, lg) : NF.As}:
  +c = F1(len, t, a, NF.Al.e4(al), 44)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), a, NF.Al.e4(al), 44), (C.BT(len, t), c), ff1(len, t, a, NF.Al.e4(al), 44)) :
    {NF.alts.c(al, a, ls, fs, lg, _) == ASR(len, t, al, a, ls, fs, lg) : NF.As}
  %Equal.sym(NF.Ab, NF.alt(al, a, c, ls, fs, lg, C.BT(len, t)), ALTR(len, t, al, a, c, ls, fs, lg), alt_t(len, t, al, a, c, ls, fs, lg)) :
    {NF.alts.ab(al, c, _) == ASR(len, t, al, a, ls, fs, lg) : NF.As}
  {==}

def ag_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +al: NF.Al, +a: U32, +ok: Bool, +ls: Bool, +fs: Bool, +lg: Bool, +more: Bool) ->
  {NF.alts.go(n, NF.As{C.BT(len, t), al, a, ok, ls, fs, lg, more}) == (C.BT(len, t), AGm(n, len, t, al, a, ok, ls, fs, lg, more)) : D.Bytes & Bool}:
  match n more:
    case 0n _:
      {==}
    case 1n+k False{}:
      {==}
    case 1n+k True{}:
      +c = F1(len, t, a, NF.Al.e4(al), 44)
      +r = ALT(len, t, al, a, c, ls, fs, lg)
      +m2 = A4.ok(r) && U32.is_lt(c, NF.Al.e4(al))
      %Equal.sym(NF.As, NF.alts.step(NF.As{C.BT(len, t), al, a, ok, ls, fs, lg, True{}}), ASR(len, t, al, a, ls, fs, lg), astep_t(len, t, al, a, ok, ls, fs, lg, True{})) :
        {NF.alts.go(k, _) == (C.BT(len, t), AGm(k, len, t, al, (c + 1 : U32), A4.ok(r), A4.lasts(r), A4.firsts(r), A4.long(r), m2)) : D.Bytes & Bool}
      ag_t(k, len, t, al, (c + 1 : U32), A4.ok(r), A4.lasts(r), A4.firsts(r), A4.long(r), m2)

def AL(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32) -> Bool:
  +bv = BAS(len, t, s3, e3)
  +l3 = (e3 - s3 : U32)
  +go = Nv.ok(bv) && U32.is_lt(s3, e3) && U32.is_lt(s4, e4)
  AGm(17n, len, t, NF.Al{s3, l3, C.AT(len, t, s3), Nv.v(bv), s4, e4}, s4, go, True{}, True{}, U32.is_le(2, l3), go)

def alleles_t(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32) ->
  {NF.alleles(C.BT(len, t), s3, e3, s4, e4) == (C.BT(len, t), AL(len, t, s3, e3, s4, e4)) : D.Bytes & Bool}:
  +f3 = C.AT(len, t, s3)
  +bv = BAS(len, t, s3, e3)
  +l3 = (e3 - s3 : U32)
  +go = Nv.ok(bv) && U32.is_lt(s3, e3) && U32.is_lt(s4, e4)
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), s3), (C.BT(len, t), f3), C.at_pair_t(len, t, s3)) :
    {NF.alleles.f(s3, e3, s4, e4, _) == (C.BT(len, t), AL(len, t, s3, e3, s4, e4)) : D.Bytes & Bool}
  %Equal.sym(NF.Bv, NF.bases(C.BT(len, t), s3, e3), NF.Bv{C.BT(len, t), Nv.ok(bv), Nv.v(bv)}, bases_t(len, t, s3, e3)) :
    {NF.alleles.k(s3, e3, s4, e4, f3, _) == (C.BT(len, t), AL(len, t, s3, e3, s4, e4)) : D.Bytes & Bool}
  ag_t(17n, len, t, NF.Al{s3, l3, f3, Nv.v(bv), s4, e4}, s4, go, True{}, True{}, U32.is_le(2, l3), go)

# ---------------------------------------------------------------------------
# INFO: noend
# ---------------------------------------------------------------------------

def B4R(+len: U32, +t: AT.Tree<U32>, +j: U32) -> NF.B4:
  NF.B4{C.BT(len, t), C.AT(len, t, (j - 1 : U32)), C.AT(len, t, (j + 1 : U32)), C.AT(len, t, (j + 2 : U32)), C.AT(len, t, (j + 3 : U32))}

def b4_t(+len: U32, +t: AT.Tree<U32>, +j: U32) ->
  {NF.b4(C.BT(len, t), j) == NF.B4{C.BT(len, t), C.AT(len, t, (j - 1 : U32)), C.AT(len, t, (j + 1 : U32)), C.AT(len, t, (j + 2 : U32)), C.AT(len, t, (j + 3 : U32))} : NF.B4}:
  +p = C.AT(len, t, (j - 1 : U32))
  +nn = C.AT(len, t, (j + 1 : U32))
  +d = C.AT(len, t, (j + 2 : U32))
  +q = C.AT(len, t, (j + 3 : U32))
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), (j - 1 : U32)), (C.BT(len, t), p), C.at_pair_t(len, t, (j - 1 : U32))) :
    {NF.b4.p(j, _) == B4R(len, t, j) : NF.B4}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), (j + 1 : U32)), (C.BT(len, t), nn), C.at_pair_t(len, t, (j + 1 : U32))) :
    {NF.b4.n(p, j, _) == B4R(len, t, j) : NF.B4}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), (j + 2 : U32)), (C.BT(len, t), d), C.at_pair_t(len, t, (j + 2 : U32))) :
    {NF.b4.d(p, nn, j, _) == B4R(len, t, j) : NF.B4}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), (j + 3 : U32)), (C.BT(len, t), q), C.at_pair_t(len, t, (j + 3 : U32))) :
    {NF.b4.q(p, nn, d, _) == B4R(len, t, j) : NF.B4}
  {==}

# The E at j starts an END entry.
def END(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) -> Bool:
  +p = C.AT(len, t, (j - 1 : U32))
  +nn = C.AT(len, t, (j + 1 : U32))
  +d = C.AT(len, t, (j + 2 : U32))
  +qq = C.AT(len, t, (j + 3 : U32))
  +start = U32.is_eq(j, from) || U32.is_eq(p, 59)
  +key = U32.is_eq(nn, 78) && U32.is_eq(d, 68) && (U32.is_eq((j + 3 : U32), to) || U32.is_eq(qq, 61) || U32.is_eq(qq, 59))
  start && key

def NEy(none: Bool, +j: U32) -> U32:
  match none:
    case True{}:
      j
    case False{}:
      (j + 1 : U32)

def NEo(none: Bool, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) -> Bool:
  match none:
    case True{}:
      True{}
    case False{}:
      Bool.not(END(len, t, from, to, j))

def NEm(none: Bool, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) -> Bool:
  match none:
    case True{}:
      False{}
    case False{}:
      Bool.not(END(len, t, from, to, j))

def NER(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) -> NF.Ne:
  NF.Ne{C.BT(len, t), from, to, (j + 1 : U32), Bool.not(END(len, t, from, to, j)), Bool.not(END(len, t, from, to, j))}

def neif_t(+none: Bool, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +j: U32) ->
  {NF.noend.if(none, C.BT(len, t), from, to, j) == NF.Ne{C.BT(len, t), from, to, NEy(none, j), NEo(none, len, t, from, to, j), NEm(none, len, t, from, to, j)} : NF.Ne}:
  match none:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(NF.B4, NF.b4(C.BT(len, t), j), NF.B4{C.BT(len, t), C.AT(len, t, (j - 1 : U32)), C.AT(len, t, (j + 1 : U32)), C.AT(len, t, (j + 2 : U32)), C.AT(len, t, (j + 3 : U32))}, b4_t(len, t, j)) :
        {NF.noend.e(from, to, j, _) == NER(len, t, from, to, j) : NF.Ne}
      {==}

def NSR(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +y: U32) -> NF.Ne:
  +j = F1(len, t, y, to, 69)
  +none = U32.is_eq(j, to)
  NF.Ne{C.BT(len, t), from, to, NEy(none, j), NEo(none, len, t, from, to, j), NEm(none, len, t, from, to, j)}

def nstep_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +y: U32, +ok: Bool, +m: Bool) ->
  {NF.noend.step(NF.Ne{C.BT(len, t), from, to, y, ok, m}) == NSR(len, t, from, to, y) : NF.Ne}:
  +j = F1(len, t, y, to, 69)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), y, to, 69), (C.BT(len, t), j), ff1(len, t, y, to, 69)) :
    {NF.noend.k(from, to, _) == NSR(len, t, from, to, y) : NF.Ne}
  neif_t(U32.is_eq(j, to), len, t, from, to, j)

# noend.go on the mirror.
def NG2(n: Nat, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +y: U32, ok: Bool, more: Bool) -> Bool:
  match n more:
    case 0n _:
      False{}
    case 1n+k False{}:
      ok
    case 1n+k True{}:
      +j = F1(len, t, y, to, 69)
      +none = U32.is_eq(j, to)
      NG2(k, len, t, from, to, NEy(none, j), NEo(none, len, t, from, to, j), NEm(none, len, t, from, to, j))

def neg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +y: U32, +ok: Bool, +more: Bool) ->
  {NF.noend.go(n, NF.Ne{C.BT(len, t), from, to, y, ok, more}) == (C.BT(len, t), NG2(n, len, t, from, to, y, ok, more)) : D.Bytes & Bool}:
  match n more:
    case 0n _:
      {==}
    case 1n+k False{}:
      {==}
    case 1n+k True{}:
      +j = F1(len, t, y, to, 69)
      +none = U32.is_eq(j, to)
      %Equal.sym(NF.Ne, NF.noend.step(NF.Ne{C.BT(len, t), from, to, y, ok, True{}}), NSR(len, t, from, to, y), nstep_t(len, t, from, to, y, ok, True{})) :
        {NF.noend.go(k, _) == (C.BT(len, t), NG2(k, len, t, from, to, NEy(none, j), NEo(none, len, t, from, to, j), NEm(none, len, t, from, to, j))) : D.Bytes & Bool}
      neg_t(k, len, t, from, to, NEy(none, j), NEo(none, len, t, from, to, j), NEm(none, len, t, from, to, j))

def NE(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) -> Bool:
  NG2(U32.to_nat((to - from + 2 : U32)), len, t, from, to, from, True{}, True{})

def noend_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32) ->
  {NF.noend(C.BT(len, t), from, to) == (C.BT(len, t), NE(len, t, from, to)) : D.Bytes & Bool}:
  neg_t(U32.to_nat((to - from + 2 : U32)), len, t, from, to, from, True{}, True{})

# ---------------------------------------------------------------------------
# INFO: endok (its END entries, one entry at a time)
# ---------------------------------------------------------------------------

def LO(ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) -> Bool:
  match ok:
    case True{}:
      U32.is_eq(C.AT(len, t, j), k)
    case False{}:
      False{}

def lo_t(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) ->
  {NF.lit.one(ok, C.BT(len, t), k, j) == (C.BT(len, t), LO(ok, len, t, k, j)) : D.Bytes & Bool}:
  match ok:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {NF.lit.eq(k, _) == (C.BT(len, t), U32.is_eq(C.AT(len, t, j), k)) : D.Bytes & Bool}
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
  {NF.lit.go(ks, (C.BT(len, t), ok), j) == (C.BT(len, t), LIT(ks, len, t, ok, j)) : D.Bytes & Bool}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +q:
      %Equal.sym(D.Bytes & Bool, NF.lit.one(ok, C.BT(len, t), k, j), (C.BT(len, t), LO(ok, len, t, k, j)), lo_t(ok, len, t, k, j)) :
        {NF.lit.go(q, _, (j + 1 : U32)) == (C.BT(len, t), LIT(q, len, t, LO(ok, len, t, k, j), (j + 1 : U32))) : D.Bytes & Bool}
      lit_t(q, len, t, LO(ok, len, t, k, j), (j + 1 : U32))

def K3IF(three: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) -> Bool:
  match three:
    case True{}:
      LIT([69, 78, 68], len, t, True{}, j)
    case False{}:
      False{}

def k3if_t(+three: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) ->
  {NF.key3.if(three, C.BT(len, t), j) == (C.BT(len, t), K3IF(three, len, t, j)) : D.Bytes & Bool}:
  match three:
    case True{}:
      lit_t([69, 78, 68], len, t, True{}, j)
    case False{}:
      {==}

# The n bytes from j are END.
def KEY3(+len: U32, +t: AT.Tree<U32>, +j: U32, +n: U32) -> Bool:
  K3IF(U32.is_eq(n, 3), len, t, j)

def key3_t(+len: U32, +t: AT.Tree<U32>, +j: U32, +n: U32) ->
  {NF.key3(C.BT(len, t), j, n) == (C.BT(len, t), KEY3(len, t, j, n)) : D.Bytes & Bool}:
  k3if_t(U32.is_eq(n, 3), len, t, j)

# An Ek without its buffer (INFO's end to, POS and REF's length are fixed).
type ED is Data:
  ED{j: U32, ok: Bool, seen: Bool, more: Bool}

def ER(+len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, x: ED) -> NF.Ek:
  match x:
    case ED{j, ok, seen, m}:
      NF.Ek{C.BT(len, t), j, to, pos, rl, ok, seen, m}

def EW(+ok: Bool, seen: Bool, end: Bool, +sm: U32) -> ED:
  match end:
    case True{}:
      ED{sm, ok, seen, False{}}
    case False{}:
      ED{(sm + 1 : U32), ok, seen, ok}

def ew_t(+ok: Bool, +seen: Bool, +end: Bool, +sm: U32, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32) ->
  {NF.ek.w(ok, seen, end, C.BT(len, t), sm, to, pos, rl) == ER(len, t, to, pos, rl, EW(ok, seen, end, sm)) : NF.Ek}:
  match end:
    case True{}:
      {==}
    case False{}:
      {==}

# The END value x is pos + rl - 1 (and this is the first END entry).
def GOOD(ok: Bool, seen: Bool, vok: Bool, +x: U32, +pos: U32, +rl: U32) -> Bool:
  ok && Bool.not(seen) && vok && U32.is_le(pos, x) && U32.is_le(1, rl) && U32.is_eq((x - pos : U32), (rl - 1 : U32))

# An END entry with its '=' at ke: the next ';' (or INFO's end) at SM.
def EV(+len: U32, +t: AT.Tree<U32>, ok: Bool, seen: Bool, +ke: U32, +to: U32, +pos: U32, +rl: U32) -> ED:
  +sm = F1(len, t, ke, to, 59)
  +nv = NUM(len, t, (ke + 1 : U32), sm)
  EW(GOOD(ok, seen, Nv.ok(nv), Nv.v(nv), pos, rl), True{}, U32.is_eq(sm, to), sm)

def ev_t(+len: U32, +t: AT.Tree<U32>, +ok: Bool, +seen: Bool, +ke: U32, +to: U32, +pos: U32, +rl: U32) ->
  {NF.ek.val(ok, seen, ke, to, pos, rl, F.find(C.BT(len, t), ke, to, 59)) == ER(len, t, to, pos, rl, EV(len, t, ok, seen, ke, to, pos, rl)) : NF.Ek}:
  +sm = F1(len, t, ke, to, 59)
  +nv = NUM(len, t, (ke + 1 : U32), sm)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), ke, to, 59), (C.BT(len, t), sm), ff1(len, t, ke, to, 59)) :
    {NF.ek.val(ok, seen, ke, to, pos, rl, _) == ER(len, t, to, pos, rl, EV(len, t, ok, seen, ke, to, pos, rl)) : NF.Ek}
  %Equal.sym(NF.Bv, NF.num(C.BT(len, t), (ke + 1 : U32), sm), NF.Bv{C.BT(len, t), Nv.ok(nv), Nv.v(nv)}, num_t(len, t, (ke + 1 : U32), sm)) :
    {NF.ek.val.k(ok, seen, sm, to, pos, rl, _) == ER(len, t, to, pos, rl, EV(len, t, ok, seen, ke, to, pos, rl)) : NF.Ek}
  ew_t(GOOD(ok, seen, Nv.ok(nv), Nv.v(nv), pos, rl), True{}, U32.is_eq(sm, to), sm, len, t, to, pos, rl)

def EE(+ok: Bool, seen: Bool, isend: Bool, end: Bool, semi: Bool, +len: U32, +t: AT.Tree<U32>, +ke: U32, +to: U32, +pos: U32, +rl: U32) -> ED:
  match isend end semi:
    case False{} True{} _:
      ED{ke, ok, seen, False{}}
    case False{} False{} True{}:
      ED{(ke + 1 : U32), ok, seen, ok}
    case False{} False{} False{}:
      EW(ok, seen, U32.is_eq(F1(len, t, ke, to, 59), to), F1(len, t, ke, to, 59))
    case True{} False{} False{}:
      EV(len, t, ok, seen, ke, to, pos, rl)
    case True{} _ _:
      ED{ke, False{}, seen, False{}}

def ee_t(+ok: Bool, +seen: Bool, +isend: Bool, +end: Bool, +semi: Bool, +len: U32, +t: AT.Tree<U32>, +ke: U32, +to: U32, +pos: U32, +rl: U32) ->
  {NF.ek.e(ok, seen, isend, end, semi, C.BT(len, t), ke, to, pos, rl) == ER(len, t, to, pos, rl, EE(ok, seen, isend, end, semi, len, t, ke, to, pos, rl)) : NF.Ek}:
  match isend end semi:
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      +sm = F1(len, t, ke, to, 59)
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), ke, to, 59), (C.BT(len, t), sm), ff1(len, t, ke, to, 59)) :
        {NF.ek.v(ok, seen, to, pos, rl, _) == ER(len, t, to, pos, rl, EW(ok, seen, U32.is_eq(sm, to), sm)) : NF.Ek}
      ew_t(ok, seen, U32.is_eq(sm, to), sm, len, t, to, pos, rl)
    case True{} False{} False{}:
      ev_t(len, t, ok, seen, ke, to, pos, rl)
    case True{} True{} _:
      {==}
    case True{} False{} True{}:
      {==}

# The entry at j: its key ends at the first '=' or ';' (or INFO's end).
def EKE(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> U32:
  F2(len, t, j, to, 61, 59)

# ek.step on the mirror.
def ES(+len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +j: U32, ok: Bool, seen: Bool) -> ED:
  +ke = EKE(len, t, to, j)
  EE(ok, seen, KEY3(len, t, j, (ke - j : U32)), U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), len, t, ke, to, pos, rl)

def es_t(+len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +j: U32, +ok: Bool, +seen: Bool, +m: Bool) ->
  {NF.ek.step(NF.Ek{C.BT(len, t), j, to, pos, rl, ok, seen, m}) == ER(len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen)) : NF.Ek}:
  +ke = EKE(len, t, to, j)
  +k = KEY3(len, t, j, (ke - j : U32))
  %Equal.sym(D.Bytes & U32, F.find2(C.BT(len, t), j, to, 61, 59), (C.BT(len, t), ke), ff2(len, t, j, to, 61, 59)) :
    {NF.ek.k(j, to, ok, seen, pos, rl, _) == ER(len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen)) : NF.Ek}
  %Equal.sym(D.Bytes & Bool, NF.key3(C.BT(len, t), j, (ke - j : U32)), (C.BT(len, t), k), key3_t(len, t, j, (ke - j : U32))) :
    {NF.ek.h(ok, seen, ke, to, pos, rl, _) == ER(len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen)) : NF.Ek}
  %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), ke), (C.BT(len, t), C.AT(len, t, ke)), C.at_pair_t(len, t, ke)) :
    {NF.ek.n(ok, seen, k, ke, to, pos, rl, _) == ER(len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen)) : NF.Ek}
  ee_t(ok, seen, k, U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), len, t, ke, to, pos, rl)

# ek.go on the mirror.
def EG(n: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, x: ED) -> Bool:
  match n x:
    case 0n ED{j, ok, seen, m}:
      False{}
    case 1n+k ED{j, ok, seen, False{}}:
      ok
    case 1n+k ED{+j, ok, seen, True{}}:
      EG(k, len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen))

def eg_t(+n: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +x: ED) ->
  {NF.ek.go(n, ER(len, t, to, pos, rl, x)) == (C.BT(len, t), EG(n, len, t, to, pos, rl, x)) : D.Bytes & Bool}:
  match n x:
    case 0n ED{+j, +ok, +seen, +m}:
      {==}
    case 1n+k ED{+j, +ok, +seen, False{}}:
      {==}
    case 1n+k ED{+j, +ok, +seen, True{}}:
      %Equal.sym(NF.Ek, NF.ek.step(NF.Ek{C.BT(len, t), j, to, pos, rl, ok, seen, True{}}), ER(len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen)), es_t(len, t, to, pos, rl, j, ok, seen, True{})) :
        {NF.ek.go(k, _) == (C.BT(len, t), EG(k, len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen))) : D.Bytes & Bool}
      eg_t(k, len, t, to, pos, rl, ES(len, t, to, pos, rl, j, ok, seen))

# INFO (from .. to-1) passes NF.endok for POS pos and a REF of rl bytes.
def EK(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +pos: U32, +rl: U32) -> Bool:
  EG(U32.to_nat((to - from + 2 : U32)), len, t, to, pos, rl, ED{from, True{}, False{}, True{}})

def endok_t(+len: U32, +t: AT.Tree<U32>, +from: U32, +to: U32, +pos: U32, +rl: U32) ->
  {NF.endok(C.BT(len, t), from, to, pos, rl) == (C.BT(len, t), EK(len, t, from, to, pos, rl)) : D.Bytes & Bool}:
  eg_t(U32.to_nat((to - from + 2 : U32)), len, t, to, pos, rl, ED{from, True{}, False{}, True{}})

# ---------------------------------------------------------------------------
# The tests: NF.pre, and NF.line
# ---------------------------------------------------------------------------

# The final CR test is passed.
def CRT(+len: U32, +t: AT.Tree<U32>, +e7: U32, +lf: U32) -> Bool:
  Bool.not(U32.is_eq(e7, lf) && U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13))

def PIf(+pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, ok: Bool) -> NF.Pre:
  match ok:
    case True{}:
      NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}
    case False{}:
      NF.Slow{}

def PInfo(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, ok: Bool) -> NF.Pre:
  match ok:
    case True{}:
      PIf(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CRT(len, t, e7, lf))
    case False{}:
      NF.Slow{}

def PAl(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, ok: Bool) -> NF.Pre:
  match ok:
    case True{}:
      PInfo(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, EK(len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)))
    case False{}:
      NF.Slow{}

def PPos(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, ok: Bool, +pos: U32) -> NF.Pre:
  match ok:
    case True{}:
      PAl(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4))
    case False{}:
      NF.Slow{}

def PC(+len: U32, +t: AT.Tree<U32>, c: NF.Cut) -> NF.Pre:
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      PPos(len, t, e0, e1, e2, e3, e4, e5, e6, e7, lf, Nv.ok(NUM(len, t, (e0 + 1 : U32), e1)), Nv.v(NUM(len, t, (e0 + 1 : U32), e1)))
    case NF.Short{}:
      NF.Slow{}
    case NF.Part{}:
      NF.Incomplete{}

def PRE(+len: U32, +t: AT.Tree<U32>, +s: U32) -> NF.Pre:
  PC(len, t, MC(len, t, s))

def pif_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +ok: Bool) ->
  {NF.pre.if(ok, C.BT(len, t), NF.Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf}) == NF.Pr{C.BT(len, t), PIf(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ok)} : NF.Pr}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def pinfo_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +ok: Bool) ->
  {NF.pre.info.if(ok, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, C.BT(len, t)) == NF.Pr{C.BT(len, t), PInfo(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ok)} : NF.Pr}:
  match ok:
    case True{}:
      +x = C.AT(len, t, (lf - 1 : U32))
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), (lf - 1 : U32)), (C.BT(len, t), x), C.at_pair_t(len, t, (lf - 1 : U32))) :
        {NF.pre.cr(pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, _) == NF.Pr{C.BT(len, t), PIf(pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CRT(len, t, e7, lf))} : NF.Pr}
      pif_t(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, CRT(len, t, e7, lf))
    case False{}:
      {==}

def pal_t(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +ok: Bool) ->
  {NF.pre.al.if(ok, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, C.BT(len, t)) == NF.Pr{C.BT(len, t), PAl(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ok)} : NF.Pr}:
  match ok:
    case True{}:
      +ne = EK(len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32))
      %Equal.sym(D.Bytes & Bool, NF.endok(C.BT(len, t), (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)), (C.BT(len, t), ne), endok_t(len, t, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32))) :
        {NF.pre.info(pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, _) == NF.Pr{C.BT(len, t), PInfo(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ne)} : NF.Pr}
      pinfo_t(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ne)
    case False{}:
      {==}

def ppos_t(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +ok: Bool, +pos: U32) ->
  {NF.pre.pos(NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, NF.Bv{C.BT(len, t), ok, pos}) == NF.Pr{C.BT(len, t), PPos(len, t, e0, e1, e2, e3, e4, e5, e6, e7, lf, ok, pos)} : NF.Pr}:
  match ok:
    case True{}:
      +al = AL(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4)
      %Equal.sym(D.Bytes & Bool, NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4), (C.BT(len, t), al), alleles_t(len, t, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4)) :
        {NF.pre.al(pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, _) == NF.Pr{C.BT(len, t), PAl(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, al)} : NF.Pr}
      pal_t(len, t, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, al)
    case False{}:
      {==}

def pre_t(+len: U32, +t: AT.Tree<U32>, +s: U32, +c: NF.Cut) ->
  {NF.pre(s, NF.Cr{C.BT(len, t), c}) == NF.Pr{C.BT(len, t), PC(len, t, c)} : NF.Pr}:
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      +nv = NUM(len, t, (e0 + 1 : U32), e1)
      %Equal.sym(NF.Bv, NF.num(C.BT(len, t), (e0 + 1 : U32), e1), NF.Bv{C.BT(len, t), Nv.ok(nv), Nv.v(nv)}, num_t(len, t, (e0 + 1 : U32), e1)) :
        {NF.pre.pos(NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, _) == NF.Pr{C.BT(len, t), PPos(len, t, e0, e1, e2, e3, e4, e5, e6, e7, lf, Nv.ok(nv), Nv.v(nv))} : NF.Pr}
      ppos_t(len, t, e0, e1, e2, e3, e4, e5, e6, e7, lf, Nv.ok(nv), Nv.v(nv))
    case NF.Short{}:
      {==}
    case NF.Part{}:
      {==}

def line_t(+len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {NF.line(C.BT(len, t), s) == NF.Pr{C.BT(len, t), PRE(len, t, s)} : NF.Pr}:
  %Equal.sym(NF.Cr, NF.cut(C.BT(len, t), s), NF.Cr{C.BT(len, t), MC(len, t, s)}, cut_t(len, t, s)) :
    {NF.pre(s, _) == NF.Pr{C.BT(len, t), PRE(len, t, s)} : NF.Pr}
  pre_t(len, t, s, MC(len, t, s))
