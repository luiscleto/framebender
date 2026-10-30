import Base
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_b_fasteq.bend as FE
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/LAWS.bend as BL
import lawful-bytes@0.1.0.0/PROOF.bend as BP
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-fields@0.1.0.0/fields.bend as FC
import lawful-fields@0.1.0.0/LAWS.bend as FL
import lawful-fields@0.1.0.0/PROOF.bend as FP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's cut (norm_split.bend's cut.ends: lawful-fields' cut with
# fast.bend's find) is lawful-fields' FC.cut on a well-formed line, so
# lawful-fields' laws (cut_view, cut_bounds, split_text) say what it gives.
# Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def BT(+len: U32, +t: AT.Tree<U32>) -> D.Bytes:
  C.BT(len, t)

def L32() -> Data:
  List<&2, U32>

def Rs() -> Type:
  D.Bytes & List<&2, U32>

# The next end: the same search, the fast one or the reference.
def nx_go(+c: Bool, +m: Nat, +go: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +from: U32, +to: U32, +sep: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool},
  +hs: {U32.is_lt(sep, 256) == True{} : Bool},
  hf: {c == True{} : Bool} -> {U32.is_le(from, to) == True{} : Bool},
  ih: @+e2: U32 -> {NS.cut.go(m, go, (C.BT(len, t), e2), to, sep) == FC.cut.go(m, go, (C.BT(len, t), e2), to, sep) : Rs()}) ->
  {NS.cut.go(m, go, NS.cut.next(c, C.BT(len, t), from, to, sep), to, sep) == FC.cut.go(m, go, FC.cut.next(c, C.BT(len, t), from, to, sep), to, sep) : Rs()}:
  match c:
    case True{}:
      +j = Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), from, to, sep))
      %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), from, to, sep), BY.find(C.BT(len, t), from, to, sep), FE.find_eq(C.BT(len, t), d, from, to, sep, hok, hf({==}), hto, hs)) :
        {NS.cut.go(m, go, _, to, sep) == FC.cut.go(m, go, BY.find(C.BT(len, t), from, to, sep), to, sep) : Rs()}
      %Equal.sym(D.Bytes & U32, BY.find(C.BT(len, t), from, to, sep), (C.BT(len, t), j), BL.find_pair(C.BT(len, t), from, to, sep)) :
        {NS.cut.go(m, go, _, to, sep) == FC.cut.go(m, go, BY.find(C.BT(len, t), from, to, sep), to, sep) : Rs()}
      %Equal.sym(D.Bytes & U32, BY.find(C.BT(len, t), from, to, sep), (C.BT(len, t), j), BL.find_pair(C.BT(len, t), from, to, sep)) :
        {NS.cut.go(m, go, (C.BT(len, t), j), to, sep) == FC.cut.go(m, go, _, to, sep) : Rs()}
      ih(j)
    case False{}:
      ih(to)

# e < to: e + 1 <= to.
def inc_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +to: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool},
  +h: {U32.is_lt(e, to) == True{} : Bool}) -> {U32.is_le((e + 1 : U32), to) == True{} : Bool}:
  +he = Equal.trans(Bool, Nat.is_lt(n(e), n(to)), U32.is_lt(e, to), True{}, Equal.sym(Bool, U32.is_lt(e, to), Nat.is_lt(n(e), n(to)), U.is_lt_to_nat(e, to)), h)
  +hel = N.lt_le_trans(n(e), n(to), n(len), he, hto)
  +hl = Equal.trans(Bool, U32.is_lt(e, len), Nat.is_lt(n(e), n(len)), True{}, U.is_lt_to_nat(e, len), hel)
  %Equal.sym(Bool, U32.is_le((e + 1 : U32), to), Nat.is_le(n((e + 1 : U32)), n(to)), U.is_le_to_nat((e + 1 : U32), to)) : {_ == True{} : Bool}
  %Equal.sym(Nat, n((e + 1 : U32)), Nat.add(n(e), 1n), W.inc_n(len, t, d, e, hok, hl)) : {Nat.is_le(_, n(to)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n(e), 1n), 1n+n(e), N.add_one(n(e))) : {Nat.is_le(_, n(to)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+n(e), n(to)), Nat.is_lt(n(e), n(to)), N.le_succ_lt(n(e), n(to))) : {_ == True{} : Bool}
  he

def go_lt(+go: Bool, +m: Nat, +e: U32, +to: U32, +hg: {U32.is_lt(e, to) == go : Bool},
  +hc: {Bool.and(go, Bool.not(Nat.is_eq(m, 0n))) == True{} : Bool}) -> {U32.is_lt(e, to) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(e, to), go, True{}, hg, N.and_true_l(go, Bool.not(Nat.is_eq(m, 0n)), hc))

law cg_eq:
  for +k: Nat
  for +more: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +e: U32
  for +to: U32
  for +sep: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {NS.cut.go(k, more, (C.BT(len, t), e), to, sep) == FC.cut.go(k, more, (C.BT(len, t), e), to, sep) : Rs()}

def cg_eq(k, more, len, t, d, e, to, sep, hok, hto, hs):
  match k more:
    case 0n _:
      {==}
    case 1n+m False{}:
      {==}
    case 1n+(+m) True{}:
      +go = U32.is_lt(e, to)
      +c = Bool.and(go, Bool.not(Nat.is_eq(m, 0n)))
      -X = NS.cut.go(m, go, NS.cut.next(c, C.BT(len, t), (e + 1 : U32), to, sep), to, sep)
      -Y = FC.cut.go(m, go, FC.cut.next(c, C.BT(len, t), (e + 1 : U32), to, sep), to, sep)
      Equal.cong(Rs(), Rs(), r => FC.cut.cons(e, r), X, Y,
        nx_go(c, m, go, len, t, d, (e + 1 : U32), to, sep, hok, hto, hs,
          hc => inc_le(len, t, d, e, to, hok, hto, go_lt(go, m, e, to, {==}, hc)),
          +e2 => cg_eq(m, go, len, t, d, e2, to, sep, hok, hto, hs)))

# cut.ends is lawful-fields' cut on a well-formed line.
law ends_eq:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +sep: U32
  for +k: Nat
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {NS.cut.ends(C.BT(len, t), from, to, sep, k) == FC.cut(C.BT(len, t), from, to, sep, k) : Rs()}

def ends_eq(len, t, d, from, to, sep, k, hok, hft, hto, hs):
  nx_go(Bool.not(Nat.is_eq(k, 0n)), k, True{}, len, t, d, from, to, sep, hok, hto, hs, hc => hft,
    +e2 => cg_eq(k, True{}, len, t, d, e2, to, sep, hok, hto, hs))

# ---------------------------------------------------------------------------
# What the cut gives
# ---------------------------------------------------------------------------

def LL() -> Data:
  List<&2, List<&2, U32>>

def Rgs() -> Data:
  List<&2, NS.Rg>

# The cut of a .. z-1 at c: its ranges (Data).
def ES(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) -> L32():
  Pair.snd(D.Bytes, L32(), FC.cut(C.BT(len, t), a, z, c, 1n+n((z - a : U32))))

def CUT(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) -> Rgs():
  NS.rgs(ES(len, t, a, z, c), a)

law cut_t:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {U32.is_le(a, z) == True{} : Bool}
  for +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {NS.cut(C.BT(len, t), NS.Rg{a, z}, c) == (C.BT(len, t), CUT(len, t, a, z, c)) : D.Bytes & Rgs()}

def cut_t(len, t, d, a, z, c, hok, haz, hz, hc):
  +k = {1n+n((z - a : U32)) : Nat}
  %Equal.sym(Rs(), NS.cut.ends(C.BT(len, t), a, z, c, k), FC.cut(C.BT(len, t), a, z, c, k), ends_eq(len, t, d, a, z, c, k, hok, haz, hz, hc)) :
    {NS.cut.k(a, _) == (C.BT(len, t), CUT(len, t, a, z, c)) : D.Bytes & Rgs()}
  %Equal.sym(Rs(), FC.cut(C.BT(len, t), a, z, c, k), (C.BT(len, t), ES(len, t, a, z, c)), FL.cut_pair(C.BT(len, t), a, z, c, k)) :
    {NS.cut.k(a, _) == (C.BT(len, t), CUT(len, t, a, z, c)) : D.Bytes & Rgs()}
  {==}

# The bytes of each range.
def SLS(+len: U32, +t: AT.Tree<U32>, rs: Rgs()) -> LL():
  match rs:
    case Nil{}:
      Nil{}
    case NS.Rg{+a, +z} <> r:
      W.SL(len, t, a, z) <> SLS(len, t, r)

# Every range lies within the line.
def ALLPV(+len: U32, rs: Rgs()) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +x <> r:
      W.PV(len, x) && ALLPV(len, r)

law count_le:
  for +xs: L32()
  for +c: U32
  {Nat.is_le(FD.count(xs, c), List.length(&2, U32, xs)) == True{} : Bool}

def count_le.k(+b: Bool, +k: Nat, +l: Nat, +h: {Nat.is_le(k, l) == True{} : Bool}) -> {Nat.is_le(FD.count.if(b, k), 1n+l) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      N.le_trans(k, l, 1n+l, h, N.le_trans(l, Nat.add(l, 1n), 1n+l, N.le_add_r(l, 1n), {%N.add_one(l) : {Nat.is_le(Nat.add(l, 1n), _) == True{} : Bool}; N.le_refl(Nat.add(l, 1n)) : {Nat.is_le(Nat.add(l, 1n), 1n+l) == True{} : Bool}}))

def count_le(xs, c):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      count_le.k(U32.is_eq(x, c), FD.count(r, c), List.length(&2, U32, r), count_le(r, c))

law take_all:
  for +ps: LL()
  for +k: Nat
  for +h: {Nat.is_le(List.length(&2, List<&2, U32>, ps), k) == True{} : Bool}
  {List.take(&2, List<&2, U32>, ps, k) == ps : LL()}

def take_all(ps, k, h):
  match ps k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case Con{+p, +r} 0n:
      Empty.absurd({List.take(&2, List<&2, U32>, Con{p, r}, 0n) == Con{p, r} : LL()}, P.false_ne_true(h))
    case Con{+p, +r} 1n+q:
      %take_all(r, q, h) : {Con{p, List.take(&2, List<&2, U32>, r, q)} == Con{p, _} : LL()}
      {==}

def Ns() -> Data:
  List<&2, Nat>

def hd0(l: Ns()) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{h, r}:
      h

def tl0(l: Ns()) -> Ns():
  match l:
    case Nil{}:
      Nil{}
    case Con{h, r}:
      r

def isnil(l: Ns()) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{h, r}:
      False{}

def u2lt(+x: U32, +y: U32, +h: {Nat.is_lt(n(x), n(y)) == True{} : Bool}) -> {U32.is_lt(x, y) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(x, y), Nat.is_lt(n(x), n(y)), True{}, U.is_lt_to_nat(x, y), h)

def wf_hd(+e: U32, +r: L32(), +f: Nat, +z: Nat, +h: {FD.within(Con{e, r}, f, z) == True{} : Bool}) -> {Nat.is_le(n(e), z) == True{} : Bool}:
  N.and_true_r(Nat.is_le(f, n(e)), Nat.is_le(n(e), z), N.and_true_l(Bool.and(Nat.is_le(f, n(e)), Nat.is_le(n(e), z)), FD.within(r, f, z), h))

def wf_tl(+e: U32, +r: L32(), +f: Nat, +z: Nat, +h: {FD.within(Con{e, r}, f, z) == True{} : Bool}) -> {FD.within(r, f, z) == True{} : Bool}:
  N.and_true_r(Bool.and(Nat.is_le(f, n(e)), Nat.is_le(n(e), z)), FD.within(r, f, z), h)

def rp.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +r: L32(), +pt: LL(), +a: U32, +l: Nat, +f: Nat, +z: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hw: {FD.within(Con{e, r}, f, n(z)) == True{} : Bool},
  +h1: {n(e) == Nat.add(n(a), l) : Nat},
  +h2: {FD.nats(r) == FD.ends(pt, Nat.add(Nat.add(n(a), l), 1n)) : Ns()},
  ih: @+a2: U32 -> {FD.nats(r) == FD.ends(pt, n(a2)) : Ns()} -> {SLS(len, t, NS.rgs(r, a2)) == FD.pieces(r, W.V(len, t), n(a2)) : LL()}) ->
  {SLS(len, t, NS.rgs(Con{e, r}, a)) == FD.pieces(Con{e, r}, W.V(len, t), n(a)) : LL()}:
  +hel = u2lt(e, len, N.le_lt_trans(n(e), n(z), n(len), wf_hd(e, r, f, n(z), hw), hz))
  +e1 = W.inc_n(len, t, d, e, hok, hel)
  +hae = {%Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {Nat.is_le(n(a), _) == True{} : Bool}; N.le_add_r(n(a), l) : {Nat.is_le(n(a), n(e)) == True{} : Bool}}
  +h3 = {%Equal.sym(Nat, n((e + 1 : U32)), Nat.add(n(e), 1n), e1) : {FD.nats(r) == FD.ends(pt, _) : Ns()};
    %Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {FD.nats(r) == FD.ends(pt, Nat.add(_, 1n)) : Ns()};
    h2 : {FD.nats(r) == FD.ends(pt, n((e + 1 : U32))) : Ns()}}
  %Equal.sym(Nat, n((e - a : U32)), Nat.sub(n(e), n(a)), W.nsub(a, e, hae)) :
    {D.slice(W.V(len, t), n(a), _) <> SLS(len, t, NS.rgs(r, (e + 1 : U32))) == FD.pieces(Con{e, r}, W.V(len, t), n(a)) : LL()}
  %e1 : {D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) <> SLS(len, t, NS.rgs(r, (e + 1 : U32))) == D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) <> FD.pieces(r, W.V(len, t), _) : LL()}
  %Equal.sym(LL(), SLS(len, t, NS.rgs(r, (e + 1 : U32))), FD.pieces(r, W.V(len, t), n((e + 1 : U32))), ih((e + 1 : U32), h3)) : {D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) <> _ == D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) <> FD.pieces(r, W.V(len, t), n((e + 1 : U32))) : LL()}
  {==}

law rg_pieces:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +es: L32()
  for +ps: LL()
  for +a: U32
  for +f: Nat
  for +z: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hw: {FD.within(es, f, n(z)) == True{} : Bool}
  for +he: {FD.nats(es) == FD.ends(ps, n(a)) : Ns()}
  {SLS(len, t, NS.rgs(es, a)) == FD.pieces(es, W.V(len, t), n(a)) : LL()}

def rg_pieces(len, t, d, es, ps, a, f, z, hok, hz, hw, he):
  match es ps:
    case Nil{} _:
      {==}
    case Con{+e, +r} Nil{}:
      Empty.absurd({SLS(len, t, NS.rgs(Con{e, r}, a)) == FD.pieces(Con{e, r}, W.V(len, t), n(a)) : LL()},
        P.false_ne_true(Equal.cong(Ns(), Bool, isnil, FD.nats(Con{e, r}), Nil{}, he)))
    case Con{+e, +r} Con{+p, +pt}:
      +l = List.length(&2, U32, p)
      rp.k(len, t, d, e, r, pt, a, l, f, z, hok, hz, hw,
        Equal.cong(Ns(), Nat, hd0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        Equal.cong(Ns(), Ns(), tl0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        +a2 => h => rg_pieces(len, t, d, r, pt, a2, f, z, hok, hz, wf_tl(e, r, f, n(z), hw), h))

def rpv.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e: U32, +r: L32(), +pt: LL(), +a: U32, +l: Nat, +f: Nat, +z: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hw: {FD.within(Con{e, r}, f, n(z)) == True{} : Bool},
  +h1: {n(e) == Nat.add(n(a), l) : Nat},
  +h2: {FD.nats(r) == FD.ends(pt, Nat.add(Nat.add(n(a), l), 1n)) : Ns()},
  ih: @+a2: U32 -> {FD.nats(r) == FD.ends(pt, n(a2)) : Ns()} -> {ALLPV(len, NS.rgs(r, a2)) == True{} : Bool}) ->
  {ALLPV(len, NS.rgs(Con{e, r}, a)) == True{} : Bool}:
  +hle = N.lt_to_le(n(e), n(len), N.le_lt_trans(n(e), n(z), n(len), wf_hd(e, r, f, n(z), hw), hz))
  +hel = u2lt(e, len, N.le_lt_trans(n(e), n(z), n(len), wf_hd(e, r, f, n(z), hw), hz))
  +e1 = W.inc_n(len, t, d, e, hok, hel)
  +hae = {%Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {Nat.is_le(n(a), _) == True{} : Bool}; N.le_add_r(n(a), l) : {Nat.is_le(n(a), n(e)) == True{} : Bool}}
  +h3 = {%Equal.sym(Nat, n((e + 1 : U32)), Nat.add(n(e), 1n), e1) : {FD.nats(r) == FD.ends(pt, _) : Ns()};
    %Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {FD.nats(r) == FD.ends(pt, Nat.add(_, 1n)) : Ns()};
    h2 : {FD.nats(r) == FD.ends(pt, n((e + 1 : U32))) : Ns()}}
  %Equal.sym(Bool, W.PV(len, NS.Rg{a, e}), True{}, W.pv_mk(len, a, e, hae, hle)) : {Bool.and(_, ALLPV(len, NS.rgs(r, (e + 1 : U32)))) == True{} : Bool}
  ih((e + 1 : U32), h3)

law rg_pv:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +es: L32()
  for +ps: LL()
  for +a: U32
  for +f: Nat
  for +z: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hw: {FD.within(es, f, n(z)) == True{} : Bool}
  for +he: {FD.nats(es) == FD.ends(ps, n(a)) : Ns()}
  {ALLPV(len, NS.rgs(es, a)) == True{} : Bool}

def rg_pv(len, t, d, es, ps, a, f, z, hok, hz, hw, he):
  match es ps:
    case Nil{} _:
      {==}
    case Con{+e, +r} Nil{}:
      Empty.absurd({ALLPV(len, NS.rgs(Con{e, r}, a)) == True{} : Bool},
        P.false_ne_true(Equal.cong(Ns(), Bool, isnil, FD.nats(Con{e, r}), Nil{}, he)))
    case Con{+e, +r} Con{+p, +pt}:
      +l = List.length(&2, U32, p)
      rpv.k(len, t, d, e, r, pt, a, l, f, z, hok, hz, hw,
        Equal.cong(Ns(), Nat, hd0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        Equal.cong(Ns(), Ns(), tl0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        +a2 => h => rg_pv(len, t, d, r, pt, a2, f, z, hok, hz, wf_tl(e, r, f, n(z), hw), h))

law ends_len:
  for +ps: LL()
  for +f: Nat
  {List.length(&2, Nat, FD.ends(ps, f)) == List.length(&2, List<&2, U32>, ps) : Nat}

def ends_len(ps, f):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %ends_len(r, Nat.add(Nat.add(f, List.length(&2, U32, p)), 1n)) : {1n+List.length(&2, Nat, FD.ends(r, Nat.add(Nat.add(f, List.length(&2, U32, p)), 1n))) == 1n+_ : Nat}
      {==}

law take_alln:
  for +ns: Ns()
  for +k: Nat
  for +h: {Nat.is_le(List.length(&2, Nat, ns), k) == True{} : Bool}
  {List.take(&2, Nat, ns, k) == ns : Ns()}

def take_alln(ns, k, h):
  match ns k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case Con{+p, +r} 0n:
      Empty.absurd({List.take(&2, Nat, Con{p, r}, 0n) == Con{p, r} : Ns()}, P.false_ne_true(h))
    case Con{+p, +r} 1n+q:
      %take_alln(r, q, h) : {Con{p, List.take(&2, Nat, r, q)} == Con{p, _} : Ns()}
      {==}

# The split of bytes a .. z-1 at c, as byte lists.
def SP(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32) -> LL():
  FD.split(D.slice(W.V(len, t), n(a), Nat.sub(n(z), n(a))), c)

def KK(+a: U32, +z: U32) -> Nat:
  1n+n((z - a : U32))

def sp_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {Nat.is_le(List.length(&2, List<&2, U32>, SP(len, t, a, z, c)), KK(a, z)) == True{} : Bool}:
  +xs = D.slice(W.V(len, t), n(a), Nat.sub(n(z), n(a)))
  +k = Nat.sub(n(z), n(a))
  +hsum = {%Equal.sym(Nat, Nat.add(n(a), Nat.sub(n(z), n(a))), n(z), N.le_sub_add(n(a), n(z), haz)) : {Nat.is_le(_, List.length(&2, U32, W.V(len, t))) == True{} : Bool};
    %Equal.sym(Nat, List.length(&2, U32, W.V(len, t)), n(len), O.view_size_t(len, t, d, hok)) : {Nat.is_le(n(z), _) == True{} : Bool};
    hz : {Nat.is_le(Nat.add(n(a), k), List.length(&2, U32, W.V(len, t))) == True{} : Bool}}
  +hxl = LP.slice_len(W.V(len, t), n(a), k, hsum)
  +hc1 = {%hxl : {Nat.is_le(FD.count(xs, c), _) == True{} : Bool}; count_le(xs, c) : {Nat.is_le(FD.count(xs, c), k) == True{} : Bool}}
  %Equal.sym(Nat, List.length(&2, List<&2, U32>, FD.split(xs, c)), Nat.add(FD.count(xs, c), 1n), FL.split_length(xs, c)) : {Nat.is_le(_, KK(a, z)) == True{} : Bool}
  %Equal.sym(Nat, n((z - a : U32)), k, W.nsub(a, z, haz)) : {Nat.is_le(Nat.add(FD.count(xs, c), 1n), 1n+_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(FD.count(xs, c), 1n), 1n+FD.count(xs, c), N.add_one(FD.count(xs, c))) : {Nat.is_le(_, 1n+k) == True{} : Bool}
  hc1

def ends_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {U32.is_le(a, z) == True{} : Bool},
  +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {FD.nats(ES(len, t, a, z, c)) == FD.ends(SP(len, t, a, z, c), n(a)) : Ns()}:
  +hn = Equal.trans(Bool, Nat.is_le(n(a), n(z)), U32.is_le(a, z), True{}, Equal.sym(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), U.is_le_to_nat(a, z)), haz)
  +E = FD.ends(SP(len, t, a, z, c), n(a))
  +hl = {%Equal.sym(Nat, List.length(&2, Nat, E), List.length(&2, List<&2, U32>, SP(len, t, a, z, c)), ends_len(SP(len, t, a, z, c), n(a))) : {Nat.is_le(_, KK(a, z)) == True{} : Bool}; sp_len(len, t, d, a, z, c, hok, hn, hz) : {Nat.is_le(List.length(&2, Nat, E), KK(a, z)) == True{} : Bool}}
  Equal.trans(Ns(), FD.nats(ES(len, t, a, z, c)), List.take(&2, Nat, E, KK(a, z)), E,
    FL.cut_ends(C.BT(len, t), d, a, z, c, KK(a, z), hok, haz, hz, hc), take_alln(E, KK(a, z), hl))

def within_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +haz: {U32.is_le(a, z) == True{} : Bool},
  +hz: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {FD.within(ES(len, t, a, z, c), n(a), n(z)) == True{} : Bool}:
  FL.cut_bounds(C.BT(len, t), d, a, z, c, KK(a, z), hok, haz, hz, hc)

# The cut's ranges hold the pieces of a .. z-1 split at c.
law cut_sls:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {U32.is_le(a, z) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {SLS(len, t, CUT(len, t, a, z, c)) == SP(len, t, a, z, c) : LL()}

def cut_sls(len, t, d, a, z, c, hok, haz, hz, hc):
  +hzl = N.lt_to_le(n(z), n(len), hz)
  +hn = Equal.trans(Bool, Nat.is_le(n(a), n(z)), U32.is_le(a, z), True{}, Equal.sym(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), U.is_le_to_nat(a, z)), haz)
  +es = ES(len, t, a, z, c)
  +sp = SP(len, t, a, z, c)
  Equal.trans(LL(), SLS(len, t, NS.rgs(es, a)), FD.pieces(es, W.V(len, t), n(a)), sp,
    rg_pieces(len, t, d, es, sp, a, n(a), z, hok, hz, within_t(len, t, d, a, z, c, hok, haz, hzl, hc), ends_t(len, t, d, a, z, c, hok, haz, hzl, hc)),
    Equal.trans(LL(), FD.pieces(es, W.V(len, t), n(a)), List.take(&2, List<&2, U32>, sp, KK(a, z)), sp,
      FL.cut_view(C.BT(len, t), d, a, z, c, KK(a, z), hok, haz, hzl, hc), take_all(sp, KK(a, z), sp_len(len, t, d, a, z, c, hok, hn, hzl))))

# Every range of the cut lies within the line.
law cut_pv:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {U32.is_le(a, z) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {ALLPV(len, CUT(len, t, a, z, c)) == True{} : Bool}

def cut_pv(len, t, d, a, z, c, hok, haz, hz, hc):
  +hzl = N.lt_to_le(n(z), n(len), hz)
  rg_pv(len, t, d, ES(len, t, a, z, c), SP(len, t, a, z, c), a, n(a), z, hok, hz, within_t(len, t, d, a, z, c, hok, haz, hzl, hc), ends_t(len, t, d, a, z, c, hok, haz, hzl, hc))

# ---------------------------------------------------------------------------
# The cut as text
# ---------------------------------------------------------------------------

def Ss() -> Data:
  List<&2, String>

# The text of each range.
def TXS(+len: U32, +t: AT.Tree<U32>, rs: Rgs()) -> Ss():
  match rs:
    case Nil{}:
      Nil{}
    case +x <> r:
      WT.TX(len, t, x) <> TXS(len, t, r)

def CHS(ps: LL()) -> Ss():
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      NR.chars(p) <> CHS(r)

law text_chars:
  for +xs: L32()
  {FD.text(xs) == NR.chars(xs) : String}

def text_chars(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %text_chars(r) : {SCon{Chr{x}, FD.text(r)} == SCon{Chr{x}, _} : String}
      {==}

law texts_chs:
  for +ps: LL()
  {FD.texts(ps) == CHS(ps) : Ss()}

def texts_chs(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %text_chars(p) : {Con{FD.text(p), FD.texts(r)} == Con{_, CHS(r)} : Ss()}
      %texts_chs(r) : {Con{FD.text(p), FD.texts(r)} == Con{FD.text(p), _} : Ss()}
      {==}

law txs_sls:
  for +len: U32
  for +t: AT.Tree<U32>
  for +rs: Rgs()
  {TXS(len, t, rs) == CHS(SLS(len, t, rs)) : Ss()}

def txs_sls(len, t, rs):
  match rs:
    case Nil{}:
      {==}
    case Con{NS.Rg{+a, +z}, +r}:
      %txs_sls(len, t, r) : {Con{WT.TX(len, t, NS.Rg{a, z}), TXS(len, t, r)} == Con{WT.TX(len, t, NS.Rg{a, z}), _} : Ss()}
      {==}

# The texts of the cut's ranges are the pieces of the range's text split at c.
law cut_tx:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {U32.is_le(a, z) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {TXS(len, t, CUT(len, t, a, z, c)) == String.split(WT.TX(len, t, NS.Rg{a, z}), Chr{c}) : Ss()}

def cut_tx(len, t, d, a, z, c, hok, haz, hz, hc):
  +hn = Equal.trans(Bool, Nat.is_le(n(a), n(z)), U32.is_le(a, z), True{}, Equal.sym(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), U.is_le_to_nat(a, z)), haz)
  +xs = D.slice(W.V(len, t), n(a), Nat.sub(n(z), n(a)))
  %Equal.sym(Ss(), TXS(len, t, CUT(len, t, a, z, c)), CHS(SLS(len, t, CUT(len, t, a, z, c))), txs_sls(len, t, CUT(len, t, a, z, c))) : {_ == String.split(WT.TX(len, t, NS.Rg{a, z}), Chr{c}) : Ss()}
  %Equal.sym(LL(), SLS(len, t, CUT(len, t, a, z, c)), SP(len, t, a, z, c), cut_sls(len, t, d, a, z, c, hok, haz, hz, hc)) :
    {CHS(_) == String.split(WT.TX(len, t, NS.Rg{a, z}), Chr{c}) : Ss()}
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), W.nsub(a, z, hn)) :
    {CHS(SP(len, t, a, z, c)) == String.split(NR.chars(D.slice(W.V(len, t), n(a), _)), Chr{c}) : Ss()}
  %texts_chs(FD.split(xs, c)) : {_ == String.split(NR.chars(xs), Chr{c}) : Ss()}
  %text_chars(xs) : {FD.texts(FD.split(xs, c)) == String.split(_, Chr{c}) : Ss()}
  Equal.sym(Ss(), String.split(FD.text(xs), Chr{c}), FD.texts(FD.split(xs, c)), FL.split_text(xs, c))

# The same, each range within a .. z (its own bound).
def rpvb.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bb: U32, +e: U32, +r: L32(), +pt: LL(), +a: U32, +l: Nat, +f: Nat, +z: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +hzb: {Nat.is_le(n(z), n(bb)) == True{} : Bool},
  +hw: {FD.within(Con{e, r}, f, n(z)) == True{} : Bool},
  +h1: {n(e) == Nat.add(n(a), l) : Nat},
  +h2: {FD.nats(r) == FD.ends(pt, Nat.add(Nat.add(n(a), l), 1n)) : Ns()},
  ih: @+a2: U32 -> {FD.nats(r) == FD.ends(pt, n(a2)) : Ns()} -> {ALLPV(bb, NS.rgs(r, a2)) == True{} : Bool}) ->
  {ALLPV(bb, NS.rgs(Con{e, r}, a)) == True{} : Bool}:
  +hle = N.le_trans(n(e), n(z), n(bb), wf_hd(e, r, f, n(z), hw), hzb)
  +hel = u2lt(e, len, N.le_lt_trans(n(e), n(z), n(len), wf_hd(e, r, f, n(z), hw), hz))
  +e1 = W.inc_n(len, t, d, e, hok, hel)
  +hae = {%Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {Nat.is_le(n(a), _) == True{} : Bool}; N.le_add_r(n(a), l) : {Nat.is_le(n(a), n(e)) == True{} : Bool}}
  +h3 = {%Equal.sym(Nat, n((e + 1 : U32)), Nat.add(n(e), 1n), e1) : {FD.nats(r) == FD.ends(pt, _) : Ns()};
    %Equal.sym(Nat, n(e), Nat.add(n(a), l), h1) : {FD.nats(r) == FD.ends(pt, Nat.add(_, 1n)) : Ns()};
    h2 : {FD.nats(r) == FD.ends(pt, n((e + 1 : U32))) : Ns()}}
  %Equal.sym(Bool, W.PV(bb, NS.Rg{a, e}), True{}, W.pv_mk(bb, a, e, hae, hle)) : {Bool.and(_, ALLPV(bb, NS.rgs(r, (e + 1 : U32)))) == True{} : Bool}
  ih((e + 1 : U32), h3)

law rg_pvb:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +bb: U32
  for +es: L32()
  for +ps: LL()
  for +a: U32
  for +f: Nat
  for +z: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hzb: {Nat.is_le(n(z), n(bb)) == True{} : Bool}
  for +hw: {FD.within(es, f, n(z)) == True{} : Bool}
  for +he: {FD.nats(es) == FD.ends(ps, n(a)) : Ns()}
  {ALLPV(bb, NS.rgs(es, a)) == True{} : Bool}

def rg_pvb(len, t, d, bb, es, ps, a, f, z, hok, hz, hzb, hw, he):
  match es ps:
    case Nil{} _:
      {==}
    case Con{+e, +r} Nil{}:
      Empty.absurd({ALLPV(bb, NS.rgs(Con{e, r}, a)) == True{} : Bool},
        P.false_ne_true(Equal.cong(Ns(), Bool, isnil, FD.nats(Con{e, r}), Nil{}, he)))
    case Con{+e, +r} Con{+p, +pt}:
      +l = List.length(&2, U32, p)
      rpvb.k(len, t, d, bb, e, r, pt, a, l, f, z, hok, hz, hzb, hw,
        Equal.cong(Ns(), Nat, hd0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        Equal.cong(Ns(), Ns(), tl0, FD.nats(Con{e, r}), FD.ends(Con{p, pt}, n(a)), he),
        +a2 => h => rg_pvb(len, t, d, bb, r, pt, a2, f, z, hok, hz, hzb, wf_tl(e, r, f, n(z), hw), h))


law cut_pvz:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +a: U32
  for +z: U32
  for +c: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +haz: {U32.is_le(a, z) == True{} : Bool}
  for +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {ALLPV(z, CUT(len, t, a, z, c)) == True{} : Bool}

def cut_pvz(len, t, d, a, z, c, hok, haz, hz, hc):
  +hzl = N.lt_to_le(n(z), n(len), hz)
  rg_pvb(len, t, d, z, ES(len, t, a, z, c), SP(len, t, a, z, c), a, n(a), z, hok, hz, N.le_refl(n(z)), within_t(len, t, d, a, z, c, hok, haz, hzl, hc), ends_t(len, t, d, a, z, c, hok, haz, hzl, hc))
