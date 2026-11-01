import Base
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_run_buf.bend as BF
import ./proof_b_adv_nat.bend as LP
import ./proof_b_alleles_list.bend as LS
import ./proof_s_w.bend as W
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# What the byte splitter's writer has written, on its model (proof_s_w.bend's
# Wm): the records so far, then the line's bytes not copied yet. Each write
# that leaves the flag set adds its piece to that text, keeps the range not
# copied within the line, and was made from a state with the flag set. Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

# The text of bytes a .. z-1 of the line.
def TX(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg) -> String:
  match x:
    case NS.Rg{+a, +z}:
      NR.chars(W.SL(len, t, a, z))

def T(+len: U32, +t: AT.Tree<U32>, +m: W.Wm) -> String:
  match m:
    case W.Wm{+out, +p, +ok}:
      String.append(NR.chars(out), TX(len, t, p))

def Out(+m: W.Wm) -> String:
  match m:
    case W.Wm{+out, +p, +ok}:
      NR.chars(out)

def Pm(+m: W.Wm) -> NS.Rg:
  match m:
    case W.Wm{+out, +p, +ok}:
      p

# ---------------------------------------------------------------------------
# Slices of the line
# ---------------------------------------------------------------------------

def sl_zz(+len: U32, +t: AT.Tree<U32>, +z: U32) -> {W.SL(len, t, z, z) == Nil{} : L32()}:
  %Equal.sym(Nat, n((z - z : U32)), 0n, Equal.trans(Nat, n((z - z : U32)), Nat.sub(n(z), n(z)), 0n, W.nsub(z, z, N.le_refl(n(z))), LS.sub_self(n(z)))) :
    {D.slice(W.V(len, t), n(z), _) == Nil{} : L32()}
  Q.take_zero(List.drop(&2, U32, W.V(len, t), n(z)))

# a .. e is a .. z then z .. e.
def sl_app(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +e: U32,
  +ha: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(e)) == True{} : Bool}) ->
  {W.SL(len, t, a, e) == List.append(&2, U32, W.SL(len, t, a, z), W.SL(len, t, z, e)) : L32()}:
  +hae = N.le_trans(n(a), n(z), n(e), ha, hz)
  %Equal.sym(Nat, n((e - a : U32)), Nat.sub(n(e), n(a)), W.nsub(a, e, hae)) :
    {D.slice(W.V(len, t), n(a), _) == List.append(&2, U32, W.SL(len, t, a, z), W.SL(len, t, z, e)) : L32()}
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), W.nsub(a, z, ha)) :
    {D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) == List.append(&2, U32, D.slice(W.V(len, t), n(a), _), W.SL(len, t, z, e)) : L32()}
  %Equal.sym(Nat, n((e - z : U32)), Nat.sub(n(e), n(z)), W.nsub(z, e, hz)) :
    {D.slice(W.V(len, t), n(a), Nat.sub(n(e), n(a))) == List.append(&2, U32, D.slice(W.V(len, t), n(a), Nat.sub(n(z), n(a))), D.slice(W.V(len, t), n(z), _)) : L32()}
  LS.slice_app(W.V(len, t), n(a), n(z), n(e), ha, hz)

def tx_app(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +e: U32,
  +ha: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(e)) == True{} : Bool}) ->
  {NR.chars(W.SL(len, t, a, e)) == String.append(NR.chars(W.SL(len, t, a, z)), NR.chars(W.SL(len, t, z, e))) : String}:
  %Equal.sym(L32(), W.SL(len, t, a, e), List.append(&2, U32, W.SL(len, t, a, z), W.SL(len, t, z, e)), sl_app(len, t, a, z, e, ha, hz)) : {NR.chars(_) == String.append(NR.chars(W.SL(len, t, a, z)), NR.chars(W.SL(len, t, z, e))) : String}
  BF.chars_app(W.SL(len, t, a, z), W.SL(len, t, z, e))

# Byte z (below len) alone.
def sl_one(+len: U32, +t: AT.Tree<U32>, +d: Nat, +z: U32, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +h: {U32.is_lt(z, len) == True{} : Bool}) ->
  {W.SL(len, t, z, (z + 1 : U32)) == [C.AT(len, t, z)] : L32()}:
  +hz = Equal.trans(Bool, Nat.is_lt(n(z), n(len)), U32.is_lt(z, len), True{}, Equal.sym(Bool, U32.is_lt(z, len), Nat.is_lt(n(z), n(len)), U.is_lt_to_nat(z, len)), h)
  +e1 = W.inc_n(len, t, d, z, hl, h)
  +hle = {%Equal.sym(Nat, n((z + 1 : U32)), Nat.add(n(z), 1n), e1) : {Nat.is_le(n(z), _) == True{} : Bool}; N.le_add_r(n(z), 1n) : {Nat.is_le(n(z), n((z + 1 : U32))) == True{} : Bool}}
  +hg = Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, z)}, List.get(&2, U32, W.V(len, t), n(z)),
    C.at_view_t(len, t, d, z, C.ok_full(len, t, d, hl), C.ok_d(len, t, d, hl), C.ok_len(len, t, d, hl), hz))
  +hlt = {%N.le_succ_lt(n(z), Nat.add(n(z), 1n)) : {_ == True{} : Bool};
    %Equal.sym(Nat, Nat.add(n(z), 1n), 1n+n(z), N.add_one(n(z))) : {Nat.is_le(1n+n(z), _) == True{} : Bool};
    N.le_refl(1n+n(z)) : {Nat.is_lt(n(z), Nat.add(n(z), 1n)) == True{} : Bool}}
  %Equal.sym(Nat, n(((z + 1 : U32) - z : U32)), Nat.sub(n((z + 1 : U32)), n(z)), W.nsub(z, (z + 1 : U32), hle)) :
    {D.slice(W.V(len, t), n(z), _) == [C.AT(len, t, z)] : L32()}
  %Equal.sym(Nat, n((z + 1 : U32)), Nat.add(n(z), 1n), e1) :
    {D.slice(W.V(len, t), n(z), Nat.sub(_, n(z))) == [C.AT(len, t, z)] : L32()}
  %Equal.sym(L32(), D.slice(W.V(len, t), n(z), Nat.sub(Nat.add(n(z), 1n), n(z))), C.AT(len, t, z) <> D.slice(W.V(len, t), Nat.add(n(z), 1n), Nat.sub(Nat.add(n(z), 1n), Nat.add(n(z), 1n))),
    LS.slice_lt(W.V(len, t), n(z), Nat.add(n(z), 1n), C.AT(len, t, z), hlt, hg)) :
    {_ == [C.AT(len, t, z)] : L32()}
  %Equal.sym(Nat, Nat.sub(Nat.add(n(z), 1n), Nat.add(n(z), 1n)), 0n, LS.sub_self(Nat.add(n(z), 1n))) :
    {C.AT(len, t, z) <> D.slice(W.V(len, t), Nat.add(n(z), 1n), _) == [C.AT(len, t, z)] : L32()}
  %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, W.V(len, t), Nat.add(n(z), 1n)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, W.V(len, t), Nat.add(n(z), 1n)))) :
    {C.AT(len, t, z) <> _ == [C.AT(len, t, z)] : L32()}
  {==}

# x <= y gives x - y == 0.
law sub_le0:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.sub(x, y) == 0n : Nat}

def sub_le0(x, y, h):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, P.false_ne_true(h))
    case 1n+p 1n+q:
      sub_le0(p, q, h)

def tx_nil(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32,
  +ha: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hz: {Nat.is_le(n(z), n(a)) == True{} : Bool}) ->
  {NR.chars(W.SL(len, t, a, z)) == "" : String}:
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), W.nsub(a, z, ha)) : {NR.chars(D.slice(W.V(len, t), n(a), _)) == "" : String}
  %Equal.sym(Nat, Nat.sub(n(z), n(a)), 0n, sub_le0(n(z), n(a), hz)) : {NR.chars(D.slice(W.V(len, t), n(a), _)) == "" : String}
  %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, W.V(len, t), n(a)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, W.V(len, t), n(a)))) : {NR.chars(_) == "" : String}
  {==}

# ---------------------------------------------------------------------------
# A write that leaves the flag set was made from a state with it set
# ---------------------------------------------------------------------------

def ff(-A: Type, +h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, P.false_ne_true(h))

def fl_mono(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +h: {W.Wm.ok(W.Wm.flush(len, t, m)) == True{} : Bool}) -> {W.Wm.ok(m) == True{} : Bool}:
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      {==}
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff({False{} == True{} : Bool}, h)

def push_mono(+m: W.Wm, +x: U32, +h: {W.Wm.ok(W.Wm.push(m, x)) == True{} : Bool}) -> {W.Wm.ok(m) == True{} : Bool}:
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      {==}
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff({False{} == True{} : Bool}, h)

def cpr_mono(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: NS.Rg, +h: {W.Wm.ok(W.Wm.cpr(len, t, m, x)) == True{} : Bool}) -> {W.Wm.ok(m) == True{} : Bool}:
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      {==}
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff({False{} == True{} : Bool}, h)

def ch_mono(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: U32, +h: {W.Wm.ok(W.Wm.ch(len, t, m, x)) == True{} : Bool}) -> {W.Wm.ok(m) == True{} : Bool}:
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      {==}
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff({False{} == True{} : Bool}, h)

def sep_mono(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +first: Bool, +x: U32, +h: {W.Wm.ok(W.Wm.sep(len, t, m, first, x)) == True{} : Bool}) -> {W.Wm.ok(m) == True{} : Bool}:
  match first:
    case True{}:
      h
    case False{}:
      ch_mono(len, t, m, x, h)

def fail_f(-A: Type, +m: W.Wm, +h: {W.Wm.ok(W.Wm.fail(m)) == True{} : Bool}) -> A:
  match m:
    case W.Wm{+out, +p, +ok}:
      ff(A, h)

# ---------------------------------------------------------------------------
# What each write adds
# ---------------------------------------------------------------------------

# flush: the records hold the text so far, nothing is left pending, the range
# stays within the line.
def FLX(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm) -> Type:
  {Out(m1) == T(len, t, m0) : String} & ({T(len, t, m1) == Out(m1) : String} & {W.PV(len, Pm(m1)) == True{} : Bool})

def tzz(+len: U32, +t: AT.Tree<U32>, +s: String, +z: U32) -> {String.append(s, NR.chars(W.SL(len, t, z, z))) == s : String}:
  %Equal.sym(L32(), W.SL(len, t, z, z), Nil{}, sl_zz(len, t, z)) : {String.append(s, NR.chars(_)) == s : String}
  MN.str_nil(s)

def fl.ok(+c: Bool, +len: U32, +t: AT.Tree<U32>, +out: L32(), +a: U32, +z: U32,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.flush.ok(c, len, t, out, a, z)) == True{} : Bool}) ->
  FLX(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.flush.ok(c, len, t, out, a, z)):
  match c:
    case True{}:
      +o = NR.chars(List.append(&2, U32, out, W.SL(len, t, a, z)))
      (BF.chars_app(out, W.SL(len, t, a, z)), (tzz(len, t, o, z), W.pv_zz(len, a, z, hp)))
    case False{}:
      ff(FLX(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm{out, NS.Rg{a, z}, False{}}), h)

def fl.if(+c: Bool, +len: U32, +t: AT.Tree<U32>, +out: L32(), +a: U32, +z: U32,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hc: {U32.is_le(z, a) == c : Bool},
  +h: {W.Wm.ok(W.Wm.flush.if(c, len, t, out, a, z)) == True{} : Bool}) ->
  FLX(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.flush.if(c, len, t, out, a, z)):
  match c:
    case True{}:
      +hz = Equal.trans(Bool, Nat.is_le(n(z), n(a)), U32.is_le(z, a), True{}, Equal.sym(Bool, U32.is_le(z, a), Nat.is_le(n(z), n(a)), U.is_le_to_nat(z, a)), hc)
      +e = tx_nil(len, t, a, z, W.pv_a(len, a, z, hp), hz)
      +o = NR.chars(out)
      +p1 = {%Equal.sym(String, NR.chars(W.SL(len, t, a, z)), "", e) : {o == String.append(o, _) : String};
        Equal.sym(String, String.append(o, ""), o, MN.str_nil(o)) : {o == String.append(o, NR.chars(W.SL(len, t, a, z))) : String}}
      +p2 = {%Equal.sym(String, NR.chars(W.SL(len, t, a, z)), "", e) : {String.append(o, _) == o : String};
        MN.str_nil(o) : {String.append(o, NR.chars(W.SL(len, t, a, z))) == o : String}}
      (p1, (p2, hp))
    case False{}:
      fl.ok(Bool.and(U32.is_le(W.LN(out), 536870912), U32.is_le((z - a : U32), 268435456)), len, t, out, a, z, hp, h)

def fl_m(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.flush(len, t, m)) == True{} : Bool}) ->
  FLX(len, t, m, W.Wm.flush(len, t, m)):
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      fl.if(U32.is_le(z, a), len, t, out, a, z, hp, {==}, h)
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff(FLX(len, t, W.Wm{out, NS.Rg{a, z}, False{}}, W.Wm{out, NS.Rg{a, z}, False{}}), h)

def flx1(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, x: FLX(len, t, m0, m1)) -> {Out(m1) == T(len, t, m0) : String}:
  (e, r) = x
  e

def flx3(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, x: FLX(len, t, m0, m1)) -> {W.PV(len, Pm(m1)) == True{} : Bool}:
  (e, r) = x
  (e2, pv) = r
  pv

def fl_out(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.flush(len, t, m)) == True{} : Bool}) ->
  {Out(W.Wm.flush(len, t, m)) == T(len, t, m) : String}:
  flx1(len, t, m, W.Wm.flush(len, t, m), fl_m(len, t, m, hp, h))

def fl_pv(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.flush(len, t, m)) == True{} : Bool}) ->
  {W.PV(len, Pm(W.Wm.flush(len, t, m))) == True{} : Bool}:
  flx3(len, t, m, W.Wm.flush(len, t, m), fl_m(len, t, m, hp, h))

# push (after a flush: what was pending is dropped).
def PUX(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +x: U32) -> Type:
  {T(len, t, m1) == String.append(Out(m0), NR.chars([x])) : String} & {W.PV(len, Pm(m1)) == True{} : Bool}

def pu.ok(+c: Bool, +len: U32, +t: AT.Tree<U32>, +out: L32(), +a: U32, +z: U32, +x: U32,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.push.ok(c, out, z, x)) == True{} : Bool}) ->
  PUX(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.push.ok(c, out, z, x), x):
  match c:
    case True{}:
      +o = NR.chars(List.append(&2, U32, out, [x]))
      (Equal.trans(String, String.append(o, NR.chars(W.SL(len, t, z, z))), o, String.append(NR.chars(out), NR.chars([x])), tzz(len, t, o, z), BF.chars_app(out, [x])),
        W.pv_zz(len, a, z, hp))
    case False{}:
      ff(PUX(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm{out, NS.Rg{z, z}, False{}}, x), h)

def push_m(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: U32, +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.push(m, x)) == True{} : Bool}) ->
  PUX(len, t, m, W.Wm.push(m, x), x):
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      pu.ok(Bool.and(U32.is_le(W.LN(out), 536870912), U32.is_le(1, 268435456)), len, t, out, a, z, x, hp, h)
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff(PUX(len, t, W.Wm{out, NS.Rg{a, z}, False{}}, W.Wm{out, NS.Rg{a, z}, False{}}, x), h)

# A write that adds s.
def ADDS(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +s: String) -> Type:
  {T(len, t, m1) == String.append(T(len, t, m0), s) : String} & {W.PV(len, Pm(m1)) == True{} : Bool}

# ch's fallback: flush, then push x.
def ch_push.k(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: U32, +hp: {W.PV(len, Pm(m)) == True{} : Bool},
  +hf: {W.Wm.ok(W.Wm.flush(len, t, m)) == True{} : Bool},
  u: PUX(len, t, W.Wm.flush(len, t, m), W.Wm.push(W.Wm.flush(len, t, m), x), x)) ->
  ADDS(len, t, m, W.Wm.push(W.Wm.flush(len, t, m), x), NR.chars([x])):
  (tp, pv) = u
  +f = W.Wm.flush(len, t, m)
  (Equal.trans(String, T(len, t, W.Wm.push(f, x)), String.append(Out(f), NR.chars([x])), String.append(T(len, t, m), NR.chars([x])),
    tp, Equal.cong(String, String, s => String.append(s, NR.chars([x])), Out(f), T(len, t, m), fl_out(len, t, m, hp, hf))), pv)

def ch_push(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: U32, +hp: {W.PV(len, Pm(m)) == True{} : Bool},
  +h: {W.Wm.ok(W.Wm.push(W.Wm.flush(len, t, m), x)) == True{} : Bool}) ->
  ADDS(len, t, m, W.Wm.push(W.Wm.flush(len, t, m), x), NR.chars([x])):
  +f = W.Wm.flush(len, t, m)
  +hf = push_mono(f, x, h)
  ch_push.k(len, t, m, x, hp, hf, push_m(len, t, f, x, fl_pv(len, t, m, hp, hf), h))

def ch.if_m(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +out: L32(), +a: U32, +z: U32, +x: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hz: {U32.is_lt(z, len) == True{} : Bool}, +hc: {U32.is_eq(C.AT(len, t, z), x) == c : Bool},
  +h: {W.Wm.ok(W.Wm.ch.if(c, len, t, out, a, z, x)) == True{} : Bool}) ->
  ADDS(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.ch.if(c, len, t, out, a, z, x), NR.chars([x])):
  match c:
    case True{}:
      +e = U.is_eq_true(C.AT(len, t, z), x, hc)
      +o = NR.chars(out)
      +s1 = W.SL(len, t, a, z)
      +z1 = (z + 1 : U32)
      +hle = {%Equal.sym(Nat, n(z1), Nat.add(n(z), 1n), W.inc_n(len, t, d, z, hl, hz)) : {Nat.is_le(n(z), _) == True{} : Bool}; N.le_add_r(n(z), 1n) : {Nat.is_le(n(z), n(z1)) == True{} : Bool}}
      +RHS = String.append(String.append(o, NR.chars(s1)), NR.chars([x]))
      +tt = {%Equal.sym(L32(), W.SL(len, t, a, z1), List.append(&2, U32, s1, W.SL(len, t, z, z1)), sl_app(len, t, a, z, z1, W.pv_a(len, a, z, hp), hle)) :
          {String.append(o, NR.chars(_)) == RHS : String};
        %Equal.sym(L32(), W.SL(len, t, z, z1), [C.AT(len, t, z)], sl_one(len, t, d, z, hl, hz)) :
          {String.append(o, NR.chars(List.append(&2, U32, s1, _))) == RHS : String};
        %Equal.sym(U32, C.AT(len, t, z), x, e) :
          {String.append(o, NR.chars(List.append(&2, U32, s1, [_]))) == RHS : String};
        %Equal.sym(String, NR.chars(List.append(&2, U32, s1, [x])), String.append(NR.chars(s1), NR.chars([x])), BF.chars_app(s1, [x])) :
          {String.append(o, _) == RHS : String};
        Equal.sym(String, RHS, String.append(o, String.append(NR.chars(s1), NR.chars([x]))), MN.str_assoc(o, NR.chars(s1), NR.chars([x]))) :
          {String.append(o, NR.chars(W.SL(len, t, a, z1))) == RHS : String}}
      (tt, W.pv_inc(len, t, d, a, z, hl, hp, hz))
    case False{}:
      ch_push(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, x, hp, h)

def ch.in_m(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +out: L32(), +a: U32, +z: U32, +x: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hz: {U32.is_lt(z, len) == c : Bool}, +h: {W.Wm.ok(W.Wm.ch.in(c, len, t, out, a, z, x)) == True{} : Bool}) ->
  ADDS(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.ch.in(c, len, t, out, a, z, x), NR.chars([x])):
  match c:
    case True{}:
      ch.if_m(U32.is_eq(C.AT(len, t, z), x), len, t, d, hl, out, a, z, x, hp, hz, {==}, h)
    case False{}:
      ch_push(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, x, hp, h)

def ch_m(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +m: W.Wm, +x: U32,
  +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.ch(len, t, m, x)) == True{} : Bool}) ->
  ADDS(len, t, m, W.Wm.ch(len, t, m, x), NR.chars([x])):
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      ch.in_m(U32.is_lt(z, len), len, t, d, hl, out, a, z, x, hp, {==}, h)
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff(ADDS(len, t, W.Wm{out, NS.Rg{a, z}, False{}}, W.Wm{out, NS.Rg{a, z}, False{}}, NR.chars([x])), h)

def wp_t(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: NS.Rg) -> {T(len, t, W.Wm.with_p(m, x)) == String.append(Out(m), TX(len, t, x)) : String}:
  match m:
    case W.Wm{+out, +p, +ok}:
      {==}

def wp_ok(+m: W.Wm, +x: NS.Rg) -> {W.Wm.ok(W.Wm.with_p(m, x)) == W.Wm.ok(m) : Bool}:
  match m:
    case W.Wm{+out, +p, +ok}:
      {==}

def wp_pv(+len: U32, +m: W.Wm, +x: NS.Rg, +hx: {W.PV(len, x) == True{} : Bool}) -> {W.PV(len, Pm(W.Wm.with_p(m, x))) == True{} : Bool}:
  match m:
    case W.Wm{+out, +p, +ok}:
      hx

# x follows a .. z: the range grows to a .. x.z.
def cpr.join(+len: U32, +t: AT.Tree<U32>, +out: L32(), +a: U32, +z: U32, +x: NS.Rg,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hx: {W.PV(len, x) == True{} : Bool}, +hc: {U32.is_eq(NS.Rg.a(x), z) == True{} : Bool},
  +pj: {W.PV(len, NS.Rg{a, NS.Rg.z(x)}) == True{} : Bool}) ->
  ADDS(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm{out, NS.Rg{a, NS.Rg.z(x)}, True{}}, TX(len, t, x)):
  match x:
    case NS.Rg{+xa, +xz}:
      +e = U.is_eq_true(xa, z, hc)
      +o = NR.chars(out)
      +hzx = {%e : {Nat.is_le(n(_), n(xz)) == True{} : Bool}; W.pv_a(len, xa, xz, hx) : {Nat.is_le(n(z), n(xz)) == True{} : Bool}}
      +RHS = String.append(String.append(o, NR.chars(W.SL(len, t, a, z))), NR.chars(W.SL(len, t, xa, xz)))
      +tt = {%Equal.sym(U32, xa, z, e) : {String.append(o, NR.chars(W.SL(len, t, a, xz))) == String.append(String.append(o, NR.chars(W.SL(len, t, a, z))), NR.chars(W.SL(len, t, _, xz))) : String};
        %Equal.sym(String, NR.chars(W.SL(len, t, a, xz)), String.append(NR.chars(W.SL(len, t, a, z)), NR.chars(W.SL(len, t, z, xz))), tx_app(len, t, a, z, xz, W.pv_a(len, a, z, hp), hzx)) :
          {String.append(o, _) == String.append(String.append(o, NR.chars(W.SL(len, t, a, z))), NR.chars(W.SL(len, t, z, xz))) : String};
        Equal.sym(String, String.append(String.append(o, NR.chars(W.SL(len, t, a, z))), NR.chars(W.SL(len, t, z, xz))), String.append(o, String.append(NR.chars(W.SL(len, t, a, z)), NR.chars(W.SL(len, t, z, xz)))),
          MN.str_assoc(o, NR.chars(W.SL(len, t, a, z)), NR.chars(W.SL(len, t, z, xz)))) :
          {String.append(o, NR.chars(W.SL(len, t, a, xz))) == RHS : String}}
      (tt, pj)

def cpr.if_m(+c: Bool, +len: U32, +t: AT.Tree<U32>, +out: L32(), +a: U32, +z: U32, +x: NS.Rg,
  +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hx: {W.PV(len, x) == True{} : Bool}, +hc: {U32.is_eq(NS.Rg.a(x), z) == c : Bool},
  +h: {W.Wm.ok(W.Wm.cpr.if(c, len, t, W.Wm{out, NS.Rg{a, z}, True{}}, a, x)) == True{} : Bool}) ->
  ADDS(len, t, W.Wm{out, NS.Rg{a, z}, True{}}, W.Wm.cpr.if(c, len, t, W.Wm{out, NS.Rg{a, z}, True{}}, a, x), TX(len, t, x)):
  match c:
    case True{}:
      +pj = W.pv_join(len, a, z, x, hp, hx, hc)
      cpr.join(len, t, out, a, z, x, hp, hx, hc, pj)
    case False{}:
      +m0 = {W.Wm{out, NS.Rg{a, z}, True{}} : W.Wm}
      +f = W.Wm.flush(len, t, m0)
      +hf = Equal.trans(Bool, W.Wm.ok(f), W.Wm.ok(W.Wm.with_p(f, x)), True{}, Equal.sym(Bool, W.Wm.ok(W.Wm.with_p(f, x)), W.Wm.ok(f), wp_ok(f, x)), h)
      (Equal.trans(String, T(len, t, W.Wm.with_p(f, x)), String.append(Out(f), TX(len, t, x)), String.append(T(len, t, m0), TX(len, t, x)),
        wp_t(len, t, f, x), Equal.cong(String, String, s => String.append(s, TX(len, t, x)), Out(f), T(len, t, m0), fl_out(len, t, m0, hp, hf))),
        wp_pv(len, f, x, hx))

def cpr_m(+len: U32, +t: AT.Tree<U32>, +m: W.Wm, +x: NS.Rg,
  +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +hx: {W.PV(len, x) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.cpr(len, t, m, x)) == True{} : Bool}) ->
  ADDS(len, t, m, W.Wm.cpr(len, t, m, x), TX(len, t, x)):
  match m:
    case W.Wm{+out, NS.Rg{+a, +z}, True{}}:
      cpr.if_m(U32.is_eq(NS.Rg.a(x), z), len, t, out, a, z, x, hp, hx, {==}, h)
    case W.Wm{+out, NS.Rg{+a, +z}, False{}}:
      ff(ADDS(len, t, W.Wm{out, NS.Rg{a, z}, False{}}, W.Wm{out, NS.Rg{a, z}, False{}}, TX(len, t, x)), h)

def SEPS(+first: Bool, +x: U32) -> String:
  match first:
    case True{}:
      ""
    case False{}:
      NR.chars([x])

def sep_m(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +m: W.Wm, +first: Bool, +x: U32,
  +hp: {W.PV(len, Pm(m)) == True{} : Bool}, +h: {W.Wm.ok(W.Wm.sep(len, t, m, first, x)) == True{} : Bool}) ->
  ADDS(len, t, m, W.Wm.sep(len, t, m, first, x), SEPS(first, x)):
  match first:
    case True{}:
      (Equal.sym(String, String.append(T(len, t, m), ""), T(len, t, m), MN.str_nil(T(len, t, m))), hp)
    case False{}:
      ch_m(len, t, d, hl, m, x, hp, h)
