import Base
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Writes as steps: WS(w, m0, s, g) says the writer state w mirrors a model
# state m1 (proof_s_w.bend's Rel) and, if m1's flag is set, m0's was set,
# g holds (the spec did not refuse) and m1's text is m0's followed by s
# (proof_s_wt.bend's T). Steps chain (ws_seq), so a function made of writes
# needs no model of its own. Every variable is reusable.

def WS(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, +s: String, +g: Bool) -> Type:
  &m1: W.Wm -> (W.Rel(len, t, w, m1) &
    ({W.Wm.ok(m1) == True{} : Bool} -> ({W.Wm.ok(m0) == True{} : Bool} & ({g == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s) : String}))))

# What a Rel gives: the range within the line.
def rel_pv(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m: W.Wm, r: W.Rel(len, t, w, m)) -> {W.PV(len, WT.Pm(m)) == True{} : Bool}:
  match m:
    case W.Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      hp

# Nothing written.
def ws_ret(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) -> WS(len, t, w, m0, "", True{}):
  (m0, (r, h => (h, ({==}, Equal.sym(String, String.append(WT.T(len, t, m0), ""), WT.T(len, t, m0), MN.str_nil(WT.T(len, t, m0)))))))

def ws_seq.k2(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +m2: W.Wm, +s1: String, +s2: String, +g1: Bool, +g2: Bool,
  +hg2: {g2 == True{} : Bool}, +t2: {WT.T(len, t, m2) == String.append(WT.T(len, t, m1), s2) : String},
  p1: {W.Wm.ok(m0) == True{} : Bool} & ({g1 == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s1) : String})) ->
  ({W.Wm.ok(m0) == True{} : Bool} & ({Bool.and(g1, g2) == True{} : Bool} & {WT.T(len, t, m2) == String.append(WT.T(len, t, m0), String.append(s1, s2)) : String})):
  (ok0, r1) = p1
  (hg1, t1) = r1
  +T0 = WT.T(len, t, m0)
  (ok0, ({%Equal.sym(Bool, g1, True{}, hg1) : {Bool.and(_, g2) == True{} : Bool}; hg2 : {Bool.and(g1, g2) == True{} : Bool}},
    Equal.trans(String, WT.T(len, t, m2), String.append(WT.T(len, t, m1), s2), String.append(T0, String.append(s1, s2)), t2,
      Equal.trans(String, String.append(WT.T(len, t, m1), s2), String.append(String.append(T0, s1), s2), String.append(T0, String.append(s1, s2)),
        Equal.cong(String, String, x => String.append(x, s2), WT.T(len, t, m1), String.append(T0, s1), t1), MN.str_assoc(T0, s1, s2)))))

def ws_seq.k(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +m2: W.Wm, +s1: String, +s2: String, +g1: Bool, +g2: Bool,
  i1: {W.Wm.ok(m1) == True{} : Bool} -> ({W.Wm.ok(m0) == True{} : Bool} & ({g1 == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s1) : String})),
  p2: {W.Wm.ok(m1) == True{} : Bool} & ({g2 == True{} : Bool} & {WT.T(len, t, m2) == String.append(WT.T(len, t, m1), s2) : String})) ->
  ({W.Wm.ok(m0) == True{} : Bool} & ({Bool.and(g1, g2) == True{} : Bool} & {WT.T(len, t, m2) == String.append(WT.T(len, t, m0), String.append(s1, s2)) : String})):
  (ok1, r2) = p2
  (hg2, t2) = r2
  ws_seq.k2(len, t, m0, m1, m2, s1, s2, g1, g2, hg2, t2, i1(ok1))

def ws_seq.m(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, -w2: NS.Sw, +s1: String, +s2: String, +g1: Bool, +g2: Bool,
  i1: {W.Wm.ok(m1) == True{} : Bool} -> ({W.Wm.ok(m0) == True{} : Bool} & ({g1 == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s1) : String})),
  b: WS(len, t, w2, m1, s2, g2)) -> WS(len, t, w2, m0, String.append(s1, s2), Bool.and(g1, g2)):
  (+m2, q) = b
  (r2, i2) = q
  (m2, (r2, +h => ws_seq.k(len, t, m0, m1, m2, s1, s2, g1, g2, i1, i2(h))))

# One step, then another from where it led.
def ws_seq(+len: U32, +t: AT.Tree<U32>, -w1: NS.Sw, -G: NS.Sw -> NS.Sw, +m0: W.Wm, +s1: String, +s2: String, +g1: Bool, +g2: Bool,
  a: WS(len, t, w1, m0, s1, g1),
  f: @+m1: W.Wm -> W.Rel(len, t, w1, m1) -> WS(len, t, G(w1), m1, s2, g2)) ->
  WS(len, t, G(w1), m0, String.append(s1, s2), Bool.and(g1, g2)):
  (+m1, q) = a
  (r1, i1) = q
  ws_seq.m(len, t, m0, m1, G(w1), s1, s2, g1, g2, i1, f(m1, r1))

# The same step, said with equal text and flag.
def ws_eq(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, +s: String, +s2: String, +g: Bool, +g2: Bool,
  +es: {s == s2 : String}, +eg: {g == g2 : Bool}, a: WS(len, t, w, m0, s, g)) -> WS(len, t, w, m0, s2, g2):
  %es : WS(len, t, w, m0, _, g2)
  %eg : WS(len, t, w, m0, s, _)
  a

# A Rel, and the range it keeps within the line.
def rel_mk(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +out: List<&2, U32>, +p: NS.Rg, +ok: Bool, +l2: U32, +t2: AT.Tree<U32>,
  eq: {w == NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok} : NS.Sw}, hok: {W.OK(l2, t2) == True{} : Bool}, hv: {W.V(l2, t2) == out : List<&2, U32>},
  +hp: {W.PV(len, p) == True{} : Bool}) -> (W.Rel(len, t, w, W.Wm{out, p, ok}) & {W.PV(len, p) == True{} : Bool}):
  ((l2, (t2, (eq, (hok, (hv, hp))))), hp)

def rel_pv2(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m: W.Wm, r: W.Rel(len, t, w, m)) -> (W.Rel(len, t, w, m) & {W.PV(len, WT.Pm(m)) == True{} : Bool}):
  match m:
    case W.Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      rel_mk(len, t, w, out, p, ok, l2, t2, eq, hok, hv, hp)

def adds_t(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +s: String, a: WT.ADDS(len, t, m0, m1, s)) -> {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s) : String}:
  (e, pv) = a
  e

# ---------------------------------------------------------------------------
# The writes as steps
# ---------------------------------------------------------------------------

def ws_cpr.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: NS.Rg, +hx: {W.PV(len, x) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, rp: W.Rel(len, t, w, m0) & {W.PV(len, WT.Pm(m0)) == True{} : Bool}) ->
  WS(len, t, NS.cpr(w, x), m0, WT.TX(len, t, x), True{}):
  (r, +hp) = rp
  (W.Wm.cpr(len, t, m0, x), (W.bind(len, t, v => NS.cpr(v, x), m => W.Wm.cpr(len, t, m, x), W.cpr_op(len, t, d, hl, x, hx), w, m0, r),
    +h => (WT.cpr_mono(len, t, m0, x, h), ({==}, adds_t(len, t, m0, W.Wm.cpr(len, t, m0, x), WT.TX(len, t, x), WT.cpr_m(len, t, m0, x, hp, hx, h))))))

def ws_cpr(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: NS.Rg, +hx: {W.PV(len, x) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) -> WS(len, t, NS.cpr(w, x), m0, WT.TX(len, t, x), True{}):
  ws_cpr.k(len, t, d, hl, x, hx, w, m0, rel_pv2(len, t, w, m0, r))

def ws_ch.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, rp: W.Rel(len, t, w, m0) & {W.PV(len, WT.Pm(m0)) == True{} : Bool}) ->
  WS(len, t, NS.ch(w, x), m0, NR.chars([x]), True{}):
  (r, +hp) = rp
  (W.Wm.ch(len, t, m0, x), (W.bind(len, t, v => NS.ch(v, x), m => W.Wm.ch(len, t, m, x), W.ch_op(len, t, d, hl, x, hx), w, m0, r),
    +h => (WT.ch_mono(len, t, m0, x, h), ({==}, adds_t(len, t, m0, W.Wm.ch(len, t, m0, x), NR.chars([x]), WT.ch_m(len, t, d, hl, m0, x, hp, h))))))

def ws_ch(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) -> WS(len, t, NS.ch(w, x), m0, NR.chars([x]), True{}):
  ws_ch.k(len, t, d, hl, x, hx, w, m0, rel_pv2(len, t, w, m0, r))

def ws_sep.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +first: Bool, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, rp: W.Rel(len, t, w, m0) & {W.PV(len, WT.Pm(m0)) == True{} : Bool}) ->
  WS(len, t, NS.sep(w, first, x), m0, WT.SEPS(first, x), True{}):
  (r, +hp) = rp
  (W.Wm.sep(len, t, m0, first, x), (W.bind(len, t, v => NS.sep(v, first, x), m => W.Wm.sep(len, t, m, first, x), W.sep_op(len, t, d, hl, first, x, hx), w, m0, r),
    +h => (WT.sep_mono(len, t, m0, first, x, h), ({==}, adds_t(len, t, m0, W.Wm.sep(len, t, m0, first, x), WT.SEPS(first, x), WT.sep_m(len, t, d, hl, m0, first, x, hp, h))))))

def ws_sep(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +first: Bool, +x: U32, +hx: {U32.is_lt(x, 256) == True{} : Bool},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) -> WS(len, t, NS.sep(w, first, x), m0, WT.SEPS(first, x), True{}):
  ws_sep.k(len, t, d, hl, first, x, hx, w, m0, rel_pv2(len, t, w, m0, r))

def ws_fail(+len: U32, +t: AT.Tree<U32>, +s: String, +g: Bool, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) -> WS(len, t, NS.Sw.fail(w), m0, s, g):
  (W.Wm.fail(m0), (W.bind(len, t, v => NS.Sw.fail(v), m => W.Wm.fail(m), W.fail_op(len, t), w, m0, r),
    +h => WT.fail_f({W.Wm.ok(m0) == True{} : Bool} & ({g == True{} : Bool} & {WT.T(len, t, W.Wm.fail(m0)) == String.append(WT.T(len, t, m0), s) : String}), m0, h)))

# A step from a state given by its parts.
def ws_at(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, -F: NS.Sw -> NS.Sw, +m0: W.Wm, +s: String, +g: Bool, r: W.Rel(len, t, w, m0),
  f: @+l2: U32 -> @+t2: AT.Tree<U32> -> @+p: NS.Rg -> @+ok: Bool -> @+h: {W.OK(l2, t2) == True{} : Bool} -> @+hp: {W.PV(len, p) == True{} : Bool} ->
    WS(len, t, F(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}), W.Wm{W.V(l2, t2), p, ok}, s, g)) ->
  WS(len, t, F(w), m0, s, g):
  match m0:
    case W.Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      %Equal.sym(NS.Sw, w, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, eq) : WS(len, t, F(_), W.Wm{out, p, ok}, s, g)
      %hv : WS(len, t, F(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}), W.Wm{_, p, ok}, s, g)
      f(l2, t2, p, ok, hok, hp)

def ws_imp.j(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +s: String, +s2: String, +g2: Bool,
  ok0: {W.Wm.ok(m0) == True{} : Bool}, +ht: {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s) : String},
  q: {g2 == True{} : Bool} & {s == s2 : String}) ->
  ({W.Wm.ok(m0) == True{} : Bool} & ({g2 == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s2) : String})):
  (hg2, es) = q
  (ok0, (hg2, {%es : {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), _) : String}; ht : {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s2) : String}}))

def ws_imp.k(+len: U32, +t: AT.Tree<U32>, +m0: W.Wm, +m1: W.Wm, +s: String, +g: Bool, +s2: String, +g2: Bool,
  k: {g == True{} : Bool} -> ({g2 == True{} : Bool} & {s == s2 : String}),
  p: {W.Wm.ok(m0) == True{} : Bool} & ({g == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s) : String})) ->
  ({W.Wm.ok(m0) == True{} : Bool} & ({g2 == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s2) : String})):
  (ok0, r) = p
  (hg, ht) = r
  ws_imp.j(len, t, m0, m1, s, s2, g2, ok0, ht, k(hg))

# The same step, its text and flag read anew when the flag holds.
def ws_imp(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, +s: String, +g: Bool, +s2: String, +g2: Bool,
  k: {g == True{} : Bool} -> ({g2 == True{} : Bool} & {s == s2 : String}), a: WS(len, t, w, m0, s, g)) -> WS(len, t, w, m0, s2, g2):
  (+m1, q) = a
  (r, i) = q
  (m1, (r, +h => ws_imp.k(len, t, m0, m1, s, g, s2, g2, k, i(h))))
