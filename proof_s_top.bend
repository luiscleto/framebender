import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_run_lem.bend as LM
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_ck.bend as CK
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/LAWS.bend as BL
import lawful-bytes@0.1.0.0/PROOF.bend as BP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB0
import lawful-words@0.1.0.0/proof_nat.bend as N

# The byte splitter's writes from the start (an empty buffer) to the end
# (the last flush and out.ck): the line comes back, and the records' buffer,
# when there is one, holds the text the writes stand for. Every variable is
# reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# The start: nothing written, nothing pending at s
# ---------------------------------------------------------------------------

def W0(+s: U32) -> W.Wm:
  W.Wm{Nil{}, NS.Rg{s, s}, True{}}

def rel0.k(+len: U32, +t: AT.Tree<U32>, +s: U32, +hs: {W.PV(len, NS.Rg{s, s}) == True{} : Bool}, m: C.BMirror(BY.empty(0n))) ->
  W.Rel(len, t, NS.Sw{C.BT(len, t), BY.empty(0n), NS.Rg{s, s}, True{}}, W0(s)):
  (+l0, q) = m
  (+t0, +e) = q
  +ok0 = LM.ok_td(l0, t0, 0n, AB0.subst(D.Bytes, x => {D.ok(x, 0n) == True{} : Bool}, BY.empty(0n), C.BT(l0, t0), Equal.sym(D.Bytes, C.BT(l0, t0), BY.empty(0n), e), BL.empty_ok(0n, {==})))
  +v0 = AB0.subst(D.Bytes, x => {D.view(x) == Nil{} : List<&2, U32>}, BY.empty(0n), C.BT(l0, t0), Equal.sym(D.Bytes, C.BT(l0, t0), BY.empty(0n), e), BL.empty_view(0n))
  %e : W.Rel(len, t, NS.Sw{C.BT(len, t), _, NS.Rg{s, s}, True{}}, W0(s))
  (l0, (t0, ({==}, (ok0, (v0, hs)))))

def rel0(+len: U32, +t: AT.Tree<U32>, +s: U32, +hs: {W.PV(len, NS.Rg{s, s}) == True{} : Bool}) ->
  W.Rel(len, t, NS.Sw{C.BT(len, t), BY.empty(0n), NS.Rg{s, s}, True{}}, W0(s)):
  rel0.k(len, t, s, hs, C.bmirror(BY.empty(0n)))

def t0(+len: U32, +t: AT.Tree<U32>, +s: U32) -> {WT.T(len, t, W0(s)) == "" : String}:
  WT.tzz(len, t, "", s)

# ---------------------------------------------------------------------------
# The end: the last flush, out.ck
# ---------------------------------------------------------------------------

def WOUT(+m: W.Wm) -> List<&2, U32>:
  match m:
    case W.Wm{+out, +p, +ok}:
      out

def out_chars(+m: W.Wm) -> {WT.Out(m) == NR.chars(WOUT(m)) : String}:
  match m:
    case W.Wm{+out, +p, +ok}:
      {==}

# What out.ck gives: the records' buffer (Some) when the flag is set and the
# buffer passes the check (k LFs; no CR unless cr).
def WRB(+b: Bool, +len: U32, +t: AT.Tree<U32>, -out: NS.Ans, +s: String, +g: Bool, +k: Nat, +cr: Bool) -> Type:
  match b:
    case True{}:
      &l2: U32 -> &t2: AT.Tree<U32> -> ({out == NS.Out{C.BT(len, t), Some{C.BT(l2, t2)}} : NS.Ans} &
        ({W.OK(l2, t2) == True{} : Bool} & ({g == True{} : Bool} & ({NR.chars(W.V(l2, t2)) == s : String} & CK.CK(l2, t2, k, cr)))))
    case False{}:
      {out == NS.Out{C.BT(len, t), None{}} : NS.Ans}

def WRES(+len: U32, +t: AT.Tree<U32>, -out: NS.Ans, +s: String, +g: Bool, +k: Nat, +cr: Bool) -> Type:
  &b: Bool -> WRB(b, len, t, out, s, g, k, cr)

def end.b(+b: Bool, +len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, -out: NS.Ans, +s: String, +g: Bool, +k: Nat, +cr: Bool,
  +hok: {W.OK(l2, t2) == True{} : Bool}, +hg: {g == True{} : Bool}, +hs: {NR.chars(W.V(l2, t2)) == s : String},
  q: CK.CKB(b, len, t, l2, t2, out, k, cr)) -> WRB(b, len, t, out, s, g, k, cr):
  match b:
    case True{}:
      (eo, ck) = q
      (l2, (t2, (eo, (hok, (hg, (hs, ck))))))
    case False{}:
      q

def end.c(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, -out: NS.Ans, +s: String, +g: Bool, +k: Nat, +cr: Bool,
  +hok: {W.OK(l2, t2) == True{} : Bool}, +hg: {g == True{} : Bool}, +hs: {NR.chars(W.V(l2, t2)) == s : String},
  r: CK.CKR(len, t, l2, t2, out, k, cr)) -> WRES(len, t, out, s, g, k, cr):
  (+b, q) = r
  (b, end.b(b, len, t, l2, t2, out, s, g, k, cr, hok, hg, hs, q))

def end.t(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +out: List<&2, U32>, +s: String, +g: Bool, +k: Nat, +cr: Bool,
  +hok: {W.OK(l2, t2) == True{} : Bool}, +hv: {W.V(l2, t2) == out : List<&2, U32>},
  q: {g == True{} : Bool} & {NR.chars(out) == s : String}) ->
  WRES(len, t, NS.out.ck(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, True{}}, k, cr), s, g, k, cr):
  (hg, hs) = q
  end.c(len, t, l2, t2, NS.out.ck(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, True{}}, k, cr), s, g, k, cr, hok, hg,
    {%Equal.sym(List<&2, U32>, W.V(l2, t2), out, hv) : {NR.chars(_) == s : String}; hs : {NR.chars(W.V(l2, t2)) == s : String}},
    CK.ck_t(len, t, l2, t2, p, k, cr, hok))

# The model at the end: its flag set, its pending range copied.
def END.k(+b: Bool, +len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +out: List<&2, U32>, +s: String, +g: Bool, +k: Nat, +cr: Bool,
  +hok: {W.OK(l2, t2) == True{} : Bool}, +hv: {W.V(l2, t2) == out : List<&2, U32>},
  i: {b == True{} : Bool} -> ({g == True{} : Bool} & {NR.chars(out) == s : String})) ->
  WRES(len, t, NS.out.ck(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, b}, k, cr), s, g, k, cr):
  match b:
    case True{}:
      end.t(len, t, l2, t2, p, out, s, g, k, cr, hok, hv, i({==}))
    case False{}:
      (False{}, {==})

def end.m(+len: U32, +t: AT.Tree<U32>, -w2: NS.Sw, +m: W.Wm, +s: String, +g: Bool, +k: Nat, +cr: Bool, r: W.Rel(len, t, w2, m),
  i: {W.Wm.ok(m) == True{} : Bool} -> ({g == True{} : Bool} & {NR.chars(WOUT(m)) == s : String})) ->
  WRES(len, t, NS.out.ck(w2, k, cr), s, g, k, cr):
  match m:
    case W.Wm{+out, +p, +ok}:
      (+l2, q) = r
      (+t2, e) = q
      (eq, r1) = e
      (hok, r2) = r1
      (hv, hp) = r2
      %Equal.sym(NS.Sw, w2, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, eq) : WRES(len, t, NS.out.ck(_, k, cr), s, g, k, cr)
      END.k(ok, len, t, l2, t2, p, out, s, g, k, cr, hok, hv, i)

def wr.kk(+len: U32, +t: AT.Tree<U32>, +m1: W.Wm, +s0: U32, +S: String, +G: Bool,
  +hp1: {W.PV(len, WT.Pm(m1)) == True{} : Bool}, +hb: {W.Wm.ok(W.Wm.flush(len, t, m1)) == True{} : Bool},
  p: {W.Wm.ok(W0(s0)) == True{} : Bool} & ({G == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, W0(s0)), S) : String})) ->
  ({G == True{} : Bool} & {NR.chars(WOUT(W.Wm.flush(len, t, m1))) == S : String}):
  (ok0, r) = p
  (hg, ht) = r
  +mf = W.Wm.flush(len, t, m1)
  (hg, Equal.trans(String, NR.chars(WOUT(mf)), WT.Out(mf), S, Equal.sym(String, WT.Out(mf), NR.chars(WOUT(mf)), out_chars(mf)),
    Equal.trans(String, WT.Out(mf), WT.T(len, t, m1), S, WT.fl_out(len, t, m1, hp1, hb),
      Equal.trans(String, WT.T(len, t, m1), String.append(WT.T(len, t, W0(s0)), S), S, ht,
        Equal.cong(String, String, x => String.append(x, S), WT.T(len, t, W0(s0)), "", t0(len, t, s0))))))

def wr.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  -w1: NS.Sw, +m1: W.Wm, +s0: U32, +S: String, +G: Bool, +k: Nat, +cr: Bool,
  rp: W.Rel(len, t, w1, m1) & {W.PV(len, WT.Pm(m1)) == True{} : Bool},
  i1: {W.Wm.ok(m1) == True{} : Bool} -> ({W.Wm.ok(W0(s0)) == True{} : Bool} & ({G == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, W0(s0)), S) : String}))) ->
  WRES(len, t, NS.out.ck(NS.flush(w1), k, cr), S, G, k, cr):
  (r1, +hp1) = rp
  +mf = W.Wm.flush(len, t, m1)
  end.m(len, t, NS.flush(w1), mf, S, G, k, cr, W.bind(len, t, v => NS.flush(v), m => W.Wm.flush(len, t, m), W.flush_op(len, t, d, hl), w1, m1, r1),
    +hb => wr.kk(len, t, m1, s0, S, G, hp1, hb, i1(WT.fl_mono(len, t, m1, hb))))

# The writes from the start, then the last flush: the line, and (when the
# flag is set) a buffer holding their text.
def write_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +s0: U32, -w: NS.Sw, +S: String, +G: Bool, +k: Nat, +cr: Bool, a: S.WS(len, t, w, W0(s0), S, G)) -> WRES(len, t, NS.out.ck(NS.flush(w), k, cr), S, G, k, cr):
  (+m1, q) = a
  (r1, i1) = q
  wr.k(len, t, d, hl, w, m1, s0, S, G, k, cr, S.rel_pv2(len, t, w, m1, r1), i1)
