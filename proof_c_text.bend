import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fix.bend as NX
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import ./proof_b_judge_bytes.bend as JB
import ./proof_b_run_inv.bend as PI
import lawful-bytes@0.1.0.0/bytes.bend as BY
import ./proof_c_defs.bend as Q
import ./proof_c_tan_pair.bend as TP
import ./proof_c_text_w.bend as WW
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase C: the rewritten line norm_fix.bend's NX.write builds, on mirrors:
# its buffer holds CHROM and its tab, the new POS, the tab, ID and the tab
# after it, the new REF's letters, a tab, the new ALTs' letters (commas
# between), then the line from ALT's tab to its LF; unless a size check
# failed (ok False: the line then takes the String path). Every variable is
# reusable.

# ---------------------------------------------------------------------------
# The alleles' letters, without the buffers
# ---------------------------------------------------------------------------

# n letters for bytes j, j+1, ... of R_k ++ a (NX.al.go's text).
def ALS(n: Nat, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +a: NX.Ap, +k: U32, +j: U32, +p0: U32, +offu: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      SCon{Chr{NX.letter(NX.code(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)))}, ALS(m, bl, bt, wl, wt, a, k, (j + 1 : U32), p0, offu)}

# How many letters an allele keeps: L - tr - d.
def NA(+a: NX.Ap, +tr: U32, +d: Nat) -> U32:
  ((NX.Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)

# An allele's letters (NX.al's text).
def ALA(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +a: NX.Ap, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32) -> String:
  ALS(U32.to_nat(NA(a, tr, d)), bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu)

# The ALTs' letters after acc, commas between (NX.as.go's text).
def ACC(als: List<&2, NX.Ap>, +acc: String, first: Bool, +bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32) -> String:
  match als:
    case Nil{}:
      acc
    case +a <> t:
      ACC(t, String.append(acc, String.append(Bool.pick(String, first, "", ","), ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu))), False{}, bl, bt, wl, wt, k, tr, d, p0, offu)

law al_go_pair:
  for +n: Nat
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +a: NX.Ap
  for +k: U32
  for +j: U32
  for +p0: U32
  for +offu: U32
  {NX.al.go(n, NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)}, a, k, j, p0, offu) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALS(n, bl, bt, wl, wt, a, k, j, p0, offu)} : NX.Rs}

def al_go_pair(n, bl, bt, wl, wt, a, k, j, p0, offu):
  match n:
    case 0n:
      {==}
    case 1n+(+m):
      +j1 = (j + 1 : U32)
      %Equal.sym(NX.Rd, NX.el(C.BT(bl, bt), C.BT(wl, wt), a, k, j1, p0, offu), NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL(bl, bt, wl, wt, a, k, j1, p0, offu)}, TP.el_pair(bl, bt, wl, wt, a, k, j1, p0, offu)) :
        {NX.al.cons(Chr{NX.letter(NX.code(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)))}, NX.al.go(m, _, a, k, j1, p0, offu)) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALS(1n+m, bl, bt, wl, wt, a, k, j, p0, offu)} : NX.Rs}
      %Equal.sym(NX.Rs, NX.al.go(m, NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL(bl, bt, wl, wt, a, k, j1, p0, offu)}, a, k, j1, p0, offu), NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALS(m, bl, bt, wl, wt, a, k, j1, p0, offu)}, al_go_pair(m, bl, bt, wl, wt, a, k, j1, p0, offu)) :
        {NX.al.cons(Chr{NX.letter(NX.code(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)))}, _) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALS(1n+m, bl, bt, wl, wt, a, k, j, p0, offu)} : NX.Rs}
      {==}

law al_pair:
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +a: NX.Ap
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +p0: U32
  for +offu: U32
  {NX.al(C.BT(bl, bt), C.BT(wl, wt), a, k, tr, d, p0, offu) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)} : NX.Rs}

def al_pair(bl, bt, wl, wt, a, k, tr, d, p0, offu):
  +j = U32.from_nat(d)
  %Equal.sym(NX.Rd, NX.el(C.BT(bl, bt), C.BT(wl, wt), a, k, j, p0, offu), NX.Rd{C.BT(bl, bt), C.BT(wl, wt), Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)}, TP.el_pair(bl, bt, wl, wt, a, k, j, p0, offu)) :
    {NX.al.go(U32.to_nat(NA(a, tr, d)), _, a, k, j, p0, offu) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)} : NX.Rs}
  al_go_pair(U32.to_nat(NA(a, tr, d)), bl, bt, wl, wt, a, k, j, p0, offu)

law as_pair:
  for +als: List<&2, NX.Ap>
  for +acc: String
  for +first: Bool
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +p0: U32
  for +offu: U32
  {NX.as.go(als, NX.Rs{C.BT(bl, bt), C.BT(wl, wt), acc}, first, k, tr, d, p0, offu) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ACC(als, acc, first, bl, bt, wl, wt, k, tr, d, p0, offu)} : NX.Rs}

def as_pair(als, acc, first, bl, bt, wl, wt, k, tr, d, p0, offu):
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      +sep = Bool.pick(String, first, "", ",")
      +acc2 = String.append(acc, String.append(sep, ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)))
      %Equal.sym(NX.Rs, NX.al(C.BT(bl, bt), C.BT(wl, wt), a, k, tr, d, p0, offu), NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)}, al_pair(bl, bt, wl, wt, a, k, tr, d, p0, offu)) :
        {NX.as.go(t, NX.as.add(acc, sep, _), False{}, k, tr, d, p0, offu) == NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ACC(a <> t, acc, first, bl, bt, wl, wt, k, tr, d, p0, offu)} : NX.Rs}
      as_pair(t, acc2, False{}, bl, bt, wl, wt, k, tr, d, p0, offu)

# ---------------------------------------------------------------------------
# Letters are bytes
# ---------------------------------------------------------------------------

def lb.k(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) ->
  {U32.is_lt(Bool.pick(U32, b0, 65, Bool.pick(U32, b1, 67, Bool.pick(U32, b2, 71, Bool.pick(U32, b3, 84, 78)))), 256) == True{} : Bool}:
  match b0 b1 b2 b3:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def letter_byte(+c: U32) -> {U32.is_lt(NX.letter(c), 256) == True{} : Bool}:
  lb.k(U32.is_eq(c, 0), U32.is_eq(c, 1), U32.is_eq(c, 2), U32.is_eq(c, 3))

law als_bytes:
  for +n: Nat
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +a: NX.Ap
  for +k: U32
  for +j: U32
  for +p0: U32
  for +offu: U32
  {E.is_bytes(ALS(n, bl, bt, wl, wt, a, k, j, p0, offu)) == True{} : Bool}

def als_bytes(n, bl, bt, wl, wt, a, k, j, p0, offu):
  match n:
    case 0n:
      {==}
    case 1n+(+m):
      +x = NX.letter(NX.code(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)))
      %Equal.sym(Bool, U32.is_lt(x, 256), True{}, letter_byte(NX.code(Q.EL(bl, bt, wl, wt, a, k, j, p0, offu)))) :
        {Bool.and(_, E.is_bytes(ALS(m, bl, bt, wl, wt, a, k, (j + 1 : U32), p0, offu))) == True{} : Bool}
      als_bytes(m, bl, bt, wl, wt, a, k, (j + 1 : U32), p0, offu)

# ---------------------------------------------------------------------------
# The writes, in order
# ---------------------------------------------------------------------------

def K1(+at: U32, +e0: U32) -> U32:
  ((e0 + 1 : U32) - at : U32)

def K2(+e1: U32, +e2: U32) -> U32:
  ((e2 + 1 : U32) - e1 : U32)

def K3(+e4: U32, +lf: U32) -> U32:
  ((lf + 1 : U32) - e4 : U32)

# What the writes from a buffer x on give: a buffer, ok, and (if ok) the text.
def WR(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, x: NX.Wb, +text: String) -> Type:
  &sl: U32 -> &st: AT.Tree<U32> -> &ok: Bool -> ({x == NX.Wb{C.BT(sl, st), C.BT(bl, bt), C.BT(wl, wt), ok} : NX.Wb}
  & ({WW.OK(sl, st) == True{} : Bool}
  & {Bool.pick(String, ok, NR.chars(WW.V(sl, st)), text) == text : String}))

def TXT(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String) -> String:
  String.append(String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf)))))

# A write that failed: the buffers back, ok false (stated for any text so the
# kernel does not normalize the text: --verdict overflowed on the inline tuple).
def wrF(+bl: U32, +bt: AT.Tree<U32>, +wl: U32, +wt: AT.Tree<U32>, +l: U32, +t: AT.Tree<U32>, +x: String,
  +hok: {WW.OK(l, t) == True{} : Bool}) ->
  WR(bl, bt, wl, wt, NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), False{}}, x):
  (l, (t, (False{}, ({==}, (hok, {==})))))

def L8(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))) : String}) ->
  WR(bl, bt, wl, wt, NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (l, (t, (True{}, ({==}, (hok, hc)))))

def L7.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as) : String},
  m: WW.WbG(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e4, K3(e4, lf)), l, t, D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e4, K3(e4, lf)), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, _, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L8(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))), String.append(String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))),
      Equal.cong(List<&2, U32>, String, z => NR.chars(z), WW.V(l2, t2), List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf)))), vw),
      Equal.trans(String, NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))), String.append(NR.chars(WW.V(l, t)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))), String.append(String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))), BF.chars_app(WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf)))),
        Equal.cong(String, String, z => String.append(z, NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e4), U32.to_nat(K3(e4, lf))))), NR.chars(WW.V(l, t)), String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), hc))))

def L7.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as) : String},
  +eg: {WW.PBC(l, K3(e4, lf)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L7.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_b_t(l, t, bl, bt, bd, wl, wt, e4, K3(e4, lf), hok, hbo, h3, eg))
    case False{}:
      %Equal.sym(Bool, WW.PBC(l, K3(e4, lf)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.pb.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L7(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as) : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L7.g(WW.PBC(l, K3(e4, lf)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L6.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t") : String},
  m: &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, as) == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
  & ({WW.OK(l2, t2) == True{} : Bool}
  & {NR.chars(WW.V(l2, t2)) == String.append(NR.chars(WW.V(l, t)), as) : String}))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, as), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(_, e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L7(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), String.append(NR.chars(WW.V(l, t)), as), String.append(String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), as), vw,
      Equal.cong(String, String, z => String.append(z, as), NR.chars(WW.V(l, t)), String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), hc)))

def L6.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t") : String},
  +eg: {Bool.and(U32.is_le(l, 536870912), NX.len_le(as, 268435456)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L6.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_s_t(l, t, bl, bt, wl, wt, as, hok, has, eg))
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), NX.len_le(as, 268435456)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.ps.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L6(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t") : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L6.g(Bool.and(U32.is_le(l, 536870912), NX.len_le(as, 268435456)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L5.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs) : String},
  m: WW.WbG(bl, bt, wl, wt, NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, 9), l, t, [9])) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, 9), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(_, as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L6(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), NR.chars(List.append(&2, U32, WW.V(l, t), [9])), String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"),
      Equal.cong(List<&2, U32>, String, z => NR.chars(z), WW.V(l2, t2), List.append(&2, U32, WW.V(l, t), [9]), vw),
      Equal.trans(String, NR.chars(List.append(&2, U32, WW.V(l, t), [9])), String.append(NR.chars(WW.V(l, t)), "\t"), String.append(String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), "\t"), BF.chars_app(WW.V(l, t), [9]),
        Equal.cong(String, String, z => String.append(z, "\t"), NR.chars(WW.V(l, t)), String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), hc))))

def L5.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs) : String},
  +eg: {Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L5.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_c_t(l, t, bl, bt, wl, wt, 9, hok, {==}, eg))
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.pc.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L5(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs) : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L5.g(Bool.and(U32.is_le(l, 536870912), U32.is_le(1, 268435456)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L4.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))) : String},
  m: &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, rs) == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
  & ({WW.OK(l2, t2) == True{} : Bool}
  & {NR.chars(WW.V(l2, t2)) == String.append(NR.chars(WW.V(l, t)), rs) : String}))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, rs), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(_, 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L5(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), String.append(NR.chars(WW.V(l, t)), rs), String.append(String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), rs), vw,
      Equal.cong(String, String, z => String.append(z, rs), NR.chars(WW.V(l, t)), String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), hc)))

def L4.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))) : String},
  +eg: {Bool.and(U32.is_le(l, 536870912), NX.len_le(rs, 268435456)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L4.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_s_t(l, t, bl, bt, wl, wt, rs, hok, hrs, eg))
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), NX.len_le(rs, 268435456)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.ps.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L4(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))) : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L4.g(Bool.and(U32.is_le(l, 536870912), NX.len_le(rs, 268435456)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L3.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)) : String},
  m: WW.WbG(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e1, K2(e1, e2)), l, t, D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e1, K2(e1, e2)), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(_, rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L4(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))),
      Equal.cong(List<&2, U32>, String, z => NR.chars(z), WW.V(l2, t2), List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2)))), vw),
      Equal.trans(String, NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), String.append(NR.chars(WW.V(l, t)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), String.append(String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), BF.chars_app(WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2)))),
        Equal.cong(String, String, z => String.append(z, NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(e1), U32.to_nat(K2(e1, e2))))), NR.chars(WW.V(l, t)), String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), hc))))

def L3.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)) : String},
  +eg: {WW.PBC(l, K2(e1, e2)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L3.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_b_t(l, t, bl, bt, bd, wl, wt, e1, K2(e1, e2), hok, hbo, h2, eg))
    case False{}:
      %Equal.sym(Bool, WW.PBC(l, K2(e1, e2)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.pb.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L3(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)) : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L3.g(WW.PBC(l, K2(e1, e2)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L2.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))) : String},
  m: &l2: U32 -> &t2: AT.Tree<U32> -> ({NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, Nat.show(q)) == NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}} : NX.Wb}
  & ({WW.OK(l2, t2) == True{} : Bool}
  & {NR.chars(WW.V(l2, t2)) == String.append(NR.chars(WW.V(l, t)), Nat.show(q)) : String}))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, Nat.show(q)), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(_, e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L3(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), String.append(NR.chars(WW.V(l, t)), Nat.show(q)), String.append(NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), Nat.show(q)), vw,
      Equal.cong(String, String, z => String.append(z, Nat.show(q)), NR.chars(WW.V(l, t)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), hc)))

def L2.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))) : String},
  +eg: {Bool.and(U32.is_le(l, 536870912), NX.len_le(Nat.show(q), 268435456)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L2.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_s_t(l, t, bl, bt, wl, wt, Nat.show(q), hok, JB.show_bytes(q), eg))
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_le(l, 536870912), NX.len_le(Nat.show(q), 268435456)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.ps.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L2(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))) : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L2.g(Bool.and(U32.is_le(l, 536870912), NX.len_le(Nat.show(q), 268435456)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

def L1.t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == "" : String},
  m: WW.WbG(bl, bt, wl, wt, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), l, t, D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0))))) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  (+l2, r1) = m
  (+t2, r2) = r1
  (eq, r3) = r2
  (ok2, vw) = r3
  %Equal.sym(NX.Wb, NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), NX.Wb{C.BT(l2, t2), C.BT(bl, bt), C.BT(wl, wt), True{}}, eq) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(_, Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
  L2(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l2, t2, hbo, h1, h2, h3, hrs, has, ok2, Equal.trans(String, NR.chars(WW.V(l2, t2)), NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0))))), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))),
      Equal.cong(List<&2, U32>, String, z => NR.chars(z), WW.V(l2, t2), List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), vw),
      Equal.trans(String, NR.chars(List.append(&2, U32, WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0))))), String.append(NR.chars(WW.V(l, t)), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0))))), NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))), BF.chars_app(WW.V(l, t), D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0)))),
        Equal.cong(String, String, z => String.append(z, NR.chars(D.slice(WW.V(bl, bt), U32.to_nat(at), U32.to_nat(K1(at, e0))))), NR.chars(WW.V(l, t)), "", hc))))

def L1.g(+g: Bool, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == "" : String},
  +eg: {WW.PBC(l, K1(at, e0)) == g : Bool}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  match g:
    case True{}:
      L1.t(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, WW.put_b_t(l, t, bl, bt, bd, wl, wt, at, K1(at, e0), hok, hbo, h1, eg))
    case False{}:
      %Equal.sym(Bool, WW.PBC(l, K1(at, e0)), False{}, eg) :
        WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.pb.ok(_, C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), at, K1(at, e0)), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as))
      wrF(bl, bt, wl, wt, l, t, TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as), hok)

def L1(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>, +at: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, +as: String, +l: U32, +t: AT.Tree<U32>,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool},
  +hrs: {E.is_bytes(rs) == True{} : Bool},
  +has: {E.is_bytes(as) == True{} : Bool},
  +hok: {WW.OK(l, t) == True{} : Bool},
  +hc: {NR.chars(WW.V(l, t)) == "" : String}) ->
  WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.put_b(NX.Wb{C.BT(l, t), C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)):
  L1.g(WW.PBC(l, K1(at, e0)), bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, l, t, hbo, h1, h2, h3, hrs, has, hok, hc, {==})

law sep_bytes:
  for +first: Bool
  {E.is_bytes(Bool.pick(String, first, "", ",")) == True{} : Bool}

def sep_bytes(first):
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

law acc_bytes:
  for +als: List<&2, NX.Ap>
  for +acc: String
  for +first: Bool
  for +bl: U32
  for +bt: AT.Tree<U32>
  for +wl: U32
  for +wt: AT.Tree<U32>
  for +k: U32
  for +tr: U32
  for +d: Nat
  for +p0: U32
  for +offu: U32
  for +h: {E.is_bytes(acc) == True{} : Bool}
  {E.is_bytes(ACC(als, acc, first, bl, bt, wl, wt, k, tr, d, p0, offu)) == True{} : Bool}

def acc_bytes(als, acc, first, bl, bt, wl, wt, k, tr, d, p0, offu, h):
  match als:
    case Nil{}:
      h
    case +a <> +t:
      +A = ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)
      +sep = Bool.pick(String, first, "", ",")
      acc_bytes(t, String.append(acc, String.append(sep, A)), False{}, bl, bt, wl, wt, k, tr, d, p0, offu,
        PI.bytes_app(acc, String.append(sep, A), h, PI.bytes_app(sep, A, sep_bytes(first), als_bytes(U32.to_nat(NA(a, tr, d)), bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu))))

def QQ(+p0: U32, +k: U32, +d: Nat) -> Nat:
  U32.to_nat(((p0 - k : U32) + U32.from_nat(d) : U32))

# NX.write on mirrors (REF a first, ALTs als).
def write_t(+bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +wl: U32, +wt: AT.Tree<U32>,
  +at: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +a: NX.Ap, +als: List<&2, NX.Ap>, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32,
  +hbo: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +h1: {Nat.is_le(Nat.add(U32.to_nat(at), U32.to_nat(K1(at, e0))), U32.to_nat(bl)) == True{} : Bool},
  +h2: {Nat.is_le(Nat.add(U32.to_nat(e1), U32.to_nat(K2(e1, e2))), U32.to_nat(bl)) == True{} : Bool},
  +h3: {Nat.is_le(Nat.add(U32.to_nat(e4), U32.to_nat(K3(e4, lf))), U32.to_nat(bl)) == True{} : Bool}) ->
  WR(bl, bt, wl, wt, NX.write(C.BT(bl, bt), C.BT(wl, wt), at, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, a <> als, k, tr, d, p0, offu),
    TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, QQ(p0, k, d), ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu), ACC(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu))):
  +q = QQ(p0, k, d)
  +rs = ALA(bl, bt, wl, wt, a, k, tr, d, p0, offu)
  +as = ACC(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu)
  +G0 = TXT(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as)
  +t0 = G.tnew(0n, 0)
  %Equal.sym(NX.Rs, NX.al(C.BT(bl, bt), C.BT(wl, wt), a, k, tr, d, p0, offu), NX.Rs{C.BT(bl, bt), C.BT(wl, wt), rs}, al_pair(bl, bt, wl, wt, a, k, tr, d, p0, offu)) :
    WR(bl, bt, wl, wt, NX.wr.alts(at, e0, e1, e2, e4, lf, q, als, k, tr, d, p0, offu, _), G0)
  %Equal.sym(NX.Rs, NX.as.go(als, NX.Rs{C.BT(bl, bt), C.BT(wl, wt), ""}, True{}, k, tr, d, p0, offu), NX.Rs{C.BT(bl, bt), C.BT(wl, wt), as}, as_pair(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu)) :
    WR(bl, bt, wl, wt, NX.wr.fin(at, e0, e1, e2, e4, lf, q, rs, _), G0)
  %Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)) :
    WR(bl, bt, wl, wt, NX.put_b(NX.put_s(NX.put_c(NX.put_s(NX.put_b(NX.put_s(NX.put_b(NX.Wb{_, C.BT(bl, bt), C.BT(wl, wt), True{}}, at, K1(at, e0)), Nat.show(q)), e1, K2(e1, e2)), rs), 9), as), e4, K3(e4, lf)), G0)
  L1(bl, bt, bd, wl, wt, at, e0, e1, e2, e4, lf, q, rs, as, 0, t0, hbo, h1, h2, h3,
    als_bytes(U32.to_nat(NA(a, tr, d)), bl, bt, wl, wt, a, k, U32.from_nat(d), p0, offu), acc_bytes(als, "", True{}, bl, bt, wl, wt, k, tr, d, p0, offu, {==}),
    BF.empty_ok_td(0n, {==}),
    Equal.cong(List<&2, U32>, String, z => NR.chars(z), WW.V(0, t0), Nil{}, BF.view0(t0)))
