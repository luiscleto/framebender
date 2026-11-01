import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_read.bend as RD
import ./proof_s_scan.bend as SC
import ./proof_b_fasteq.bend as FE
import ./proof_s_gtspec.bend as G
import ./proof_s_tok.bend as TK
import ./proof_b_cut_pair.bend as CP
import lawful-bytes@0.1.1.0/fast.bend as F
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-fields@0.1.1.0/fields.bend as FC
import lawful-fields@0.1.1.0/LAWS.bend as FL
import lawful-fields@0.1.1.0/PROOF.bend as FP
import lawful-fields@0.1.1.0/proof_num.bend as LN
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A genotype in the record for ALT i (norm_split.bend's tok and gt) writes
# what B.Gt.split gives. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def X(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

def TXR(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  WT.TX(len, t, NS.Rg{a, z})

def TOKT(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  G.GSTR(G.ALLELE(o, nn, i, TXR(len, t, a, z)))

def TOKG(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> Bool:
  G.GOK(G.ALLELE(o, nn, i, TXR(len, t, a, z)))

# ---------------------------------------------------------------------------
# The bytes of a token
# ---------------------------------------------------------------------------

# One byte.
def tx1(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +he: {U32.is_eq((z - a : U32), 1) == True{} : Bool}) -> {TXR(len, t, a, z) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}:
  +e1 = Equal.cong(U32, Nat, w => U32.to_nat(w), (z - a : U32), 1, U.is_eq_true((z - a : U32), 1, he))
  +haz = W.pv_a(len, a, z, hp)
  +ez = {%W.nsub(a, z, haz) : {_ == 1n : Nat}; e1 : {Nat.sub(n(z), n(a)) == 1n : Nat}}
  +ez2 = {%N.le_sub_add(n(a), n(z), haz) : {_ == Nat.add(n(a), 1n) : Nat};
    %Equal.sym(Nat, Nat.sub(n(z), n(a)), 1n, ez) : {Nat.add(n(a), _) == Nat.add(n(a), 1n) : Nat}; {==} : {n(z) == Nat.add(n(a), 1n) : Nat}}
  +hal = {%ez2 : {Nat.is_le(_, n(len)) == True{} : Bool}; W.pv_z(len, a, z, hp) : {Nat.is_le(Nat.add(n(a), 1n), n(len)) == True{} : Bool}}
  +hlt = {%N.le_succ_lt(n(a), n(len)) : {_ == True{} : Bool}; %N.add_one(n(a)) : {Nat.is_le(_, n(len)) == True{} : Bool}; hal : {Nat.is_lt(n(a), n(len)) == True{} : Bool}}
  +hg = Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, a)}, List.get(&2, U32, X(len, t), n(a)),
    C.at_view_t(len, t, d, a, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hlt))
  +hl1 = {%N.le_succ_lt(n(a), Nat.add(n(a), 1n)) : {_ == True{} : Bool}; %Equal.sym(Nat, Nat.add(n(a), 1n), 1n+n(a), N.add_one(n(a))) : {Nat.is_le(1n+n(a), _) == True{} : Bool}; N.le_refl(1n+n(a)) : {Nat.is_lt(n(a), Nat.add(n(a), 1n)) == True{} : Bool}}
  %Equal.sym(Nat, n((z - a : U32)), 1n, e1) : {NR.chars(D.slice(X(len, t), n(a), _)) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}
  %N.sub_add_l(n(a), 1n) : {NR.chars(D.slice(X(len, t), n(a), _)) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}
  %Equal.sym(L32(), D.slice(X(len, t), n(a), Nat.sub(Nat.add(n(a), 1n), n(a))), C.AT(len, t, a) <> D.slice(X(len, t), Nat.add(n(a), 1n), Nat.sub(Nat.add(n(a), 1n), Nat.add(n(a), 1n))),
    LS.slice_lt(X(len, t), n(a), Nat.add(n(a), 1n), C.AT(len, t, a), hl1, hg)) : {NR.chars(_) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}
  %Equal.sym(Nat, Nat.sub(Nat.add(n(a), 1n), Nat.add(n(a), 1n)), 0n, LS.sub_self(Nat.add(n(a), 1n))) : {NR.chars(C.AT(len, t, a) <> D.slice(X(len, t), Nat.add(n(a), 1n), _)) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}
  %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, X(len, t), Nat.add(n(a), 1n)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, X(len, t), Nat.add(n(a), 1n)))) : {NR.chars(C.AT(len, t, a) <> _) == SCon{Chr{C.AT(len, t, a)}, SNil{}} : String}
  {==}

def lt_of_add(+i: Nat, +k: Nat) -> {Nat.is_lt(i, Nat.add(i, 1n+k)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(i, 1n+k), 1n+Nat.add(i, k), N.add_succ(i, k)) : {Nat.is_lt(i, _) == True{} : Bool}
  %N.le_succ_lt(i, 1n+Nat.add(i, k)) : {_ == True{} : Bool}
  N.le_add_r(i, k)

# a < z and z - a != 1: a + 1 < z.
def two.k(+na: Nat, +nz: Nat, +k: Nat, +ha: {Nat.is_lt(na, nz) == True{} : Bool},
  +hne: {Nat.is_eq(Nat.sub(nz, na), 1n) == False{} : Bool},
  +hk: {Nat.sub(nz, Nat.add(na, 1n)) == k : Nat}) -> {Nat.is_lt(Nat.add(na, 1n), nz) == True{} : Bool}:
  match k:
    case 0n:
      +e1 = Equal.trans(Nat, Nat.sub(nz, na), 1n+Nat.sub(nz, Nat.add(na, 1n)), 1n, LS.sub_lt(nz, na, ha), Equal.cong(Nat, Nat, x => 1n+x, Nat.sub(nz, Nat.add(na, 1n)), 0n, hk))
      Empty.absurd({Nat.is_lt(Nat.add(na, 1n), nz) == True{} : Bool},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_eq(Nat.sub(nz, na), 1n), True{}, Equal.sym(Bool, Nat.is_eq(Nat.sub(nz, na), 1n), False{}, hne),
          %Equal.sym(Nat, Nat.sub(nz, na), 1n, e1) : {Nat.is_eq(_, 1n) == True{} : Bool}; {==})))
    case 1n+q:
      +hle = {%Equal.sym(Nat, Nat.add(na, 1n), 1n+na, N.add_one(na)) : {Nat.is_le(_, nz) == True{} : Bool}; %Equal.sym(Bool, Nat.is_le(1n+na, nz), Nat.is_lt(na, nz), N.le_succ_lt(na, nz)) : {_ == True{} : Bool}; ha : {Nat.is_le(Nat.add(na, 1n), nz) == True{} : Bool}}
      %Equal.sym(Nat, nz, Nat.add(Nat.add(na, 1n), Nat.sub(nz, Nat.add(na, 1n))), Equal.sym(Nat, Nat.add(Nat.add(na, 1n), Nat.sub(nz, Nat.add(na, 1n))), nz, N.le_sub_add(Nat.add(na, 1n), nz, hle))) :
        {Nat.is_lt(Nat.add(na, 1n), _) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(nz, Nat.add(na, 1n)), 1n+q, hk) : {Nat.is_lt(Nat.add(na, 1n), Nat.add(Nat.add(na, 1n), _)) == True{} : Bool}
      lt_of_add(Nat.add(na, 1n), q)

def A1(+a: U32) -> U32:
  (a + 1 : U32)

# Two bytes or more.
def tx2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +ha: {Nat.is_lt(n(a), n(z)) == True{} : Bool}, +hne: {U32.is_eq((z - a : U32), 1) == False{} : Bool}) ->
  {RD.BS(len, t, a, z) == C.AT(len, t, a) <> (C.AT(len, t, A1(a)) <> RD.BS(len, t, A1(A1(a)), z)) : L32()}:
  +haz = N.lt_to_le(n(a), n(z), ha)
  +hne2 = {%W.nsub(a, z, haz) : {Nat.is_eq(_, 1n) == False{} : Bool}; %U.is_eq_to_nat((z - a : U32), 1) : {_ == False{} : Bool}; hne : {Nat.is_eq(Nat.sub(n(z), n(a)), 1n) == False{} : Bool}}
  +hl = N.lt_le_trans(n(a), n(z), n(len), ha, hzl)
  +ha1 = {%Equal.sym(Nat, n((a + 1 : U32)), Nat.add(n(a), 1n), AL.inc_len(len, t, d, a, h, hl)) : {Nat.is_lt(_, n(z)) == True{} : Bool}; two.k(n(a), n(z), Nat.sub(n(z), Nat.add(n(a), 1n)), ha, hne2, {==}) : {Nat.is_lt(n(A1(a)), n(z)) == True{} : Bool}}
  %Equal.sym(L32(), RD.BS(len, t, a, z), C.AT(len, t, a) <> RD.BS(len, t, A1(a), z), RD.sl_cons(len, t, d, a, z, h, hzl, ha)) : {_ == C.AT(len, t, a) <> (C.AT(len, t, A1(a)) <> RD.BS(len, t, A1(A1(a)), z)) : L32()}
  %Equal.sym(L32(), RD.BS(len, t, A1(a), z), C.AT(len, t, A1(a)) <> RD.BS(len, t, A1(A1(a)), z), RD.sl_cons(len, t, d, A1(a), z, h, hzl, ha1)) : {C.AT(len, t, a) <> _ == C.AT(len, t, a) <> (C.AT(len, t, A1(a)) <> RD.BS(len, t, A1(A1(a)), z)) : L32()}
  {==}

# ---------------------------------------------------------------------------
# tok: one allele
# ---------------------------------------------------------------------------

def GS(+o: Bool, +nn: Nat, +i: Nat, +s: String) -> String:
  G.GSTR(G.ALLELE(o, nn, i, s))

def GG(+o: Bool, +nn: Nat, +i: Nat, +s: String) -> Bool:
  G.GOK(G.ALLELE(o, nn, i, s))

# A number v: written if it is at most nn (B.Gt.num).
def tok_le(+c5: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +v: U32, +hc5: {Nat.is_le(n(v), nn) == c5 : Bool}, +s0: String,
  +ek: {G.ALLELE(o, nn, i, s0) == TK.NUMG(o, nn, i, n(v)) : B.Got},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok.le(c5, o, i, v, w), m0, GS(o, nn, i, s0), GG(o, nn, i, s0)):
  match c5:
    case True{}:
      +rv = NS.rule(o, i, v)
      +es = {%Equal.sym(B.Got, G.ALLELE(o, nn, i, s0), TK.NUMG(o, nn, i, n(v)), ek) : {NR.chars([rv]) == G.GSTR(_) : String}; %Equal.sym(Bool, Nat.is_le(n(v), nn), True{}, hc5) : {NR.chars([rv]) == G.GSTR(Bool.pick(B.Got, _, B.Got{B.Gt.show(B.Gt.rule(o, i, Some{n(v)}))}, B.Refuse{B.BadGt{}})) : String};
        TK.rule_show(o, i, v) : {NR.chars([rv]) == GS(o, nn, i, s0) : String}}
      +eg = {%Equal.sym(B.Got, G.ALLELE(o, nn, i, s0), TK.NUMG(o, nn, i, n(v)), ek) : {True{} == G.GOK(_) : Bool}; %Equal.sym(Bool, Nat.is_le(n(v), nn), True{}, hc5) : {True{} == G.GOK(Bool.pick(B.Got, _, B.Got{B.Gt.show(B.Gt.rule(o, i, Some{n(v)}))}, B.Refuse{B.BadGt{}})) : Bool};
        {==} : {True{} == GG(o, nn, i, s0) : Bool}}
      S.ws_eq(len, t, NS.ch(w, rv), m0, NR.chars([rv]), GS(o, nn, i, s0), True{}, GG(o, nn, i, s0), es, eg,
        S.ws_ch(len, t, d, hl, rv, TK.rule_lt(o, i, v), w, m0, r))
    case False{}:
      S.ws_fail(len, t, GS(o, nn, i, s0), GG(o, nn, i, s0), w, m0, r)

def SC1(+x: U32) -> String:
  SCon{Chr{x}, SNil{}}

def tok.dg(+c4: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +x: U32, +hc3: {U32.is_eq(x, 46) == False{} : Bool},
  +hc4: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == c4 : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok.digit(c4, o, nn, i, (x - 48 : U32), w), m0, GS(o, nn, i, SC1(x)), GG(o, nn, i, SC1(x))):
  match c4:
    case True{}:
      tok_le(Nat.is_le(n((x - 48 : U32)), nn), len, t, d, hl, o, nn, i, (x - 48 : U32), {==}, SC1(x), TK.alle1(o, nn, i, x, hc3, hc4), w, m0, r)
    case False{}:
      S.ws_fail(len, t, GS(o, nn, i, SC1(x)), GG(o, nn, i, SC1(x)), w, m0, r)

def tok.one(+c3: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +x: U32, +hc3: {U32.is_eq(x, 46) == c3 : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok.one1(c3, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), o, nn, i, x, w), m0, GS(o, nn, i, SC1(x)), GG(o, nn, i, SC1(x))):
  match c3:
    case True{}:
      +xe = U.is_eq_true(x, 46, hc3)
      +es = {%Equal.sym(U32, x, 46, xe) : {NR.chars([46]) == GS(o, nn, i, SC1(_)) : String}; {==} : {NR.chars([46]) == GS(o, nn, i, SC1(x)) : String}}
      +eg = {%Equal.sym(U32, x, 46, xe) : {True{} == GG(o, nn, i, SC1(_)) : Bool}; {==} : {True{} == GG(o, nn, i, SC1(x)) : Bool}}
      S.ws_eq(len, t, NS.ch(w, 46), m0, NR.chars([46]), GS(o, nn, i, SC1(x)), True{}, GG(o, nn, i, SC1(x)), es, eg,
        S.ws_ch(len, t, d, hl, 46, {==}, w, m0, r))
    case False{}:
      tok.dg(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), len, t, d, hl, o, nn, i, x, hc3, {==}, w, m0, r)

def L3(+x: U32, +y: U32, +r: L32()) -> L32():
  Con{x, Con{y, r}}

def tok.zz(+c6: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +x: U32, +y: U32, +r: L32(), +v: U32, +hc6: {U32.is_eq(x, 48) == c6 : Bool},
  +hk: {FD.dec(L3(x, y, r)) == Some{n(v)} : Maybe<&2, Nat>}, -w: NS.Sw, +m0: W.Wm, rr: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok.z(c6, o, nn, i, v, w), m0, GS(o, nn, i, NR.chars(L3(x, y, r))), GG(o, nn, i, NR.chars(L3(x, y, r)))):
  match c6:
    case True{}:
      S.ws_fail(len, t, GS(o, nn, i, NR.chars(L3(x, y, r))), GG(o, nn, i, NR.chars(L3(x, y, r))), w, m0, rr)
    case False{}:
      tok_le(Nat.is_le(n(v), nn), len, t, d, hl, o, nn, i, v, {==}, NR.chars(L3(x, y, r)), TK.allem(o, nn, i, x, y, r, n(v), hc6, hk), w, m0, rr)

def tok.mm(+mv: Maybe<&2, U32>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +x: U32, +y: U32, +r: L32(), +bd: Nat,
  +hv: {FD.nat_of(mv) == FD.decb(L3(x, y, r), bd) : Maybe<&2, Nat>}, -w: NS.Sw, +m0: W.Wm, rr: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok.m(mv, U32.is_eq(x, 48), o, nn, i, w), m0, GS(o, nn, i, NR.chars(L3(x, y, r))), GG(o, nn, i, NR.chars(L3(x, y, r)))):
  match mv:
    case Some{+v}:
      tok.zz(U32.is_eq(x, 48), len, t, d, hl, o, nn, i, x, y, r, v, {==},
        TK.decb_some(L3(x, y, r), n(v), bd, Equal.sym(Maybe<&2, Nat>, Some{n(v)}, FD.decb(L3(x, y, r), bd), hv)), w, m0, rr)
    case None{}:
      S.ws_fail(len, t, GS(o, nn, i, NR.chars(L3(x, y, r))), GG(o, nn, i, NR.chars(L3(x, y, r))), w, m0, rr)

def NV(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> Maybe<&2, U32>:
  Pair.snd(D.Bytes, Maybe<&2, U32>, FC.num(C.BT(len, t), a, z))

# lawful-fields' num_view with its bound named (2^32 in unary must not be
# written out by the checker).
def nv_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat},
  +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {FD.nat_of(NV(len, t, a, z)) == FD.decb(RD.BS(len, t, a, z), bd) : Maybe<&2, Nat>}:
  LN.nvt(len, t, d, a, z, bd, U32.to_nat(429496729), hbd, {==}, LN.QM(bd, hbd), hl, AL.le_u(a, z, haz), hzl)


def tok.multi(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +ha: {Nat.is_lt(n(a), n(z)) == True{} : Bool},
  +hne: {U32.is_eq((z - a : U32), 1) == False{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}) ->
  S.WS(len, t, NS.tok.many(False{}, o, nn, i, a, z, C.AT(len, t, a), C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z))):
  +x = C.AT(len, t, a)
  +y = C.AT(len, t, A1(a))
  +r = RD.BS(len, t, A1(A1(a)), z)
  +haz = W.pv_a(len, a, z, hpz)
  +hzl = W.pv_z(len, a, z, hpz)
  +eB = tx2(len, t, d, a, z, hl, hzl, ha, hne)
  +eT = Equal.trans(String, TXR(len, t, a, z), NR.chars(RD.BS(len, t, a, z)), NR.chars(L3(x, y, r)), RD.tx_eq(len, t, a, z, haz),
    Equal.cong(L32(), String, xs => NR.chars(xs), RD.BS(len, t, a, z), L3(x, y, r), eB))
  +hv = {%eB : {FD.nat_of(NV(len, t, a, z)) == FD.decb(_, bd) : Maybe<&2, Nat>};
    nv_view(len, t, d, a, z, bd, hbd, hl, haz, hzl) : {FD.nat_of(NV(len, t, a, z)) == FD.decb(L3(x, y, r), bd) : Maybe<&2, Nat>}}
  %Equal.sym(D.Bytes & Maybe<&2, U32>, FC.num(C.BT(len, t), a, z), (C.BT(len, t), NV(len, t, a, z)), FL.num_pair(C.BT(len, t), a, z)) :
    S.WS(len, t, NS.tok.d(_, U32.is_eq(x, 48), o, nn, i, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z)))
  %Equal.sym(String, TXR(len, t, a, z), NR.chars(L3(x, y, r)), eT) :
    S.WS(len, t, NS.tok.d((C.BT(len, t), NV(len, t, a, z)), U32.is_eq(x, 48), o, nn, i, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, GS(o, nn, i, _), GG(o, nn, i, _))
  tok.mm(NV(len, t, a, z), len, t, d, hl, o, nn, i, x, y, r, bd, hv,
    NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp))

def tok.single(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hc2: {U32.is_eq((z - a : U32), 1) == True{} : Bool}) ->
  S.WS(len, t, NS.tok.many(True{}, o, nn, i, a, z, C.AT(len, t, a), C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z))):
  +x = C.AT(len, t, a)
  %Equal.sym(String, TXR(len, t, a, z), SC1(x), tx1(len, t, d, a, z, hl, hpz, hc2)) :
    S.WS(len, t, NS.tok.many(True{}, o, nn, i, a, z, x, C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, GS(o, nn, i, _), GG(o, nn, i, _))
  tok.one(U32.is_eq(x, 46), len, t, d, hl, o, nn, i, x, {==}, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp))

def tok.c2(+c2: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +ha: {Nat.is_lt(n(a), n(z)) == True{} : Bool},
  +hc2: {U32.is_eq((z - a : U32), 1) == c2 : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}) ->
  S.WS(len, t, NS.tok.many(c2, o, nn, i, a, z, C.AT(len, t, a), C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z))):
  match c2:
    case True{}:
      tok.single(len, t, d, hl, o, nn, i, a, z, l2, t2, p, ok, h, hp, hpz, hc2)
    case False{}:
      tok.multi(len, t, d, hl, o, nn, i, a, z, l2, t2, p, ok, h, hp, hpz, ha, hc2, bd, hbd)

def tok.c1(+c1: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +hc1: {U32.is_le(z, a) == c1 : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}) ->
  S.WS(len, t, NS.tok.e(c1, o, nn, i, a, z, C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z))):
  match c1:
    case True{}:
      S.ws_fail(len, t, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z)), NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp))
    case False{}:
      +ha = N.not_le_lt(n(z), n(a), Equal.trans(Bool, Nat.is_le(n(z), n(a)), U32.is_le(z, a), False{}, Equal.sym(Bool, U32.is_le(z, a), Nat.is_le(n(z), n(a)), U.is_le_to_nat(z, a)), hc1))
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), a), (C.BT(len, t), C.AT(len, t, a)), C.at_pair_t(len, t, a)) :
        S.WS(len, t, NS.tok.x(o, nn, i, a, z, _, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z)))
      tok.c2(U32.is_eq((z - a : U32), 1), len, t, d, hl, o, nn, i, a, z, l2, t2, p, ok, h, hp, hpz, ha, {==}, bd, hbd)

# One allele a .. z-1 of a genotype: what B.Gt.allele gives.
def tok_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok(w, o, nn, i, a, z), m0, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z))):
  S.ws_at(len, t, w, v => NS.tok(v, o, nn, i, a, z), m0, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z)), r,
    +l2 => +t2 => +p => +ok => +h => +hp => tok.c1(U32.is_le(z, a), len, t, d, hl, o, nn, i, a, z, l2, t2, p, ok, h, hp, hpz, {==}, bd, hbd))

# ---------------------------------------------------------------------------
# The first separator ('/' or '|') of a genotype
# ---------------------------------------------------------------------------

def J2(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find2(C.BT(len, t), a, z, 47, 124))

def F2V(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> Nat:
  D.first2(X(len, t), n(a), n(z), 47, 124)

def j2_val(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {n(J2(len, t, a, z)) == F2V(len, t, a, z) : Nat}:
  CP.f2_view(len, t, d, a, z, 47, 124, h, AL.le_u(a, z, haz), hzl, {==}, {==})

def j2_range(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {Bool.and(Nat.is_le(n(a), n(J2(len, t, a, z))), Nat.is_le(n(J2(len, t, a, z)), n(z))) == True{} : Bool}:
  %Equal.sym(Nat, n(J2(len, t, a, z)), F2V(len, t, a, z), j2_val(len, t, d, a, z, h, haz, hzl)) : {Bool.and(Nat.is_le(n(a), _), Nat.is_le(_, n(z))) == True{} : Bool}
  BL.first2_range(X(len, t), n(a), n(z), 47, 124, haz, %AL.len_x(len, t, d, h) : {Nat.is_le(n(z), _) == True{} : Bool}; hzl)

def is_sep_at(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hj: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hh: {D.has2(X(len, t), n(j), 47, 124) == True{} : Bool}) -> {B.Gt.is_sep(Chr{C.AT(len, t, j)}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, X(len, t), n(j)),
    C.at_view_t(len, t, d, j, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hj)) :
    {Bool.or(D.is_some(_, 47), D.is_some(_, 124)) == True{} : Bool}
  hh

def j2_hit(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(J2(len, t, a, z)), n(z)) == True{} : Bool}) -> {B.Gt.is_sep(Chr{C.AT(len, t, J2(len, t, a, z))}) == True{} : Bool}:
  +j = J2(len, t, a, z)
  +ev = j2_val(len, t, d, a, z, h, haz, hzl)
  is_sep_at(len, t, d, j, h, N.lt_le_trans(n(j), n(z), n(len), hlt, hzl),
    %Equal.sym(Nat, n(j), F2V(len, t, a, z), ev) : {D.has2(X(len, t), _, 47, 124) == True{} : Bool};
    BL.first2_hit(X(len, t), n(a), n(z), 47, 124, haz, %AL.len_x(len, t, d, h) : {Nat.is_le(n(z), _) == True{} : Bool}; hzl, %ev : {Nat.is_lt(_, n(z)) == True{} : Bool}; hlt))

law nosep_take:
  for +ys: L32()
  {G.NOSEP(NR.chars(List.take(&2, U32, ys, D.run_len2(ys, 47, 124)))) == True{} : Bool}

def nt.k(+b: Bool, +y: U32, +r: L32(), +eb: {Bool.or(U32.is_eq(y, 47), U32.is_eq(y, 124)) == b : Bool},
  +ih: {G.NOSEP(NR.chars(List.take(&2, U32, r, D.run_len2(r, 47, 124)))) == True{} : Bool}) ->
  {G.NOSEP(NR.chars(List.take(&2, U32, Con{y, r}, Bool.pick(Nat, b, 0n, Nat.add(1n, D.run_len2(r, 47, 124)))))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Bool.or(U32.is_eq(y, 47), U32.is_eq(y, 124)), False{}, eb) : {Bool.and(Bool.not(_), G.NOSEP(NR.chars(List.take(&2, U32, r, D.run_len2(r, 47, 124))))) == True{} : Bool}
      ih

def nosep_take(ys):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      nt.k(Bool.or(U32.is_eq(y, 47), U32.is_eq(y, 124)), y, r, {==}, nosep_take(r))

def Y2(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> L32():
  D.slice(X(len, t), n(a), Nat.sub(n(z), n(a)))

# The bytes before the first separator hold none.
def nosep_pre(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {G.NOSEP(TXR(len, t, a, J2(len, t, a, z))) == True{} : Bool}:
  +j = J2(len, t, a, z)
  +Y = Y2(len, t, a, z)
  +R = D.run_len2(Y, 47, 124)
  +L = List.drop(&2, U32, X(len, t), n(a))
  +hr = N.and_true_l(Nat.is_le(n(a), n(j)), Nat.is_le(n(j), n(z)), j2_range(len, t, d, a, z, h, haz, hzl))
  +hjz = N.and_true_r(Nat.is_le(n(a), n(j)), Nat.is_le(n(j), n(z)), j2_range(len, t, d, a, z, h, haz, hzl))
  +hR = N.le_sub_r(n(a), R, n(z), %j2_val(len, t, d, a, z, h, haz, hzl) : {Nat.is_le(_, n(z)) == True{} : Bool}; hjz)
  %Equal.sym(String, TXR(len, t, a, j), NR.chars(D.slice(X(len, t), n(a), Nat.sub(n(j), n(a)))), RD.tx_eq(len, t, a, j, hr)) :
    {G.NOSEP(_) == True{} : Bool}
  %Equal.sym(Nat, n(j), Nat.add(n(a), R), j2_val(len, t, d, a, z, h, haz, hzl)) :
    {G.NOSEP(NR.chars(D.slice(X(len, t), n(a), Nat.sub(_, n(a))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(n(a), R), n(a)), R, N.sub_add_l(n(a), R)) :
    {G.NOSEP(NR.chars(D.slice(X(len, t), n(a), _))) == True{} : Bool}
  %Q.take_take(L, Nat.sub(n(z), n(a)), R, hR) : {G.NOSEP(NR.chars(_)) == True{} : Bool}
  nosep_take(Y)

def nosep_all(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +he: {U32.is_eq(J2(len, t, a, z), z) == True{} : Bool}) -> {G.NOSEP(TXR(len, t, a, z)) == True{} : Bool}:
  %U.is_eq_true(J2(len, t, a, z), z, he) : {G.NOSEP(TXR(len, t, a, _)) == True{} : Bool}
  nosep_pre(len, t, d, a, z, h, haz, hzl)

# The text at a separator j (a <= j < z): before it, the separator, after it.
def txr_sep(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +haj: {Nat.is_le(n(a), n(j)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool}, +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}) ->
  {TXR(len, t, a, z) == String.append(TXR(len, t, a, j), SCon{Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z)}) : String}:
  +hjl = N.lt_le_trans(n(j), n(z), n(len), hjz, hzl)
  +hju = Equal.trans(Bool, U32.is_lt(j, len), Nat.is_lt(n(j), n(len)), True{}, U.is_lt_to_nat(j, len), hjl)
  +ej1 = AL.inc_len(len, t, d, j, h, hjl)
  +h1 = {%Equal.sym(Nat, n(A1(j)), Nat.add(n(j), 1n), ej1) : {Nat.is_le(n(j), _) == True{} : Bool}; N.le_add_r(n(j), 1n) : {Nat.is_le(n(j), n(A1(j))) == True{} : Bool}}
  +h2 = SC.j1_le(len, t, d, j, z, h, hzl, hjz)
  %Equal.sym(String, NR.chars(W.SL(len, t, a, z)), String.append(NR.chars(W.SL(len, t, a, j)), NR.chars(W.SL(len, t, j, z))), WT.tx_app(len, t, a, j, z, haj, N.lt_to_le(n(j), n(z), hjz))) : {_ == String.append(TXR(len, t, a, j), SCon{Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z)}) : String}
  %Equal.sym(String, NR.chars(W.SL(len, t, j, z)), String.append(NR.chars(W.SL(len, t, j, A1(j))), NR.chars(W.SL(len, t, A1(j), z))), WT.tx_app(len, t, j, A1(j), z, h1, h2)) : {String.append(TXR(len, t, a, j), _) == String.append(TXR(len, t, a, j), SCon{Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z)}) : String}
  %Equal.sym(L32(), W.SL(len, t, j, A1(j)), [C.AT(len, t, j)], WT.sl_one(len, t, d, j, h, hju)) : {String.append(TXR(len, t, a, j), String.append(NR.chars(_), NR.chars(W.SL(len, t, A1(j), z)))) == String.append(TXR(len, t, a, j), SCon{Chr{C.AT(len, t, j)}, TXR(len, t, A1(j), z)}) : String}
  {==}

def cat_nil(+A: B.Got, +hA: {G.GOK(A) == True{} : Bool}) -> ({G.GOK(G.CAT(A, B.Got{""})) == True{} : Bool} & {G.GSTR(A) == G.GSTR(G.CAT(A, B.Got{""})) : String}):
  match A:
    case B.Got{+s}:
      ({==}, Equal.sym(String, String.append(s, ""), s, MN.str_nil(s)))
    case B.Refuse{+c}:
      Empty.absurd({G.GOK(G.CAT(B.Refuse{c}, B.Got{""})) == True{} : Bool} & {G.GSTR(B.Refuse{c}) == G.GSTR(G.CAT(B.Refuse{c}, B.Got{""})) : String}, P.false_ne_true(hA))

def cat2(+A: B.Got, +s: String, +Bg: B.Got, +hA: {G.GOK(A) == True{} : Bool}, +hB: {G.GOK(Bg) == True{} : Bool}) ->
  ({G.GOK(G.CAT(A, G.CAT(B.Got{s}, Bg))) == True{} : Bool} & {String.append(G.GSTR(A), String.append(s, G.GSTR(Bg))) == G.GSTR(G.CAT(A, G.CAT(B.Got{s}, Bg))) : String}):
  match A Bg:
    case B.Got{+x} B.Got{+y}:
      ({==}, {==})
    case B.Got{+x} B.Refuse{+c}:
      Empty.absurd({G.GOK(G.CAT(B.Got{x}, G.CAT(B.Got{s}, B.Refuse{c}))) == True{} : Bool} & {String.append(x, String.append(s, "")) == G.GSTR(G.CAT(B.Got{x}, G.CAT(B.Got{s}, B.Refuse{c}))) : String}, P.false_ne_true(hB))
    case B.Refuse{+c} _:
      Empty.absurd({G.GOK(G.CAT(B.Refuse{c}, G.CAT(B.Got{s}, Bg))) == True{} : Bool} & {String.append("", String.append(s, G.GSTR(Bg))) == G.GSTR(G.CAT(B.Refuse{c}, G.CAT(B.Got{s}, Bg))) : String}, P.false_ne_true(hA))

# ---------------------------------------------------------------------------
# gt: a genotype (B.Gt.split)
# ---------------------------------------------------------------------------

def SPS(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  G.GSTR(G.SPLIT(o, nn, i, TXR(len, t, a, z)))

def SPG(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> Bool:
  G.GOK(G.SPLIT(o, nn, i, TXR(len, t, a, z)))

def gl_done(+q: Nat, -w: NS.Sw, +a: U32, +z: U32, +o: Bool, +nn: Nat, +i: Nat) ->
  {NS.gt.loop(q, NS.Gs{w, a, z, True{}}, o, nn, i) == NS.Gs{w, a, z, True{}} : NS.Gs}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def gl.k(+A: B.Got, +Sp: B.Got, +es: {Sp == G.CAT(A, B.Got{""}) : B.Got},
  q: {G.GOK(G.CAT(A, B.Got{""})) == True{} : Bool} & {G.GSTR(A) == G.GSTR(G.CAT(A, B.Got{""})) : String}) ->
  ({G.GOK(Sp) == True{} : Bool} & {G.GSTR(A) == G.GSTR(Sp) : String}):
  (hg, ht) = q
  ({%Equal.sym(B.Got, Sp, G.CAT(A, B.Got{""}), es) : {G.GOK(_) == True{} : Bool}; hg : {G.GOK(Sp) == True{} : Bool}}, {%Equal.sym(B.Got, Sp, G.CAT(A, B.Got{""}), es) : {G.GSTR(A) == G.GSTR(_) : String}; ht : {G.GSTR(A) == G.GSTR(Sp) : String}})

# The last allele: no separator left.
def gt.last(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hns: {G.NOSEP(TXR(len, t, a, z)) == True{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.tok(w, o, nn, i, a, z), m0, SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z)):
  +A = G.ALLELE(o, nn, i, TXR(len, t, a, z))
  +es = G.split_nosep(o, nn, i, TXR(len, t, a, z), hns)
  S.ws_imp(len, t, NS.tok(w, o, nn, i, a, z), m0, GS(o, nn, i, TXR(len, t, a, z)), GG(o, nn, i, TXR(len, t, a, z)), SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z),
    hg => gl.k(A, G.SPLIT(o, nn, i, TXR(len, t, a, z)), es, cat_nil(A, hg)),
    tok_t(len, t, d, hl, o, nn, i, a, z, hpz, bd, hbd, w, m0, r))

def gs.k(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +a: U32, +j: U32, +z: U32, +x: U32,
  +eS: {G.SPLIT(o, nn, i, TXR(len, t, a, z)) == G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z)))) : B.Got},
  q: {G.GOK(G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z))))) == True{} : Bool} &
     {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(SCon{Chr{x}, SNil{}}, SPS(o, nn, i, len, t, A1(j), z))) == G.GSTR(G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z))))) : String}) ->
  ({SPG(o, nn, i, len, t, a, z) == True{} : Bool} & {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(SCon{Chr{x}, SNil{}}, SPS(o, nn, i, len, t, A1(j), z))) == SPS(o, nn, i, len, t, a, z) : String}):
  (hg, ht) = q
  +R = G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z))))
  ({%Equal.sym(B.Got, G.SPLIT(o, nn, i, TXR(len, t, a, z)), R, eS) : {G.GOK(_) == True{} : Bool}; hg : {SPG(o, nn, i, len, t, a, z) == True{} : Bool}},
   {%Equal.sym(B.Got, G.SPLIT(o, nn, i, TXR(len, t, a, z)), R, eS) : {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(SCon{Chr{x}, SNil{}}, SPS(o, nn, i, len, t, A1(j), z))) == G.GSTR(_) : String}; ht : {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(SCon{Chr{x}, SNil{}}, SPS(o, nn, i, len, t, A1(j), z))) == SPS(o, nn, i, len, t, a, z) : String}})

# At a separator j: the allele before it, the separator, the rest.
def gt.sep_k(+o: Bool, +nn: Nat, +i: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +j: U32, +z: U32, +haj: {Nat.is_le(n(a), n(j)) == True{} : Bool}, +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hns: {G.NOSEP(TXR(len, t, a, j)) == True{} : Bool}, +hsep: {B.Gt.is_sep(Chr{C.AT(len, t, j)}) == True{} : Bool},
  +hg: {Bool.and(GG(o, nn, i, TXR(len, t, a, j)), Bool.and(True{}, SPG(o, nn, i, len, t, A1(j), z))) == True{} : Bool}) ->
  ({SPG(o, nn, i, len, t, a, z) == True{} : Bool} & {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(WT.TX(len, t, NS.Rg{j, A1(j)}), SPS(o, nn, i, len, t, A1(j), z))) == SPS(o, nn, i, len, t, a, z) : String}):
  +x = C.AT(len, t, j)
  +hju = Equal.trans(Bool, U32.is_lt(j, len), Nat.is_lt(n(j), n(len)), True{}, U.is_lt_to_nat(j, len), N.lt_le_trans(n(j), n(z), n(len), hjz, hzl))
  +eS = {%Equal.sym(String, TXR(len, t, a, z), String.append(TXR(len, t, a, j), SCon{Chr{x}, TXR(len, t, A1(j), z)}), txr_sep(len, t, d, a, j, z, hl, haj, hjz, hzl)) : {G.SPLIT(o, nn, i, _) == G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z)))) : B.Got};
    G.split_sep(o, nn, i, TXR(len, t, a, j), Chr{x}, TXR(len, t, A1(j), z), hns, hsep) :
    {G.SPLIT(o, nn, i, TXR(len, t, a, z)) == G.CAT(G.ALLELE(o, nn, i, TXR(len, t, a, j)), G.CAT(B.Got{SCon{Chr{x}, SNil{}}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z)))) : B.Got}}
  +hA = N.and_true_l(GG(o, nn, i, TXR(len, t, a, j)), Bool.and(True{}, SPG(o, nn, i, len, t, A1(j), z)), hg)
  +hB = N.and_true_r(GG(o, nn, i, TXR(len, t, a, j)), Bool.and(True{}, SPG(o, nn, i, len, t, A1(j), z)), hg)
  %Equal.sym(L32(), W.SL(len, t, j, A1(j)), [x], WT.sl_one(len, t, d, j, hl, hju)) :
    ({SPG(o, nn, i, len, t, a, z) == True{} : Bool} & {String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(NR.chars(_), SPS(o, nn, i, len, t, A1(j), z))) == SPS(o, nn, i, len, t, a, z) : String})
  gs.k(o, nn, i, len, t, a, j, z, x, eS, cat2(G.ALLELE(o, nn, i, TXR(len, t, a, j)), SCon{Chr{x}, SNil{}}, G.SPLIT(o, nn, i, TXR(len, t, A1(j), z)), hA, hB))

def SW0(+len: U32, +t: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool) -> NS.Sw:
  NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}

def WM0(+l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool) -> W.Wm:
  W.Wm{W.V(l2, t2), p, ok}

def gt.e(+e: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hm: {Nat.is_lt(n(z), Nat.add(n(a), 1n+q)) == True{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +he: {U32.is_eq(J2(len, t, a, z), z) == e : Bool},
  ih: @+m2: W.Wm -> W.Rel(len, t, NS.cpr(NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, J2(len, t, a, z)), NS.Rg{J2(len, t, a, z), A1(J2(len, t, a, z))}), m2) ->
    {W.PV(len, NS.Rg{A1(J2(len, t, a, z)), z}) == True{} : Bool} -> {Nat.is_lt(n(z), Nat.add(n(A1(J2(len, t, a, z))), q)) == True{} : Bool} ->
    S.WS(len, t, NS.gt.fin(NS.gt.loop(q, NS.Gs{NS.cpr(NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, J2(len, t, a, z)), NS.Rg{J2(len, t, a, z), A1(J2(len, t, a, z))}), A1(J2(len, t, a, z)), z, False{}}, o, nn, i)),
      m2, SPS(o, nn, i, len, t, A1(J2(len, t, a, z)), z), SPG(o, nn, i, len, t, A1(J2(len, t, a, z)), z))) ->
  S.WS(len, t, NS.gt.fin(NS.gt.loop(q, NS.gt.if(e, o, nn, i, a, J2(len, t, a, z), z, SW0(len, t, l2, t2, p, ok)), o, nn, i)), WM0(l2, t2, p, ok),
    SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z)):
  match e:
    case True{}:
      +haz = W.pv_a(len, a, z, hpz)
      +hzl = W.pv_z(len, a, z, hpz)
      %Equal.sym(NS.Gs, NS.gt.loop(q, NS.Gs{NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, z), a, z, True{}}, o, nn, i), NS.Gs{NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, z), a, z, True{}},
        gl_done(q, NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, z), a, z, o, nn, i)) :
        S.WS(len, t, NS.gt.fin(_), WM0(l2, t2, p, ok), SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z))
      gt.last(len, t, d, hl, o, nn, i, a, z, hpz, nosep_all(len, t, d, a, z, hl, haz, hzl, he), bd, hbd,
        SW0(len, t, l2, t2, p, ok), WM0(l2, t2, p, ok), W.refl(len, l2, t, t2, p, ok, h, hp))
    case False{}:
      +haz = W.pv_a(len, a, z, hpz)
      +hzl = W.pv_z(len, a, z, hpz)
      +j = J2(len, t, a, z)
      +j1 = A1(j)
      +haj = N.and_true_l(Nat.is_le(n(a), n(j)), Nat.is_le(n(j), n(z)), j2_range(len, t, d, a, z, hl, haz, hzl))
      +hjz = SC.lt_of(j, z, N.and_true_r(Nat.is_le(n(a), n(j)), Nat.is_le(n(j), n(z)), j2_range(len, t, d, a, z, hl, haz, hzl)), he)
      +hjl = N.lt_le_trans(n(j), n(z), n(len), hjz, hzl)
      +ej1 = AL.inc_len(len, t, d, j, hl, hjl)
      +hj1z = SC.j1_le(len, t, d, j, z, hl, hzl, hjz)
      +hpj = W.pv_mk(len, a, j, haj, N.lt_to_le(n(j), n(len), hjl))
      +hps = W.pv_mk(len, j, j1, {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej1) : {Nat.is_le(n(j), _) == True{} : Bool}; N.le_add_r(n(j), 1n) : {Nat.is_le(n(j), n(j1)) == True{} : Bool}}, N.le_trans(n(j1), n(z), n(len), hj1z, hzl))
      +hpr = W.pv_mk(len, j1, z, hj1z, hzl)
      +hm2 = {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej1) : {Nat.is_lt(n(z), Nat.add(_, q)) == True{} : Bool}; SC.fuel_step(n(a), n(j), n(z), q, haj, hm) : {Nat.is_lt(n(z), Nat.add(n(j1), q)) == True{} : Bool}}
      -sw = SW0(len, t, l2, t2, p, ok)
      -tk = NS.tok(sw, o, nn, i, a, j)
      +sep = {NS.Rg{j, j1} : NS.Rg}
      S.ws_imp(len, t, NS.gt.fin(NS.gt.loop(q, NS.Gs{NS.cpr(tk, sep), j1, z, False{}}, o, nn, i)), WM0(l2, t2, p, ok),
        String.append(GS(o, nn, i, TXR(len, t, a, j)), String.append(WT.TX(len, t, sep), SPS(o, nn, i, len, t, j1, z))),
        Bool.and(GG(o, nn, i, TXR(len, t, a, j)), Bool.and(True{}, SPG(o, nn, i, len, t, j1, z))),
        SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z),
        hg => gt.sep_k(o, nn, i, len, t, d, hl, a, j, z, haj, hjz, hzl, nosep_pre(len, t, d, a, z, hl, haz, hzl), j2_hit(len, t, d, a, z, hl, haz, hzl, hjz), hg),
        S.ws_seq(len, t, tk, v => NS.gt.fin(NS.gt.loop(q, NS.Gs{NS.cpr(v, sep), j1, z, False{}}, o, nn, i)), WM0(l2, t2, p, ok),
          GS(o, nn, i, TXR(len, t, a, j)), String.append(WT.TX(len, t, sep), SPS(o, nn, i, len, t, j1, z)),
          GG(o, nn, i, TXR(len, t, a, j)), Bool.and(True{}, SPG(o, nn, i, len, t, j1, z)),
          tok_t(len, t, d, hl, o, nn, i, a, j, hpj, bd, hbd, sw, WM0(l2, t2, p, ok), W.refl(len, l2, t, t2, p, ok, h, hp)),
          +m1 => r1 => S.ws_seq(len, t, NS.cpr(tk, sep), v => NS.gt.fin(NS.gt.loop(q, NS.Gs{v, j1, z, False{}}, o, nn, i)), m1,
            WT.TX(len, t, sep), SPS(o, nn, i, len, t, j1, z), True{}, SPG(o, nn, i, len, t, j1, z),
            S.ws_cpr(len, t, d, hl, sep, hps, tk, m1, r1),
            +m2 => r2 => ih(m2, r2, hpr, hm2))))

def gt.in(+q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hm: {Nat.is_lt(n(z), Nat.add(n(a), 1n+q)) == True{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  ih: @+m2: W.Wm -> W.Rel(len, t, NS.cpr(NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, J2(len, t, a, z)), NS.Rg{J2(len, t, a, z), A1(J2(len, t, a, z))}), m2) ->
    {W.PV(len, NS.Rg{A1(J2(len, t, a, z)), z}) == True{} : Bool} -> {Nat.is_lt(n(z), Nat.add(n(A1(J2(len, t, a, z))), q)) == True{} : Bool} ->
    S.WS(len, t, NS.gt.fin(NS.gt.loop(q, NS.Gs{NS.cpr(NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, J2(len, t, a, z)), NS.Rg{J2(len, t, a, z), A1(J2(len, t, a, z))}), A1(J2(len, t, a, z)), z, False{}}, o, nn, i)),
      m2, SPS(o, nn, i, len, t, A1(J2(len, t, a, z)), z), SPG(o, nn, i, len, t, A1(J2(len, t, a, z)), z))) ->
  S.WS(len, t, NS.gt.fin(NS.gt.loop(q, NS.gt.step(o, nn, i, SW0(len, t, l2, t2, p, ok), a, z), o, nn, i)), WM0(l2, t2, p, ok),
    SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z)):
  %Equal.sym(D.Bytes & U32, F.find2(C.BT(len, t), a, z, 47, 124), (C.BT(len, t), J2(len, t, a, z)), FE.find2_pair(C.BT(len, t), a, z, 47, 124)) :
    S.WS(len, t, NS.gt.fin(NS.gt.loop(q, NS.gt.next(o, nn, i, a, z, _, C.BT(l2, t2), p, ok), o, nn, i)), WM0(l2, t2, p, ok), SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z))
  gt.e(U32.is_eq(J2(len, t, a, z), z), q, len, t, d, hl, o, nn, i, a, z, hpz, hm, bd, hbd, l2, t2, p, ok, h, hp, {==}, ih)

law gt_go:
  for +m: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +o: Bool
  for +nn: Nat
  for +i: Nat
  for +a: U32
  for +z: U32
  for +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}
  for +hm: {Nat.is_lt(n(z), Nat.add(n(a), m)) == True{} : Bool}
  for +bd: Nat
  for +hbd: {Nat.pow(2n, 32n) == bd : Nat}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.gt.fin(NS.gt.loop(m, NS.Gs{w, a, z, False{}}, o, nn, i)), m0, SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z))

def gt_go(m, len, t, d, hl, o, nn, i, a, z, hpz, hm, bd, hbd, w, m0, r):
  match m:
    case 0n:
      SC.no_fuel(S.WS(len, t, NS.gt.fin(NS.gt.loop(0n, NS.Gs{w, a, z, False{}}, o, nn, i)), m0, SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z)),
        n(a), n(z), W.pv_a(len, a, z, hpz), hm)
    case 1n+(+q):
      S.ws_at(len, t, w, v => NS.gt.fin(NS.gt.loop(q, NS.gt.step(o, nn, i, v, a, z), o, nn, i)), m0, SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z), r,
        +l2 => +t2 => +p => +ok => +h => +hp => gt.in(q, len, t, d, hl, o, nn, i, a, z, hpz, hm, bd, hbd, l2, t2, p, ok, h, hp,
          +m2 => r2 => hh => hq => gt_go(q, len, t, d, hl, o, nn, i, A1(J2(len, t, a, z)), z, hh, hq, bd, hbd,
            NS.cpr(NS.tok(SW0(len, t, l2, t2, p, ok), o, nn, i, a, J2(len, t, a, z)), NS.Rg{J2(len, t, a, z), A1(J2(len, t, a, z))}), m2, r2)))

# A genotype x in the record for ALT i of nn: what B.Gt.split gives.
def gt_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +o: Bool, +nn: Nat, +i: Nat, +a: U32, +z: U32, +hpz: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.gt(w, o, nn, i, NS.Rg{a, z}), m0, SPS(o, nn, i, len, t, a, z), SPG(o, nn, i, len, t, a, z)):
  gt_go(1n+n((z - a : U32)), len, t, d, hl, o, nn, i, a, z, hpz, SC.fuel0(a, z, W.pv_a(len, a, z, hpz)), bd, hbd, w, m0, r)
