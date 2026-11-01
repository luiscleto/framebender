import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_cut.bend as K
import ./proof_s_gtspec.bend as G
import ./proof_s_kinds.bend as KD
import ./proof_s_info.bend as IF
import ./proof_s_fmt.bend as FM
import ./norm_seq.bend as Norm
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A record of a split line (norm_split.bend's samples, rec.tail, record)
# writes what B.Rec.piece gives, followed by the line's terminator. Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def Ss() -> Data:
  List<&2, String>

def Rgs() -> Data:
  List<&2, NS.Rg>

def Tags() -> Data:
  List<&2, B.Tag>

# ---------------------------------------------------------------------------
# The samples (fields 9 on)
# ---------------------------------------------------------------------------

def FSL(+len: U32, +t: AT.Tree<U32>, +tags: Tags(), +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, cols: Rgs()) -> G.Gs():
  match cols:
    case Nil{}:
      Nil{}
    case Con{NS.Rg{+a, +z}, r}:
      Con{FM.FS(len, t, tags, kss, o, nalt, i, a, z), FSL(len, t, tags, kss, o, nalt, i, r)}

def pv_lt(+len: U32, +bb: U32, +a: U32, +z: U32, +hp: {W.PV(bb, NS.Rg{a, z}) == True{} : Bool}, +hb: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}) ->
  {Nat.is_lt(n(z), n(len)) == True{} : Bool}:
  N.le_lt_trans(n(z), n(bb), n(len), W.pv_z(bb, a, z, hp), hb)

def pv_up(+len: U32, +bb: U32, +a: U32, +z: U32, +hp: {W.PV(bb, NS.Rg{a, z}) == True{} : Bool}, +hb: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}) ->
  {W.PV(len, NS.Rg{a, z}) == True{} : Bool}:
  W.pv_mk(len, a, z, W.pv_a(bb, a, z, hp), N.lt_to_le(n(z), n(len), pv_lt(len, bb, a, z, hp, hb)))

law samples_t:
  for +cols: Rgs()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +tags: Tags()
  for +kss: Ss()
  for +o: Bool
  for +nalt: Nat
  for +i: Nat
  for +bb: U32
  for +hpc: {K.ALLPV(bb, cols) == True{} : Bool}
  for +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}
  for +bd: Nat
  for +hbd: {Nat.pow(2n, 32n) == bd : Nat}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.samples(cols, w, KD.MAPF(tags, kss), o, nalt, i), m0, G.JT(FSL(len, t, tags, kss, o, nalt, i, cols), False{}, "\t"), G.JG(FSL(len, t, tags, kss, o, nalt, i, cols)))

def samples_t(cols, len, t, d, hl, tags, kss, o, nalt, i, bb, hpc, hbl, bd, hbd, w, m0, r):
  match cols:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{NS.Rg{+a, +z}, +rr}:
      +hp = N.and_true_l(W.PV(bb, NS.Rg{a, z}), K.ALLPV(bb, rr), hpc)
      +hr = N.and_true_r(W.PV(bb, NS.Rg{a, z}), K.ALLPV(bb, rr), hpc)
      +g = FM.FS(len, t, tags, kss, o, nalt, i, a, z)
      +R = FSL(len, t, tags, kss, o, nalt, i, rr)
      -cw = NS.ch(w, 9)
      S.ws_seq(len, t, cw, v => NS.samples(rr, NS.sample(v, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), KD.MAPF(tags, kss), o, nalt, i), m0,
        NR.chars([9]), String.append(G.GSTR(g), G.JT(R, False{}, "\t")), True{}, Bool.and(G.GOK(g), G.JG(R)),
        S.ws_ch(len, t, d, hl, 9, {==}, w, m0, r),
        +m1 => r1 => S.ws_seq(len, t, NS.sample(cw, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), v => NS.samples(rr, v, KD.MAPF(tags, kss), o, nalt, i), m1,
          G.GSTR(g), G.JT(R, False{}, "\t"), G.GOK(g), G.JG(R),
          FM.sample_t(len, t, d, hl, tags, kss, o, nalt, i, a, z, AL.le_u(a, z, W.pv_a(bb, a, z, hp)), pv_lt(len, bb, a, z, hp, hbl), bd, hbd, cw, m1, r1),
          +m2 => r2 => samples_t(rr, len, t, d, hl, tags, kss, o, nalt, i, bb, hr, hbl, bd, hbd, NS.sample(cw, KD.MAPF(tags, kss), NS.Rg{a, z}, o, nalt, i), m2, r2)))

# ---------------------------------------------------------------------------
# B.Rec.piece.go from field 9 on: each a sample (B.Fmt.split)
# ---------------------------------------------------------------------------

def DF(+defs: B.Defs) -> Tags():
  B.Defs.fmt(defs)

def DI(+defs: B.Defs) -> Tags():
  B.Defs.info(defs)

def gne.k(+b: Bool, +j: Nat, +c: Nat, +h: {Nat.is_le(9n, j) == True{} : Bool}, +hc: {Nat.is_lt(c, 9n) == True{} : Bool},
  +hb: {Nat.is_eq(j, c) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = N.eq_sound(j, c, hb)
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(9n, 9n), True{}, Equal.sym(Bool, Nat.is_lt(9n, 9n), False{}, N.lt_irrefl(9n)),
        N.le_lt_trans(9n, c, 9n, %e : {Nat.is_le(9n, _) == True{} : Bool}; h, hc))))

# 9 <= j: j is not a smaller c.
def ge_ne(+j: Nat, +c: Nat, +h: {Nat.is_le(9n, j) == True{} : Bool}, +hc: {Nat.is_lt(c, 9n) == True{} : Bool}) -> {Nat.is_eq(j, c) == False{} : Bool}:
  gne.k(Nat.is_eq(j, c), j, c, h, hc, {==})

law rpg9:
  for +cols: Rgs()
  for +j: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +A: String
  for +defs: B.Defs
  for +kss: Ss()
  for +o: Bool
  for +nalt: Nat
  for +i: Nat
  for +h: {Nat.is_le(9n, j) == True{} : Bool}
  {B.Rec.piece.go(K.TXS(len, t, cols), j, A, defs, kss, o, nalt, i) == FSL(len, t, DF(defs), kss, o, nalt, i, cols) : G.Gs()}

def rpg9(cols, j, len, t, A, defs, kss, o, nalt, i, h):
  match cols:
    case Nil{}:
      {==}
    case Con{NS.Rg{+a, +z}, +rr}:
      +f = WT.TX(len, t, NS.Rg{a, z})
      +hjj = {%N.add_one(j) : {Nat.is_le(Nat.add(j, 1n), _) == True{} : Bool}; N.le_refl(Nat.add(j, 1n)) : {Nat.is_le(Nat.add(j, 1n), 1n+j) == True{} : Bool}}
      +h1 = N.le_trans(9n, j, 1n+j, h, N.le_trans(j, Nat.add(j, 1n), 1n+j, N.le_add_r(j, 1n), hjj))
      %Equal.sym(Bool, Nat.is_eq(j, 4n), False{}, ge_ne(j, 4n, h, {==})) :
        {Con{Bool.pick(B.Got, _, B.Got{A}, Bool.pick(B.Got, Nat.is_eq(j, 7n), B.Info.split(f, DI(defs), nalt, i), Bool.pick(B.Got, Nat.is_le(9n, j), B.Fmt.split(kss, f, DF(defs), o, nalt, i), B.Got{f}))), B.Rec.piece.go(K.TXS(len, t, rr), 1n+j, A, defs, kss, o, nalt, i)} ==
          FSL(len, t, DF(defs), kss, o, nalt, i, Con{NS.Rg{a, z}, rr}) : G.Gs()}
      %Equal.sym(Bool, Nat.is_eq(j, 7n), False{}, ge_ne(j, 7n, h, {==})) :
        {Con{Bool.pick(B.Got, _, B.Info.split(f, DI(defs), nalt, i), Bool.pick(B.Got, Nat.is_le(9n, j), B.Fmt.split(kss, f, DF(defs), o, nalt, i), B.Got{f})), B.Rec.piece.go(K.TXS(len, t, rr), 1n+j, A, defs, kss, o, nalt, i)} ==
          FSL(len, t, DF(defs), kss, o, nalt, i, Con{NS.Rg{a, z}, rr}) : G.Gs()}
      %Equal.sym(Bool, Nat.is_le(9n, j), True{}, h) :
        {Con{Bool.pick(B.Got, _, B.Fmt.split(kss, f, DF(defs), o, nalt, i), B.Got{f}), B.Rec.piece.go(K.TXS(len, t, rr), 1n+j, A, defs, kss, o, nalt, i)} ==
          FSL(len, t, DF(defs), kss, o, nalt, i, Con{NS.Rg{a, z}, rr}) : G.Gs()}
      %Equal.sym(G.Gs(), B.Rec.piece.go(K.TXS(len, t, rr), 1n+j, A, defs, kss, o, nalt, i), FSL(len, t, DF(defs), kss, o, nalt, i, rr),
        rpg9(rr, 1n+j, len, t, A, defs, kss, o, nalt, i, h1)) :
        {Con{B.Fmt.split(kss, f, DF(defs), o, nalt, i), _} == FSL(len, t, DF(defs), kss, o, nalt, i, Con{NS.Rg{a, z}, rr}) : G.Gs()}
      {==}

# ---------------------------------------------------------------------------
# The joined text, then the terminator
# ---------------------------------------------------------------------------

def JTT(gs: G.Gs(), +first: Bool, +sep: String, +e: String) -> String:
  match gs:
    case Nil{}:
      e
    case Con{+g, r}:
      String.append(G.PS(first, sep), String.append(G.GSTR(g), JTT(r, False{}, sep, e)))

law jtt_eq:
  for +gs: G.Gs()
  for +first: Bool
  for +sep: String
  for +e: String
  {JTT(gs, first, sep, e) == String.append(G.JT(gs, first, sep), e) : String}

def jtt_eq(gs, first, sep, e):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      +P0 = G.PS(first, sep)
      +X = G.GSTR(g)
      +J = G.JT(r, False{}, sep)
      %Equal.sym(String, JTT(r, False{}, sep, e), String.append(J, e), jtt_eq(r, False{}, sep, e)) :
        {String.append(P0, String.append(X, _)) == String.append(String.append(P0, String.append(X, J)), e) : String}
      %Equal.sym(String, String.append(String.append(P0, String.append(X, J)), e), String.append(P0, String.append(String.append(X, J), e)), MN.str_assoc(P0, String.append(X, J), e)) : {String.append(P0, String.append(X, String.append(J, e))) == _ : String}
      %Equal.sym(String, String.append(String.append(X, J), e), String.append(X, String.append(J, e)), MN.str_assoc(X, J, e)) : {String.append(P0, String.append(X, String.append(J, e))) == String.append(P0, _) : String}
      {==}

def pv_upx(+len: U32, +bb: U32, +x: NS.Rg, +hp: {W.PV(bb, x) == True{} : Bool}, +hb: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}) ->
  {W.PV(len, x) == True{} : Bool}:
  match x:
    case NS.Rg{+a, +z}:
      pv_up(len, bb, a, z, hp, hb)

# ---------------------------------------------------------------------------
# rec.tail: FORMAT and the samples (fields 8 on)
# ---------------------------------------------------------------------------

def RPGT(+len: U32, +t: AT.Tree<U32>, +A: String, +defs: B.Defs, +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, rest: Rgs()) -> G.Gs():
  B.Rec.piece.go(K.TXS(len, t, rest), 8n, A, defs, kss, o, nalt, i)

def rec_tail_t(+rest: Rgs(), +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +A: String, +defs: B.Defs, +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, +bb: U32,
  +hpc: {K.ALLPV(bb, rest) == True{} : Bool}, +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.rec.tail(rest, w, KD.MAPF(DF(defs), kss), o, nalt, i), m0,
    G.JT(RPGT(len, t, A, defs, kss, o, nalt, i, rest), False{}, "\t"), G.JG(RPGT(len, t, A, defs, kss, o, nalt, i, rest))):
  match rest:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{+f8, +cols}:
      +hp8 = N.and_true_l(W.PV(bb, f8), K.ALLPV(bb, cols), hpc)
      +hpr = N.and_true_r(W.PV(bb, f8), K.ALLPV(bb, cols), hpc)
      +F8 = WT.TX(len, t, f8)
      +L = FSL(len, t, DF(defs), kss, o, nalt, i, cols)
      -cw = NS.ch(w, 9)
      %Equal.sym(G.Gs(), B.Rec.piece.go(K.TXS(len, t, cols), 9n, A, defs, kss, o, nalt, i), L, rpg9(cols, 9n, len, t, A, defs, kss, o, nalt, i, {==})) :
        S.WS(len, t, NS.rec.tail(Con{f8, cols}, w, KD.MAPF(DF(defs), kss), o, nalt, i), m0, G.JT(Con{B.Got{F8}, _}, False{}, "\t"), G.JG(Con{B.Got{F8}, _}))
      S.ws_seq(len, t, cw, v => NS.samples(cols, NS.cpr(v, f8), KD.MAPF(DF(defs), kss), o, nalt, i), m0,
        NR.chars([9]), String.append(F8, G.JT(L, False{}, "\t")), True{}, Bool.and(True{}, G.JG(L)),
        S.ws_ch(len, t, d, hl, 9, {==}, w, m0, r),
        +m1 => r1 => S.ws_seq(len, t, NS.cpr(cw, f8), v => NS.samples(cols, v, KD.MAPF(DF(defs), kss), o, nalt, i), m1,
          F8, G.JT(L, False{}, "\t"), True{}, G.JG(L),
          S.ws_cpr(len, t, d, hl, f8, pv_upx(len, bb, f8, hp8, hbl), cw, m1, r1),
          +m2 => r2 => samples_t(cols, len, t, d, hl, DF(defs), kss, o, nalt, i, bb, hpr, hbl, bd, hbd, NS.cpr(cw, f8), m2, r2)))

# ---------------------------------------------------------------------------
# record: one record (B.Rec.piece), then the terminator
# (generated by data/tmp/split/tools/genrec.py)
# ---------------------------------------------------------------------------

def record_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +defs: B.Defs, +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat,
  +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32, +rest: Rgs(), +term: NS.Rg, +a: NS.Rg,
  +bb: U32, +hps: {K.ALLPV(bb, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}) == True{} : Bool}, +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool},
  +hpa: {W.PV(len, a) == True{} : Bool}, +hpt: {W.PV(len, term) == True{} : Bool},
  +haz7: {U32.is_le(a7, z7) == True{} : Bool}, +hz7: {Nat.is_lt(n(z7), n(len)) == True{} : Bool},
  +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.record(w, NS.Ln{Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}, KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), KD.MAPF(DF(defs), kss), term}, o, nalt, i, a), m0,
    String.append(G.JT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t"), WT.TX(len, t, term)), G.JG(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i))):
  +p0 = N.and_true_l(W.PV(bb, f0), K.ALLPV(bb, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}), hps)
  +q1 = N.and_true_r(W.PV(bb, f0), K.ALLPV(bb, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}), hps)
  +p1 = N.and_true_l(W.PV(bb, f1), K.ALLPV(bb, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}), q1)
  +q2 = N.and_true_r(W.PV(bb, f1), K.ALLPV(bb, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}), q1)
  +p2 = N.and_true_l(W.PV(bb, f2), K.ALLPV(bb, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}), q2)
  +q3 = N.and_true_r(W.PV(bb, f2), K.ALLPV(bb, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}), q2)
  +p3 = N.and_true_l(W.PV(bb, f3), K.ALLPV(bb, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}), q3)
  +q4 = N.and_true_r(W.PV(bb, f3), K.ALLPV(bb, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}), q3)
  +p4 = N.and_true_l(W.PV(bb, f4), K.ALLPV(bb, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}), q4)
  +q5 = N.and_true_r(W.PV(bb, f4), K.ALLPV(bb, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}), q4)
  +p5 = N.and_true_l(W.PV(bb, f5), K.ALLPV(bb, Con{f6, Con{NS.Rg{a7, z7}, rest}}), q5)
  +q6 = N.and_true_r(W.PV(bb, f5), K.ALLPV(bb, Con{f6, Con{NS.Rg{a7, z7}, rest}}), q5)
  +p6 = N.and_true_l(W.PV(bb, f6), K.ALLPV(bb, Con{NS.Rg{a7, z7}, rest}), q6)
  +q7 = N.and_true_r(W.PV(bb, f6), K.ALLPV(bb, Con{NS.Rg{a7, z7}, rest}), q6)
  +q8 = N.and_true_r(W.PV(bb, NS.Rg{a7, z7}), K.ALLPV(bb, rest), q7)
  S.ws_eq(len, t, NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m0, String.append(WT.TX(len, t, f0), String.append(NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))))))))), String.append(G.JT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t"), WT.TX(len, t, term)), Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))))))))))), G.JG(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i)),
    Equal.trans(String, String.append(WT.TX(len, t, f0), String.append(NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))))))))), JTT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t", WT.TX(len, t, term)), String.append(G.JT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t"), WT.TX(len, t, term)),
      {%jtt_eq(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t", WT.TX(len, t, term)) : {String.append(WT.TX(len, t, f0), String.append(NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), _))))))))))))))) == JTT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t", WT.TX(len, t, term)) : String}; {==} : {String.append(WT.TX(len, t, f0), String.append(NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))))))))) == JTT(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t", WT.TX(len, t, term)) : String}},
      jtt_eq(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i), True{}, "\t", WT.TX(len, t, term))),
    {%Equal.sym(Bool, Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}), G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), N.and_true_r_id(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)))) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), _))))))))))))))) == G.JG(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i)) : Bool}; {==} : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))))))))))) == G.JG(B.Rec.piece.go(K.TXS(len, t, Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i)) : Bool}},
    S.ws_seq(len, t, NS.cpr(w, f0), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(v, 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m0,
      WT.TX(len, t, f0), String.append(NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))))))))))))),
      S.ws_cpr(len, t, d, hl, f0, pv_upx(len, bb, f0, p0, hbl), w, m0, r),
      +m1 => r1 =>
      S.ws_seq(len, t, NS.ch(NS.cpr(w, f0), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(v, f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m1,
        NR.chars([9]), String.append(WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))))))))),
        S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(w, f0), m1, r1),
        +m2 => r2 =>
        S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(v, 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m2,
          WT.TX(len, t, f1), String.append(NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))))))))))),
          S.ws_cpr(len, t, d, hl, f1, pv_upx(len, bb, f1, p1, hbl), NS.ch(NS.cpr(w, f0), 9), m2, r2),
          +m3 => r3 =>
          S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(v, f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m3,
            NR.chars([9]), String.append(WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))))))),
            S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), m3, r3),
            +m4 => r4 =>
            S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(v, 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m4,
              WT.TX(len, t, f2), String.append(NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))))))))),
              S.ws_cpr(len, t, d, hl, f2, pv_upx(len, bb, f2, p2, hbl), NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), m4, r4),
              +m5 => r5 =>
              S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(v, f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m5,
                NR.chars([9]), String.append(WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))))),
                S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), m5, r5),
                +m6 => r6 =>
                S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(v, 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m6,
                  WT.TX(len, t, f3), String.append(NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))))))),
                  S.ws_cpr(len, t, d, hl, f3, pv_upx(len, bb, f3, p3, hbl), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), m6, r6),
                  +m7 => r7 =>
                  S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(v, a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m7,
                    NR.chars([9]), String.append(WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))))),
                    S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), m7, r7),
                    +m8 => r8 =>
                    S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(v, 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m8,
                      WT.TX(len, t, a), String.append(NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))))),
                      S.ws_cpr(len, t, d, hl, a, hpa, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), m8, r8),
                      +m9 => r9 =>
                      S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(v, f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m9,
                        NR.chars([9]), String.append(WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))))),
                        S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), m9, r9),
                        +m10 => r10 =>
                        S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(v, 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m10,
                          WT.TX(len, t, f5), String.append(NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))))),
                          S.ws_cpr(len, t, d, hl, f5, pv_upx(len, bb, f5, p5, hbl), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), m10, r10),
                          +m11 => r11 =>
                          S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(v, f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m11,
                            NR.chars([9]), String.append(WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))))), True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})))),
                            S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), m11, r11),
                            +m12 => r12 =>
                            S.ws_seq(len, t, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(v, 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m12,
                              WT.TX(len, t, f6), String.append(NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)))), True{}, Bool.and(True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}))),
                              S.ws_cpr(len, t, d, hl, f6, pv_upx(len, bb, f6, p6, hbl), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), m12, r12),
                              +m13 => r13 =>
                              S.ws_seq(len, t, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), v => NS.cpr(NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), v, nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), term), m13,
                                NR.chars([9]), String.append(G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term))), True{}, Bool.and(G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{})),
                                S.ws_ch(len, t, d, hl, 9, {==}, NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), m13, r13),
                                +m14 => r14 =>
                                S.ws_seq(len, t, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), v => NS.cpr(NS.rec.tail(rest, v, KD.MAPF(DF(defs), kss), o, nalt, i), term), m14,
                                  G.GSTR(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), String.append(G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term)), G.GOK(IF.INFOS(len, t, DI(defs), nalt, i, a7, z7)), Bool.and(G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{}),
                                  IF.info_t(len, t, d, hl, DI(defs), nalt, i, a7, z7, haz7, hz7, NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), m14, r14),
                                  +m15 => r15 =>
                                  S.ws_seq(len, t, NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), v => NS.cpr(v, term), m15,
                                    G.JT(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest), False{}, "\t"), WT.TX(len, t, term), G.JG(RPGT(len, t, WT.TX(len, t, a), defs, kss, o, nalt, i, rest)), True{},
                                    rec_tail_t(rest, len, t, d, hl, WT.TX(len, t, a), defs, kss, o, nalt, i, bb, q8, hbl, bd, hbd, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), m15, r15),
                                    +m16 => r16 =>
                                    S.ws_cpr(len, t, d, hl, term, hpt, NS.rec.tail(rest, NS.info.go(KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(NS.ch(NS.cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), nalt, i, True{}), KD.MAPF(DF(defs), kss), o, nalt, i), m16, r16))))))))))))))))))

# ---------------------------------------------------------------------------
# records: one record per ALT, from ALT i on
# ---------------------------------------------------------------------------

def FSX(+f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32, +rest: Rgs()) -> Rgs():
  Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{NS.Rg{a7, z7}, rest}}}}}}}}

def RPGA(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, +i: Nat, +a: NS.Rg) -> G.Gs():
  B.Rec.piece.go(K.TXS(len, t, fs), 0n, WT.TX(len, t, a), defs, kss, o, nalt, i)

def RT(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, +term: NS.Rg, alts: Rgs(), +i: Nat) -> String:
  match alts:
    case Nil{}:
      ""
    case Con{+a, r}:
      String.append(G.JT(RPGA(len, t, defs, fs, kss, o, nalt, i, a), True{}, "\t"), String.append(WT.TX(len, t, term), RT(len, t, defs, fs, kss, o, nalt, term, r, 1n+i)))

def RG(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, alts: Rgs(), +i: Nat) -> Bool:
  match alts:
    case Nil{}:
      True{}
    case Con{+a, r}:
      Bool.and(G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, r, 1n+i))

law records_t:
  for +alts: Rgs()
  for +i: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +defs: B.Defs
  for +kss: Ss()
  for +o: Bool
  for +nalt: Nat
  for +f0: NS.Rg
  for +f1: NS.Rg
  for +f2: NS.Rg
  for +f3: NS.Rg
  for +f4: NS.Rg
  for +f5: NS.Rg
  for +f6: NS.Rg
  for +a7: U32
  for +z7: U32
  for +rest: Rgs()
  for +term: NS.Rg
  for +bb: U32
  for +hps: {K.ALLPV(bb, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, rest)) == True{} : Bool}
  for +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}
  for +hpas: {K.ALLPV(len, alts) == True{} : Bool}
  for +hpt: {W.PV(len, term) == True{} : Bool}
  for +haz7: {U32.is_le(a7, z7) == True{} : Bool}
  for +hz7: {Nat.is_lt(n(z7), n(len)) == True{} : Bool}
  for +bd: Nat
  for +hbd: {Nat.pow(2n, 32n) == bd : Nat}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.records(alts, w, NS.Ln{FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, rest), KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), KD.MAPF(DF(defs), kss), term}, o, nalt, i), m0,
    RT(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, rest), kss, o, nalt, term, alts, i), RG(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, rest), kss, o, nalt, alts, i))

def records_t(alts, i, len, t, d, hl, defs, kss, o, nalt, f0, f1, f2, f3, f4, f5, f6, a7, z7, rest, term, bb, hps, hbl, hpas, hpt, haz7, hz7, bd, hbd, w, m0, r):
  match alts:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{+a, +rr}:
      +fs = FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, rest)
      +l = {NS.Ln{fs, KD.MAPI(len, t, DI(defs), K.CUT(len, t, a7, z7, 59)), KD.MAPF(DF(defs), kss), term} : NS.Ln}
      +hpa = N.and_true_l(W.PV(len, a), K.ALLPV(len, rr), hpas)
      +hpr = N.and_true_r(W.PV(len, a), K.ALLPV(len, rr), hpas)
      +J = G.JT(RPGA(len, t, defs, fs, kss, o, nalt, i, a), True{}, "\t")
      +TT = WT.TX(len, t, term)
      +R = RT(len, t, defs, fs, kss, o, nalt, term, rr, 1n+i)
      S.ws_eq(len, t, NS.records(rr, NS.record(w, l, o, nalt, i, a), l, o, nalt, 1n+i), m0,
        String.append(String.append(J, TT), R), String.append(J, String.append(TT, R)),
        Bool.and(G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, rr, 1n+i)), Bool.and(G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, rr, 1n+i)),
        MN.str_assoc(J, TT, R), {==},
        S.ws_seq(len, t, NS.record(w, l, o, nalt, i, a), v => NS.records(rr, v, l, o, nalt, 1n+i), m0,
          String.append(J, TT), R, G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, rr, 1n+i),
          record_t(len, t, d, hl, defs, kss, o, nalt, i, f0, f1, f2, f3, f4, f5, f6, a7, z7, rest, term, a, bb, hps, hbl, hpa, hpt, haz7, hz7, bd, hbd, w, m0, r),
          +m1 => r1 => records_t(rr, 1n+i, len, t, d, hl, defs, kss, o, nalt, f0, f1, f2, f3, f4, f5, f6, a7, z7, rest, term, bb, hps, hbl, hpr, hpt, haz7, hz7, bd, hbd, NS.record(w, l, o, nalt, i, a), m1, r1)))

# ---------------------------------------------------------------------------
# The records against B.Rec.parts' pieces
# ---------------------------------------------------------------------------

def KSS(fss: Ss()) -> Ss():
  String.split(B.Rec.field(fss, 8n), ':')

def PSL(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, alts: Rgs(), +i: Nat) -> Ss():
  match alts:
    case Nil{}:
      Nil{}
    case Con{+a, r}:
      Con{G.JT(RPGA(len, t, defs, fs, kss, o, nalt, i, a), True{}, "\t"), PSL(len, t, defs, fs, kss, o, nalt, r, 1n+i)}

def PRT(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, +term: NS.Rg, alts: Rgs(), +i: Nat) -> Type:
  {B.Parts.of(B.Rec.pieces.go(K.TXS(len, t, alts), K.TXS(len, t, fs), defs, o, nalt, i)) == B.Pieces{PSL(len, t, defs, fs, kss, o, nalt, alts, i)} : B.Parts} &
  {Norm.recs_text(PSL(len, t, defs, fs, kss, o, nalt, alts, i), WT.TX(len, t, term)) == RT(len, t, defs, fs, kss, o, nalt, term, alts, i) : String}

def pt.k(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +fs: Rgs(), +kss: Ss(), +o: Bool, +nalt: Nat, +term: NS.Rg, +a: NS.Rg, +r: Rgs(), +i: Nat,
  +hk: {KSS(K.TXS(len, t, fs)) == kss : Ss()},
  +hga: {G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)) == True{} : Bool},
  ih: PRT(len, t, defs, fs, kss, o, nalt, term, r, 1n+i)) ->
  PRT(len, t, defs, fs, kss, o, nalt, term, Con{a, r}, i):
  (e1, e2) = ih
  +L = RPGA(len, t, defs, fs, kss, o, nalt, i, a)
  +J = G.JT(L, True{}, "\t")
  +ep = {%Equal.sym(Ss(), KSS(K.TXS(len, t, fs)), kss, hk) : {B.Got.join(B.Rec.piece.go(K.TXS(len, t, fs), 0n, WT.TX(len, t, a), defs, _, o, nalt, i), "\t") == B.Got{J} : B.Got};
    G.join_t(L, "\t", hga) : {B.Rec.piece(K.TXS(len, t, fs), WT.TX(len, t, a), defs, o, nalt, i) == B.Got{J} : B.Got}}
  +P1 = {%Equal.sym(B.Got, B.Rec.piece(K.TXS(len, t, fs), WT.TX(len, t, a), defs, o, nalt, i), B.Got{J}, ep) :
      {B.Parts.cons(_, B.Parts.of(B.Rec.pieces.go(K.TXS(len, t, r), K.TXS(len, t, fs), defs, o, nalt, 1n+i))) == B.Pieces{PSL(len, t, defs, fs, kss, o, nalt, Con{a, r}, i)} : B.Parts};
    %Equal.sym(B.Parts, B.Parts.of(B.Rec.pieces.go(K.TXS(len, t, r), K.TXS(len, t, fs), defs, o, nalt, 1n+i)), B.Pieces{PSL(len, t, defs, fs, kss, o, nalt, r, 1n+i)}, e1) :
      {B.Parts.cons(B.Got{J}, _) == B.Pieces{PSL(len, t, defs, fs, kss, o, nalt, Con{a, r}, i)} : B.Parts};
    {==} : {B.Parts.of(B.Rec.pieces.go(K.TXS(len, t, Con{a, r}), K.TXS(len, t, fs), defs, o, nalt, i)) == B.Pieces{PSL(len, t, defs, fs, kss, o, nalt, Con{a, r}, i)} : B.Parts}}
  +P2 = {%Equal.sym(String, Norm.recs_text(PSL(len, t, defs, fs, kss, o, nalt, r, 1n+i), WT.TX(len, t, term)), RT(len, t, defs, fs, kss, o, nalt, term, r, 1n+i), e2) :
      {String.append(J, String.append(WT.TX(len, t, term), _)) == RT(len, t, defs, fs, kss, o, nalt, term, Con{a, r}, i) : String};
    {==} : {Norm.recs_text(PSL(len, t, defs, fs, kss, o, nalt, Con{a, r}, i), WT.TX(len, t, term)) == RT(len, t, defs, fs, kss, o, nalt, term, Con{a, r}, i) : String}}
  (P1, P2)

law parts_t:
  for +alts: Rgs()
  for +i: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +defs: B.Defs
  for +fs: Rgs()
  for +kss: Ss()
  for +o: Bool
  for +nalt: Nat
  for +term: NS.Rg
  for +hk: {KSS(K.TXS(len, t, fs)) == kss : Ss()}
  for +hg: {RG(len, t, defs, fs, kss, o, nalt, alts, i) == True{} : Bool}
  PRT(len, t, defs, fs, kss, o, nalt, term, alts, i)

def parts_t(alts, i, len, t, defs, fs, kss, o, nalt, term, hk, hg):
  match alts:
    case Nil{}:
      ({==}, {==})
    case Con{+a, +r}:
      +hga = N.and_true_l(G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, r, 1n+i), hg)
      +hgr = N.and_true_r(G.JG(RPGA(len, t, defs, fs, kss, o, nalt, i, a)), RG(len, t, defs, fs, kss, o, nalt, r, 1n+i), hg)
      pt.k(len, t, defs, fs, kss, o, nalt, term, a, r, i, hk, hga, parts_t(r, 1n+i, len, t, defs, fs, kss, o, nalt, term, hk, hgr))

# Eight fields (no FORMAT): the FORMAT keys are not read.
law rt8:
  for +alts: Rgs()
  for +i: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +defs: B.Defs
  for +f0: NS.Rg
  for +f1: NS.Rg
  for +f2: NS.Rg
  for +f3: NS.Rg
  for +f4: NS.Rg
  for +f5: NS.Rg
  for +f6: NS.Rg
  for +a7: U32
  for +z7: U32
  for +k1: Ss()
  for +k2: Ss()
  for +o: Bool
  for +nalt: Nat
  for +term: NS.Rg
  {RT(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{}), k1, o, nalt, term, alts, i) == RT(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{}), k2, o, nalt, term, alts, i) : String}

def rt8(alts, i, len, t, defs, f0, f1, f2, f3, f4, f5, f6, a7, z7, k1, k2, o, nalt, term):
  match alts:
    case Nil{}:
      {==}
    case Con{+a, +r}:
      +fs = FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{})
      %Equal.sym(String, RT(len, t, defs, fs, k1, o, nalt, term, r, 1n+i), RT(len, t, defs, fs, k2, o, nalt, term, r, 1n+i), rt8(r, 1n+i, len, t, defs, f0, f1, f2, f3, f4, f5, f6, a7, z7, k1, k2, o, nalt, term)) :
        {String.append(G.JT(RPGA(len, t, defs, fs, k1, o, nalt, i, a), True{}, "\t"), String.append(WT.TX(len, t, term), _)) == RT(len, t, defs, fs, k2, o, nalt, term, Con{a, r}, i) : String}
      {==}

law rg8:
  for +alts: Rgs()
  for +i: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +defs: B.Defs
  for +f0: NS.Rg
  for +f1: NS.Rg
  for +f2: NS.Rg
  for +f3: NS.Rg
  for +f4: NS.Rg
  for +f5: NS.Rg
  for +f6: NS.Rg
  for +a7: U32
  for +z7: U32
  for +k1: Ss()
  for +k2: Ss()
  for +o: Bool
  for +nalt: Nat
  {RG(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{}), k1, o, nalt, alts, i) == RG(len, t, defs, FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{}), k2, o, nalt, alts, i) : Bool}

def rg8(alts, i, len, t, defs, f0, f1, f2, f3, f4, f5, f6, a7, z7, k1, k2, o, nalt):
  match alts:
    case Nil{}:
      {==}
    case Con{+a, +r}:
      +fs = FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{})
      %Equal.sym(Bool, RG(len, t, defs, fs, k1, o, nalt, r, 1n+i), RG(len, t, defs, fs, k2, o, nalt, r, 1n+i), rg8(r, 1n+i, len, t, defs, f0, f1, f2, f3, f4, f5, f6, a7, z7, k1, k2, o, nalt)) :
        {Bool.and(G.JG(RPGA(len, t, defs, fs, k1, o, nalt, i, a)), _) == RG(len, t, defs, fs, k2, o, nalt, Con{a, r}, i) : Bool}
      {==}
