import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_fast.bend as NF
import ./proof_c_defs.bend as Q
import ./proof_b_cut_pair.bend as M
import ./proof_b_cut_nat.bend as Z
import ./proof_b_cut_ne.bend as E
import ./proof_b_cut_pos.bend as PO
import ./proof_c_pre_key.bend as K
import ./proof_c_pre_let.bend as L
import ./proof_c_pre_lp.bend as G
import ./proof_b_alleles.bend as AL
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-fields@0.1.0.0/proof_num.bend as LN
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-bytes@0.1.0.0/proof_list.bend as PL
import lawful-bytes@0.1.0.0/proof_same.bend as PSm
import lawful-bytes@0.1.0.0/proof_seq.bend as SQ
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# INFO's END entries on bytes: when NF.endok passes on INFO's bytes (M.EK,
# the fast path's END test), B.Info.end_ok holds on INFO's text for POS pos
# and a REF of rl bytes (the value POS + len(REF) - 1). The scan (M.EG) walks
# the entries (the pieces between ';') as proof_c_pre_key.bend's nostale scan
# does; an entry's key ends at its first '=' (or ';', or INFO's end), as
# B.Info.key reads it. Its search lemmas are reused (K.KE is M.EKE).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def LL() -> Data:
  List<&2, List<&2, U32>>

def ML() -> Data:
  List<&2, Maybe<&2, Nat>>

# ---------------------------------------------------------------------------
# The key END
# ---------------------------------------------------------------------------

def LO_and(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +j: U32) -> {M.LO(ok, len, t, k, j) == Bool.and(ok, U32.is_eq(C.AT(len, t, j), k)) : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# lit.go on the mirror: the bytes from j are ks.
def lit_v(+ks: List<&2, U32>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +ok: Bool, +j: U32,
  +hj: {Nat.is_le(Nat.add(n(j), List.length(&2, U32, ks)), n(len)) == True{} : Bool},
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {M.LIT(ks, len, t, ok, j) == Bool.and(ok, D.list_eq(D.slice(Q.xs(len, t), n(j), List.length(&2, U32, ks)), ks)) : Bool}:
  match ks:
    case Nil{}:
      +Lz = List.drop(&2, U32, Q.xs(len, t), n(j))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, Lz, 0n), Nil{}, SQ.take_zero(Lz)) : {ok == Bool.and(ok, D.list_eq(_, Nil{})) : Bool}
      Equal.sym(Bool, Bool.and(ok, True{}), ok, LS.and_true(ok))
    case +k <> +q:
      +VW = Q.xs(len, t)
      +y = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +m = List.length(&2, U32, q)
      +S1 = D.slice(VW, n(j1), m)
      %Equal.sym(Bool, M.LO(ok, len, t, k, j), Bool.and(ok, U32.is_eq(C.AT(len, t, j), k)), LO_and(ok, len, t, k, j)) : {M.LIT(q, len, t, _, j1) == Bool.and(ok, D.list_eq(D.slice(VW, n(j), 1n+m), k <> q)) : Bool}
      %Equal.sym(List<&2, U32>, D.slice(VW, n(j), 1n+m), y <> D.slice(VW, Nat.add(n(j), 1n), m), PSm.slice_cons(VW, n(j), m, y, G.get_of(len, t, d, j, m, h, hj))) :
        {M.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == Bool.and(ok, D.list_eq(_, k <> q)) : Bool}
      %G.inc_of(len, t, d, j, m, h, hj) :
        {M.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == Bool.and(ok, Bool.and(U32.is_eq(y, k), D.list_eq(D.slice(VW, _, m), q))) : Bool}
      %LS.and_assoc(ok, U32.is_eq(y, k), D.list_eq(S1, q)) :
        {M.LIT(q, len, t, Bool.and(ok, U32.is_eq(y, k)), j1) == _ : Bool}
      lit_v(q, len, t, d, Bool.and(ok, U32.is_eq(y, k)), j1, G.nx_of(len, t, d, j, m, h, hj), h)

def EB() -> List<&2, U32>:
  [69, 78, 68]

def kf3.k(+b: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +m: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjm: {Nat.is_le(Nat.add(n(j), n(m)), n(len)) == True{} : Bool}, +hb: {U32.is_eq(m, 3) == b : Bool},
  +hk: {M.KEY3(len, t, j, m) == False{} : Bool}) ->
  {D.list_eq(K.KSL(len, t, j, m), EB()) == False{} : Bool}:
  match b:
    case True{}:
      +e = U.is_eq_true(m, 3, hb)
      +hk2 = AB.subst(U32, z => {M.KEY3(len, t, j, z) == False{} : Bool}, m, 3, e, hk)
      +hjm2 = AB.subst(U32, z => {Nat.is_le(Nat.add(n(j), n(z)), n(len)) == True{} : Bool}, m, 3, e, hjm)
      %Equal.sym(U32, m, 3, e) : {D.list_eq(K.KSL(len, t, j, _), EB()) == False{} : Bool}
      Equal.trans(Bool, D.list_eq(D.slice(Q.xs(len, t), n(j), 3n), EB()), M.LIT(EB(), len, t, True{}, j), False{},
        Equal.sym(Bool, M.LIT(EB(), len, t, True{}, j), D.list_eq(D.slice(Q.xs(len, t), n(j), 3n), EB()), lit_v(EB(), len, t, d, True{}, j, hjm2, h)),
        hk2)
    case False{}:
      +sl = LP.slice_len(Q.xs(len, t), n(j), n(m), AB.subst(Nat, z => {Nat.is_le(Nat.add(n(j), n(m)), z) == True{} : Bool}, n(len), List.length(&2, U32, Q.xs(len, t)), LP.len_x(len, t, d, h), hjm))
      LP.list_eq_len(K.KSL(len, t, j, m), EB(),
        AB.subst(Nat, z => {Nat.is_eq(z, 3n) == False{} : Bool}, n(m), List.length(&2, U32, K.KSL(len, t, j, m)), Equal.sym(Nat, List.length(&2, U32, K.KSL(len, t, j, m)), n(m), sl),
          Z.une(m, 3, hb)))

# A key the bytes test refused is not END.
def k3false(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +m: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjm: {Nat.is_le(Nat.add(n(j), n(m)), n(len)) == True{} : Bool}, +hk: {M.KEY3(len, t, j, m) == False{} : Bool}) ->
  {String.eq(Norm.chars(K.KSL(len, t, j, m)), "END") == False{} : Bool}:
  %Equal.sym(Bool, String.eq(Norm.chars(K.KSL(len, t, j, m)), Norm.chars(EB())), D.list_eq(K.KSL(len, t, j, m), EB()), L.seq(K.KSL(len, t, j, m), EB())) : {_ == False{} : Bool}
  kf3.k(U32.is_eq(m, 3), len, t, d, j, m, h, hjm, {==}, hk)

def k3m.k(+b: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32, +m: U32, +hb: {U32.is_eq(m, 3) == b : Bool},
  +hk: {M.K3IF(b, len, t, j) == True{} : Bool}) -> {U32.is_eq(m, 3) == True{} : Bool}:
  match b:
    case True{}:
      hb
    case False{}:
      Empty.absurd({U32.is_eq(m, 3) == True{} : Bool}, N.false_ne_true(hk))

# A key the bytes test took is three bytes long.
def k3m(+len: U32, +t: AT.Tree<U32>, +j: U32, +m: U32, +hk: {M.KEY3(len, t, j, m) == True{} : Bool}) -> {m == 3 : U32}:
  U.is_eq_true(m, 3, k3m.k(U32.is_eq(m, 3), len, t, j, m, {==}, hk))

# ... and is END.
def k3true(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +m: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjm: {Nat.is_le(Nat.add(n(j), n(m)), n(len)) == True{} : Bool}, +hk: {M.KEY3(len, t, j, m) == True{} : Bool}) ->
  {String.eq(Norm.chars(K.KSL(len, t, j, m)), "END") == True{} : Bool}:
  +e = k3m(len, t, j, m, hk)
  +hk2 = AB.subst(U32, z => {M.KEY3(len, t, j, z) == True{} : Bool}, m, 3, e, hk)
  +hjm2 = AB.subst(U32, z => {Nat.is_le(Nat.add(n(j), n(z)), n(len)) == True{} : Bool}, m, 3, e, hjm)
  %Equal.sym(U32, m, 3, e) : {String.eq(Norm.chars(K.KSL(len, t, j, _)), "END") == True{} : Bool}
  %Equal.sym(Bool, String.eq(Norm.chars(K.KSL(len, t, j, 3)), Norm.chars(EB())), D.list_eq(K.KSL(len, t, j, 3), EB()), L.seq(K.KSL(len, t, j, 3), EB())) : {_ == True{} : Bool}
  Equal.trans(Bool, D.list_eq(D.slice(Q.xs(len, t), n(j), 3n), EB()), M.LIT(EB(), len, t, True{}, j), True{},
    Equal.sym(Bool, M.LIT(EB(), len, t, True{}, j), D.list_eq(D.slice(Q.xs(len, t), n(j), 3n), EB()), lit_v(EB(), len, t, d, True{}, j, hjm2, h)),
    hk2)

# ---------------------------------------------------------------------------
# The entries
# ---------------------------------------------------------------------------

# The END values of the entries from j on (INFO ends at to).
def ENDS(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> ML():
  B.Info.ends.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), n(j), Nat.sub(n(to), n(j))), 59)))

# The entry at j has key END.
def SEQ(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> Bool:
  String.eq(Norm.chars(K.KSL(len, t, j, (K.KE(len, t, to, j) - j : U32))), "END")

# One entry (j .. s-1, the rest after it), its key ending at ke: its END
# value if its key is END, then the rest's.
def ENTQ(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +s: Nat, +ke: U32, +rest: LL(),
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hjk: {Nat.is_le(n(j), n(ke)) == True{} : Bool},
  +hfs: {D.first(Q.xs(len, t), n(j), n(to), 59) == s : Nat},
  +hrest: {LS.tsplit(D.slice(Q.xs(len, t), s, Nat.sub(n(to), s)), 59) == rest : LL()},
  +hfk: {D.first(Q.xs(len, t), n(j), s, 61) == n(ke) : Nat}) ->
  {ENDS(len, t, to, j) == B.Info.ends.put(String.eq(Norm.chars(K.KSL(len, t, j, (ke - j : U32))), "END"), Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(s, n(j)))), B.Info.ends.go(AL.mapc(rest))) : ML()}:
  +X = Q.xs(len, t)
  +ent = D.slice(X, n(j), Nat.sub(s, n(j)))
  +f59 = D.first(X, n(j), n(to), 59)
  +f61 = D.first(X, n(j), s, 61)
  +RHS = B.Info.ends.put(String.eq(Norm.chars(K.KSL(len, t, j, (ke - j : U32))), "END"), Norm.chars(ent), B.Info.ends.go(AL.mapc(rest)))
  +hkey = Equal.trans(String, B.Info.key(Norm.chars(ent)), B.Rec.field(AL.mapc(FD.split(ent, 61)), 0n), Norm.chars(K.KSL(len, t, j, (ke - j : U32))),
    Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), String.split(Norm.chars(ent), '='), AL.mapc(FD.split(ent, 61)), K.csplit_g(ent, 61)),
    Equal.trans(String, B.Rec.field(AL.mapc(FD.split(ent, 61)), 0n), Norm.chars(D.slice(X, n(j), Nat.sub(f61, n(j)))), Norm.chars(K.KSL(len, t, j, (ke - j : U32))),
      Equal.cong(LL(), String, z => B.Rec.field(AL.mapc(z), 0n), FD.split(ent, 61), Con{D.slice(X, n(j), Nat.sub(f61, n(j))), LS.tsplit(D.slice(X, f61, Nat.sub(s, f61)), 61)}, LS.spl(X, n(j), s, 61)),
      Equal.cong(Nat, String, z => Norm.chars(D.slice(X, n(j), z)), Nat.sub(f61, n(j)), n((ke - j : U32)),
        Equal.trans(Nat, Nat.sub(f61, n(j)), Nat.sub(n(ke), n(j)), n((ke - j : U32)), Equal.cong(Nat, Nat, z => Nat.sub(z, n(j)), f61, n(ke), hfk), Equal.sym(Nat, n((ke - j : U32)), Nat.sub(n(ke), n(j)), LP.sub_u(ke, j, hjk))))))
  %Equal.sym(LL(), FD.split(D.slice(X, n(j), Nat.sub(n(to), n(j))), 59), Con{D.slice(X, n(j), Nat.sub(f59, n(j))), LS.tsplit(D.slice(X, f59, Nat.sub(n(to), f59)), 59)}, LS.spl(X, n(j), n(to), 59)) :
    {B.Info.ends.go(AL.mapc(_)) == RHS : ML()}
  %Equal.sym(Nat, f59, s, hfs) :
    {B.Info.ends.go(AL.mapc(Con{D.slice(X, n(j), Nat.sub(_, n(j))), LS.tsplit(D.slice(X, _, Nat.sub(n(to), _)), 59)})) == RHS : ML()}
  %Equal.sym(LL(), LS.tsplit(D.slice(X, s, Nat.sub(n(to), s)), 59), rest, hrest) :
    {B.Info.ends.go(AL.mapc(Con{ent, _})) == RHS : ML()}
  %Equal.sym(String, B.Info.key(Norm.chars(ent)), Norm.chars(K.KSL(len, t, j, (ke - j : U32))), hkey) :
    {B.Info.ends.put(String.eq(_, "END"), Norm.chars(ent), B.Info.ends.go(AL.mapc(rest))) == RHS : ML()}
  {==}

# INFO's end reached: one entry left.
def e_end(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == True{} : Bool}) ->
  {ENDS(len, t, to, j) == B.Info.ends.put(SEQ(len, t, to, j), Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(n(to), n(j)))), Nil{}) : ML()}:
  +ke = K.KE(len, t, to, j)
  +X = Q.xs(len, t)
  +ek = Equal.cong(U32, Nat, z => n(z), ke, to, U.is_eq_true(ke, to, hen))
  +hL = K.hlx(len, t, d, n(to), h, hto)
  +hfs = Z.unq(X, n(j), n(to), n(to), 59, hjt, N.le_refl(n(to)), hL, h0 => K.lt_no(n(to), {D.has(X, n(to), 59) == True{} : Bool}, h0),
    +k => a => b => K.m59(len, t, d, to, j, h, hto, hjt, k, a, AB.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, n(to), n(ke), Equal.sym(Nat, n(ke), n(to), ek), b)))
  +hfk = Z.unq(X, n(j), n(ke), n(to), 61, K.kj(len, t, d, to, j, h, hto, hjt), K.kt(len, t, d, to, j, h, hto, hjt), hL,
    h0 => K.lt_no(n(to), {D.has(X, n(ke), 61) == True{} : Bool}, AB.subst(Nat, z => {Nat.is_lt(z, n(to)) == True{} : Bool}, n(ke), n(to), ek, h0)),
    +k => a => b => K.m61(len, t, d, to, j, h, hto, hjt, k, a, b))
  ENTQ(len, t, d, to, j, n(to), ke, Nil{}, h, K.kj(len, t, d, to, j, h, hto, hjt), hfs, LS.ts_eq(X, n(to), 59), hfk)

# The entries from c + 1 (a ';' at c), as ENDS at c + 1 as a word.
def ends_next(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +c: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hcl: {Nat.is_lt(n(c), n(len)) == True{} : Bool}) ->
  {B.Info.ends.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), Nat.add(n(c), 1n), Nat.sub(n(to), Nat.add(n(c), 1n))), 59))) == ENDS(len, t, to, (c + 1 : U32)) : ML()}:
  Equal.cong(Nat, ML(), z => B.Info.ends.go(AL.mapc(FD.split(D.slice(Q.xs(len, t), z, Nat.sub(n(to), z)), 59))), Nat.add(n(c), 1n), n((c + 1 : U32)),
    Equal.sym(Nat, n((c + 1 : U32)), Nat.add(n(c), 1n), LP.inc_len(len, t, d, c, h, hcl)))

# A ';' ends the key: the entry ends there too.
def e_semi(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == True{} : Bool}) ->
  {ENDS(len, t, to, j) == B.Info.ends.put(SEQ(len, t, to, j), Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(n(K.KE(len, t, to, j)), n(j)))), ENDS(len, t, to, (K.KE(len, t, to, j) + 1 : U32))) : ML()}:
  +ke = K.KE(len, t, to, j)
  +X = Q.xs(len, t)
  +hL = K.hlx(len, t, d, n(to), h, hto)
  +lt = K.ke_lt(len, t, d, to, j, h, hto, hjt, hen)
  +lk = K.ke_len(len, t, d, to, j, h, hto, hjt, hen)
  +hg = Z.tabget(len, t, d, ke, 59, h, lk, hse)
  +hfs = Z.unq(X, n(j), n(ke), n(to), 59, K.kj(len, t, d, to, j, h, hto, hjt), K.kt(len, t, d, to, j, h, hto, hjt), hL,
    h0 => Z.has_get(X, n(ke), 59, 59, hg),
    +k => a => b => K.m59(len, t, d, to, j, h, hto, hjt, k, a, b))
  +hfk = Z.unq(X, n(j), n(ke), n(ke), 61, K.kj(len, t, d, to, j, h, hto, hjt), N.le_refl(n(ke)), K.hlx(len, t, d, n(ke), h, K.kl(len, t, d, to, j, h, hto, hjt)),
    h0 => K.lt_no(n(ke), {D.has(X, n(ke), 61) == True{} : Bool}, h0),
    +k => a => b => K.m61(len, t, d, to, j, h, hto, hjt, k, a, b))
  +rest = FD.split(D.slice(X, Nat.add(n(ke), 1n), Nat.sub(n(to), Nat.add(n(ke), 1n))), 59)
  +p = Norm.chars(D.slice(X, n(j), Nat.sub(n(ke), n(j))))
  Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, B.Info.ends.go(AL.mapc(rest))), B.Info.ends.put(SEQ(len, t, to, j), p, ENDS(len, t, to, (ke + 1 : U32))),
    ENTQ(len, t, d, to, j, n(ke), ke, rest, h, K.kj(len, t, d, to, j, h, hto, hjt), hfs, LS.ts_lt(X, n(ke), n(to), 59, lt, hg), hfk),
    Equal.cong(ML(), ML(), z => B.Info.ends.put(SEQ(len, t, to, j), p, z), B.Info.ends.go(AL.mapc(rest)), ENDS(len, t, to, (ke + 1 : U32)), ends_next(len, t, d, to, ke, h, lk)))

# '=' then no ';' before INFO's end.
def e_eq_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool},
  +hb2: {U32.is_eq(K.SM(len, t, to, j), to) == True{} : Bool}) ->
  {ENDS(len, t, to, j) == B.Info.ends.put(SEQ(len, t, to, j), Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j)))), Nil{}) : ML()}:
  +X = Q.xs(len, t)
  +f = K.F59(len, t, to, j)
  +ef = Equal.trans(Nat, f, n(K.SM(len, t, to, j)), n(to), Equal.sym(Nat, n(K.SM(len, t, to, j)), f, K.nsm(len, t, d, to, j, h, hto, hjt)),
    Equal.cong(U32, Nat, z => n(z), K.SM(len, t, to, j), to, U.is_eq_true(K.SM(len, t, to, j), to, hb2)))
  ENTQ(len, t, d, to, j, f, K.KE(len, t, to, j), Nil{}, h, K.kj(len, t, d, to, j, h, hto, hjt),
    K.hfs_e(len, t, d, to, j, h, hto, hjt, hen, hse),
    AB.subst(Nat, z => {LS.tsplit(D.slice(X, z, Nat.sub(n(to), z)), 59) == Nil{} : LL()}, n(to), f, Equal.sym(Nat, f, n(to), ef), LS.ts_eq(X, n(to), 59)),
    K.hfk_e(len, t, d, to, j, h, hto, hjt, hen, hse))

# '=' then a ';' before INFO's end: the next entry follows it.
def e_eq_f(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool},
  +hb2: {U32.is_eq(K.SM(len, t, to, j), to) == False{} : Bool}) ->
  {ENDS(len, t, to, j) == B.Info.ends.put(SEQ(len, t, to, j), Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j)))), ENDS(len, t, to, (K.SM(len, t, to, j) + 1 : U32))) : ML()}:
  +X = Q.xs(len, t)
  +sm = K.SM(len, t, to, j)
  +f = K.F59(len, t, to, j)
  +es = K.nsm(len, t, d, to, j, h, hto, hjt)
  +lt2 = Z.le_ne_lt(f, n(to), K.smt(len, t, d, to, j, h, hto, hjt),
    AB.subst(Nat, z => {Nat.is_eq(z, n(to)) == False{} : Bool}, n(sm), f, es, Z.une(sm, to, hb2)))
  +ke = K.KE(len, t, to, j)
  +hit = PL.first_hit(X, n(ke), n(to), 59, K.kt(len, t, d, to, j, h, hto, hjt), K.hlx(len, t, d, n(to), h, hto), lt2)
  +hg2 = LP.has_get(X, f, 59, hit)
  +sml = AB.subst(Nat, z => {Nat.is_lt(z, n(len)) == True{} : Bool}, f, n(sm), Equal.sym(Nat, n(sm), f, es), N.lt_le_trans(f, n(to), n(len), lt2, hto))
  +rest = FD.split(D.slice(X, Nat.add(f, 1n), Nat.sub(n(to), Nat.add(f, 1n))), 59)
  +p = Norm.chars(D.slice(X, n(j), Nat.sub(f, n(j))))
  +hr = Equal.trans(ML(), B.Info.ends.go(AL.mapc(rest)), B.Info.ends.go(AL.mapc(FD.split(D.slice(X, Nat.add(n(sm), 1n), Nat.sub(n(to), Nat.add(n(sm), 1n))), 59))), ENDS(len, t, to, (sm + 1 : U32)),
    Equal.cong(Nat, ML(), z => B.Info.ends.go(AL.mapc(FD.split(D.slice(X, Nat.add(z, 1n), Nat.sub(n(to), Nat.add(z, 1n))), 59))), f, n(sm), Equal.sym(Nat, n(sm), f, es)),
    ends_next(len, t, d, to, sm, h, sml))
  Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, B.Info.ends.go(AL.mapc(rest))), B.Info.ends.put(SEQ(len, t, to, j), p, ENDS(len, t, to, (sm + 1 : U32))),
    ENTQ(len, t, d, to, j, f, ke, rest, h, K.kj(len, t, d, to, j, h, hto, hjt),
      K.hfs_e(len, t, d, to, j, h, hto, hjt, hen, hse), LS.ts_lt(X, f, n(to), 59, lt2, hg2),
      K.hfk_e(len, t, d, to, j, h, hto, hjt, hen, hse)),
    Equal.cong(ML(), ML(), z => B.Info.ends.put(SEQ(len, t, to, j), p, z), B.Info.ends.go(AL.mapc(rest)), ENDS(len, t, to, (sm + 1 : U32)), hr))

# ---------------------------------------------------------------------------
# An END entry's value
# ---------------------------------------------------------------------------

def drop0(+s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      {==}

# The text of a .. b-1 with its first k characters dropped.
def drop_fld(+k: Nat, +xs: List<&2, U32>, +a: Nat, +b: Nat, +hab: {Nat.is_le(Nat.add(a, k), b) == True{} : Bool},
  +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {String.drop(Q.fld(xs, a, b), k) == Q.fld(xs, Nat.add(a, k), b) : String}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)) : {String.drop(Q.fld(xs, a, b), 0n) == Q.fld(xs, _, b) : String}
      drop0(Q.fld(xs, a, b))
    case 1n+(+q):
      +hp = G.lt_of(a, q, b, hab)
      +ea = N.add_assoc(a, 1n, q)
      %Equal.sym(String, Q.fld(xs, a, b), SCon{Chr{E.XV(xs, a)}, Q.fld(xs, Nat.add(a, 1n), b)}, E.fld_cons(xs, a, b, hp, hb)) :
        {String.drop(_, 1n+q) == Q.fld(xs, Nat.add(a, 1n+q), b) : String}
      %ea : {String.drop(Q.fld(xs, Nat.add(a, 1n), b), q) == Q.fld(xs, _, b) : String}
      drop_fld(q, xs, Nat.add(a, 1n), b, AB.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, Nat.add(a, 1n+q), Nat.add(Nat.add(a, 1n), q), Equal.sym(Nat, Nat.add(Nat.add(a, 1n), q), Nat.add(a, 1n+q), ea), hab), hb)

# The expected value: POS + len(REF) - 1.
def EV0(+pos: U32, +rl: U32) -> Nat:
  Nat.sub(Nat.add(n(pos), n(rl)), 1n)

# v - pos == rl - 1 with pos <= v and 1 <= rl: v is pos + rl - 1.
def vnat(+pos: U32, +rl: U32, +x: U32, +h1: {U32.is_le(pos, x) == True{} : Bool}, +h2: {U32.is_le(1, rl) == True{} : Bool},
  +h3: {U32.is_eq((x - pos : U32), (rl - 1 : U32)) == True{} : Bool}) -> {n(x) == EV0(pos, rl) : Nat}:
  +P = n(pos)
  +R = n(rl)
  +V = n(x)
  +e2 = Equal.cong(U32, Nat, z => n(z), (x - pos : U32), (rl - 1 : U32), U.is_eq_true((x - pos : U32), (rl - 1 : U32), h3))
  +e3 = Equal.trans(Nat, Nat.sub(V, P), n((x - pos : U32)), Nat.sub(R, 1n), Equal.sym(Nat, n((x - pos : U32)), Nat.sub(V, P), U.to_nat_sub_le(x, pos, h1)),
    Equal.trans(Nat, n((x - pos : U32)), n((rl - 1 : U32)), Nat.sub(R, 1n), e2, U.to_nat_sub_le(rl, 1, h2)))
  +l1 = Z.ule(pos, x, h1)
  +l2 = Z.ule(1, rl, h2)
  +ev = Equal.trans(Nat, V, Nat.add(P, Nat.sub(V, P)), Nat.add(P, Nat.sub(R, 1n)), Equal.sym(Nat, Nat.add(P, Nat.sub(V, P)), V, N.le_sub_add(P, V, l1)),
    Equal.cong(Nat, Nat, z => Nat.add(P, z), Nat.sub(V, P), Nat.sub(R, 1n), e3))
  +ec = Equal.trans(Nat, Nat.sub(Nat.add(P, R), 1n), Nat.sub(Nat.add(R, P), 1n), Nat.add(P, Nat.sub(R, 1n)),
    Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.add(P, R), Nat.add(R, P), N.add_comm(P, R)),
    Equal.trans(Nat, Nat.sub(Nat.add(R, P), 1n), Nat.add(Nat.sub(R, 1n), P), Nat.add(P, Nat.sub(R, 1n)), U.sub_add_comm(R, P, 1n, l2), N.add_comm(Nat.sub(R, 1n), P)))
  Equal.trans(Nat, V, Nat.add(P, Nat.sub(R, 1n)), EV0(pos, rl), ev, Equal.sym(Nat, EV0(pos, rl), Nat.add(P, Nat.sub(R, 1n)), ec))

# What GOOD passing says.
def gd5(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) ->
  {(Bool.not(seen) && vok && U32.is_le(pos, x) && U32.is_le(1, rl)) == True{} : Bool}:
  N.and_true_l(Bool.not(seen) && vok && U32.is_le(pos, x) && U32.is_le(1, rl), U32.is_eq((x - pos : U32), (rl - 1 : U32)), hg)

def gd4(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) ->
  {(Bool.not(seen) && vok && U32.is_le(pos, x)) == True{} : Bool}:
  N.and_true_l(Bool.not(seen) && vok && U32.is_le(pos, x), U32.is_le(1, rl), gd5(seen, vok, x, pos, rl, hg))

def gd3(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) ->
  {(Bool.not(seen) && vok) == True{} : Bool}:
  N.and_true_l(Bool.not(seen) && vok, U32.is_le(pos, x), gd4(seen, vok, x, pos, rl, hg))

def gd_seen(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) -> {seen == False{} : Bool}:
  LS.not_t(seen, N.and_true_l(Bool.not(seen), vok, gd3(seen, vok, x, pos, rl, hg)))

def gd_vok(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) -> {vok == True{} : Bool}:
  N.and_true_r(Bool.not(seen), vok, gd3(seen, vok, x, pos, rl, hg))

def gd_val(+seen: Bool, +vok: Bool, +x: U32, +pos: U32, +rl: U32, +hg: {M.GOOD(True{}, seen, vok, x, pos, rl) == True{} : Bool}) -> {n(x) == EV0(pos, rl) : Nat}:
  vnat(pos, rl, x, N.and_true_r(Bool.not(seen) && vok, U32.is_le(pos, x), gd4(seen, vok, x, pos, rl, hg)),
    N.and_true_r(Bool.not(seen) && vok && U32.is_le(pos, x), U32.is_le(1, rl), gd5(seen, vok, x, pos, rl, hg)),
    N.and_true_r(Bool.not(seen) && vok && U32.is_le(pos, x) && U32.is_le(1, rl), U32.is_eq((x - pos : U32), (rl - 1 : U32)), hg))

def hjm_of(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n(j), n((K.KE(len, t, to, j) - j : U32))), n(len)) == True{} : Bool}:
  +ke = K.KE(len, t, to, j)
  AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, n(ke), Nat.add(n(j), n((ke - j : U32))), Equal.sym(Nat, Nat.add(n(j), n((ke - j : U32))), n(ke), K.hsum(j, ke, K.kj(len, t, d, to, j, h, hto, hjt))), K.kl(len, t, d, to, j, h, hto, hjt))

# The '=' at ke (not a ';') comes before the next ';'.
def ke_f59(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool}) ->
  {Nat.is_le(Nat.add(n(K.KE(len, t, to, j)), 1n), K.F59(len, t, to, j)) == True{} : Bool}:
  +ke = K.KE(len, t, to, j)
  +X = Q.xs(len, t)
  +lt = K.ke_lt(len, t, d, to, j, h, hto, hjt, hen)
  +sm = E.step_miss(X, n(ke), n(to), 59, C.AT(len, t, ke), PF.step_get(len, t, d, ke, h, K.ke_len(len, t, d, to, j, h, hto, hjt, hen)), hse, lt)
  +r = PL.first_range(X, Nat.add(n(ke), 1n), n(to), 59, C.succ_le(n(ke), n(to), lt), K.hlx(len, t, d, n(to), h, hto))
  AB.subst(Nat, z => {Nat.is_le(Nat.add(n(ke), 1n), z) == True{} : Bool}, D.first(X, Nat.add(n(ke), 1n), n(to), 59), K.F59(len, t, to, j), Equal.sym(Nat, K.F59(len, t, to, j), D.first(X, Nat.add(n(ke), 1n), n(to), 59), sm),
    N.and_true_l(Nat.is_le(Nat.add(n(ke), 1n), D.first(X, Nat.add(n(ke), 1n), n(to), 59)), Nat.is_le(D.first(X, Nat.add(n(ke), 1n), n(to), 59), n(to)), r))

def pct1(+len: U32, +t: AT.Tree<U32>, +a: Nat, +b: Nat, +pos: U32, r: PO.PCT(len, t, a, b, pos)) ->
  {B.Pos.read(Q.fld(Q.xs(len, t), a, b)) == Some{n(pos)} : Maybe<&2, Nat>}:
  match r:
    case (x, y):
      x

def NV(+len: U32, +t: AT.Tree<U32>, +to: U32, +j: U32) -> M.Nv:
  M.NUM(len, t, (K.KE(len, t, to, j) + 1 : U32), K.SM(len, t, to, j))

# An END entry the scan took: its value, read as B.Info.ends reads it (the
# text after "END="), is POS + len(REF) - 1.
def end_val(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +pos: U32, +rl: U32, +seen: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool},
  +hg: {M.GOOD(True{}, seen, M.Nv.ok(NV(len, t, to, j)), M.Nv.v(NV(len, t, to, j)), pos, rl) == True{} : Bool}) ->
  {B.Pos.read(String.drop(Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j)))), 4n)) == Some{EV0(pos, rl)} : Maybe<&2, Nat>}:
  +X = Q.xs(len, t)
  +ke = K.KE(len, t, to, j)
  +sm = K.SM(len, t, to, j)
  +f = K.F59(len, t, to, j)
  +x = M.Nv.v(NV(len, t, to, j))
  +hjk = K.kj(len, t, d, to, j, h, hto, hjt)
  +lk = K.ke_len(len, t, d, to, j, h, hto, hjt, hen)
  +es = K.nsm(len, t, d, to, j, h, hto, hjt)
  +hkf = ke_f59(len, t, d, to, j, h, hto, hjt, hen, hse)
  +e3a = Equal.trans(Nat, Nat.sub(n(ke), n(j)), n((ke - j : U32)), 3n, Equal.sym(Nat, n((ke - j : U32)), Nat.sub(n(ke), n(j)), LP.sub_u(ke, j, hjk)),
    Equal.cong(U32, Nat, z => n(z), (ke - j : U32), 3, k3m(len, t, j, (ke - j : U32), hk)))
  +e3 = Equal.trans(Nat, n(ke), Nat.add(n(j), Nat.sub(n(ke), n(j))), Nat.add(n(j), 3n), Equal.sym(Nat, Nat.add(n(j), Nat.sub(n(ke), n(j))), n(ke), N.le_sub_add(n(j), n(ke), hjk)),
    Equal.cong(Nat, Nat, z => Nat.add(n(j), z), Nat.sub(n(ke), n(j)), 3n, e3a))
  +eq4 = Equal.trans(Nat, Nat.add(n(j), 4n), Nat.add(Nat.add(n(j), 3n), 1n), Nat.add(n(ke), 1n), Equal.sym(Nat, Nat.add(Nat.add(n(j), 3n), 1n), Nat.add(n(j), 4n), N.add_assoc(n(j), 3n, 1n)),
    Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(n(j), 3n), n(ke), Equal.sym(Nat, n(ke), Nat.add(n(j), 3n), e3)))
  +hab = AB.subst(Nat, z => {Nat.is_le(z, f) == True{} : Bool}, Nat.add(n(ke), 1n), Nat.add(n(j), 4n), Equal.sym(Nat, Nat.add(n(j), 4n), Nat.add(n(ke), 1n), eq4), hkf)
  +hfn = N.le_trans(f, n(to), n(len), K.smt(len, t, d, to, j, h, hto, hjt), hto)
  +hfx = K.hlx(len, t, d, f, h, hfn)
  +i1 = LP.inc_len(len, t, d, ke, h, lk)
  +hft2 = AB.subst(Nat, z => {Nat.is_le(z, n(sm)) == True{} : Bool}, Nat.add(n(ke), 1n), n((ke + 1 : U32)), Equal.sym(Nat, n((ke + 1 : U32)), Nat.add(n(ke), 1n), i1),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(n(ke), 1n), z) == True{} : Bool}, f, n(sm), Equal.sym(Nat, n(sm), f, es), hkf))
  +htl = AB.subst(Nat, z => {Nat.is_le(z, n(len)) == True{} : Bool}, f, n(sm), Equal.sym(Nat, n(sm), f, es), hfn)
  +pr = pct1(len, t, n((ke + 1 : U32)), n(sm), x,
    PO.pos_core(len, t, d, (ke + 1 : U32), sm, x, Nat.pow(2n, 32n), U32.to_nat(429496729), {==}, {==}, LN.QM(Nat.pow(2n, 32n), {==}),
      h, hft2, htl, gd_vok(seen, M.Nv.ok(NV(len, t, to, j)), x, pos, rl, hg), {==}))
  %Equal.sym(String, String.drop(Q.fld(X, n(j), f), 4n), Q.fld(X, Nat.add(n(j), 4n), f), drop_fld(4n, X, n(j), f, hab, hfx)) : {B.Pos.read(_) == Some{EV0(pos, rl)} : Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.add(n(j), 4n), Nat.add(n(ke), 1n), eq4) : {B.Pos.read(Q.fld(X, _, f)) == Some{EV0(pos, rl)} : Maybe<&2, Nat>}
  %i1 : {B.Pos.read(Q.fld(X, _, f)) == Some{EV0(pos, rl)} : Maybe<&2, Nat>}
  %es : {B.Pos.read(Q.fld(X, n((ke + 1 : U32)), _)) == Some{EV0(pos, rl)} : Maybe<&2, Nat>}
  %gd_val(seen, M.Nv.ok(NV(len, t, to, j)), x, pos, rl, hg) : {B.Pos.read(Q.fld(X, n((ke + 1 : U32)), n(sm))) == Some{_} : Maybe<&2, Nat>}
  pr

# ---------------------------------------------------------------------------
# The scan, entry by entry
# ---------------------------------------------------------------------------

# What the scan knows of the END values l of the entries still to read: none
# once one was seen, else they pass B.Info.end_ok.go for E.
def HEL(seen: Bool, +l: ML(), +E: Nat) -> Type:
  match seen:
    case True{}:
      {l == Nil{} : ML()}
    case False{}:
      {B.Info.end_ok.go(l, E) == True{} : Bool}

def HE(seen: Bool, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +j: U32) -> Type:
  HEL(seen, ENDS(len, t, to, j), EV0(pos, rl))

def he_nil(+seen: Bool, +l: ML(), +E: Nat, +hl: {l == Nil{} : ML()}) -> HEL(seen, l, E):
  match seen:
    case True{}:
      hl
    case False{}:
      %Equal.sym(ML(), l, Nil{}, hl) : {B.Info.end_ok.go(_, E) == True{} : Bool}
      {==}

def he_one(+seen: Bool, +l: ML(), +E: Nat, +hl: {l == Some{E} <> Nil{} : ML()}, +hs: {seen == False{} : Bool}) -> HEL(seen, l, E):
  %Equal.sym(Bool, seen, False{}, hs) : HEL(_, l, E)
  %Equal.sym(ML(), l, Some{E} <> Nil{}, hl) : {B.Info.end_ok.go(_, E) == True{} : Bool}
  N.eq_refl(E)

def he_eq(+seen: Bool, +l: ML(), +r: ML(), +E: Nat, +hl: {l == r : ML()}, hr: HEL(seen, r, E)) -> HEL(seen, l, E):
  AB.subst(ML(), z => HEL(seen, z, E), r, l, Equal.sym(ML(), l, r, hl), hr)

def ef_ed(+q: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +j: U32, +seen: Bool) ->
  {M.EG(q, len, t, to, pos, rl, M.ED{j, False{}, seen, False{}}) == False{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+k:
      {==}

def ew_false(+end: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32, +sm: U32, +seen: Bool) ->
  {M.EG(q, len, t, to, pos, rl, M.EW(False{}, seen, end, sm)) == False{} : Bool}:
  match end:
    case True{}:
      ef_ed(q, len, t, to, pos, rl, sm, seen)
    case False{}:
      ef_ed(q, len, t, to, pos, rl, (sm + 1 : U32), seen)

def no(+b: Bool, -G: Type, +hf: {b == False{} : Bool}, +ht: {b == True{} : Bool}) -> G:
  Empty.absurd(G, LS.ft(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hf), ht)))

def EIH(+q: Nat, +len: U32, +t: AT.Tree<U32>, +to: U32, +pos: U32, +rl: U32) -> Type:
  @jj: U32 -> @sn: Bool -> {Nat.is_le(n(jj), n(to)) == True{} : Bool} -> {M.EG(q, len, t, to, pos, rl, M.ED{jj, True{}, sn, True{}}) == True{} : Bool} -> HE(sn, len, t, to, pos, rl, jj)

def SEQf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == False{} : Bool}) -> {SEQ(len, t, to, j) == False{} : Bool}:
  k3false(len, t, d, j, (K.KE(len, t, to, j) - j : U32), h, hjm_of(len, t, d, to, j, h, hto, hjt), hk)

def SEQt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +j: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == True{} : Bool}) -> {SEQ(len, t, to, j) == True{} : Bool}:
  k3true(len, t, d, j, (K.KE(len, t, to, j) - j : U32), h, hjm_of(len, t, d, to, j, h, hto, hjt), hk)

# A put whose key test is False adds nothing.
def put_f(+b: Bool, +p: String, +r: ML(), +hb: {b == False{} : Bool}) -> {B.Info.ends.put(b, p, r) == r : ML()}:
  %Equal.sym(Bool, b, False{}, hb) : {B.Info.ends.put(_, p, r) == r : ML()}
  {==}

def put_t(+b: Bool, +p: String, +r: ML(), +E: Nat, +hb: {b == True{} : Bool}, +hv: {B.Pos.read(String.drop(p, 4n)) == Some{E} : Maybe<&2, Nat>}, +hr: {r == Nil{} : ML()}) ->
  {B.Info.ends.put(b, p, r) == Some{E} <> Nil{} : ML()}:
  %Equal.sym(Bool, b, True{}, hb) : {B.Info.ends.put(_, p, r) == Some{E} <> Nil{} : ML()}
  %Equal.sym(Maybe<&2, Nat>, B.Pos.read(String.drop(p, 4n)), Some{E}, hv) : {_ <> r == Some{E} <> Nil{} : ML()}
  %Equal.sym(ML(), r, Nil{}, hr) : {Some{E} <> _ == Some{E} <> Nil{} : ML()}
  {==}

# '=' after a key that is not END: the value is skipped.
def eeq2(+b2: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +pos: U32, +rl: U32, +j: U32, +seen: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == False{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool},
  +hb2: {U32.is_eq(K.SM(len, t, to, j), to) == b2 : Bool},
  +hok: {M.EG(q, len, t, to, pos, rl, M.EW(True{}, seen, b2, K.SM(len, t, to, j))) == True{} : Bool},
  ih: EIH(q, len, t, to, pos, rl)) ->
  HE(seen, len, t, to, pos, rl, j):
  match b2:
    case True{}:
      +sq = SEQf(len, t, d, to, j, h, hto, hjt, hk)
      +p = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j))))
      he_nil(seen, ENDS(len, t, to, j), EV0(pos, rl), Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, Nil{}), Nil{},
        e_eq_t(len, t, d, to, j, h, hto, hjt, hen, hse, hb2), put_f(SEQ(len, t, to, j), p, Nil{}, sq)))
    case False{}:
      +sq = SEQf(len, t, d, to, j, h, hto, hjt, hk)
      +p = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j))))
      +sm = K.SM(len, t, to, j)
      +lt = K.sm_lt(len, t, d, to, j, h, hto, hjt, hb2)
      he_eq(seen, ENDS(len, t, to, j), ENDS(len, t, to, (sm + 1 : U32)), EV0(pos, rl),
        Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, ENDS(len, t, to, (sm + 1 : U32))), ENDS(len, t, to, (sm + 1 : U32)),
          e_eq_f(len, t, d, to, j, h, hto, hjt, hen, hse, hb2), put_f(SEQ(len, t, to, j), p, ENDS(len, t, to, (sm + 1 : U32)), sq)),
        ih((sm + 1 : U32), seen, K.c1_le(len, t, d, to, sm, h, N.lt_le_trans(n(sm), n(to), n(len), lt, hto), lt), hok))

# An END entry with a value: it must be the first, with the value POS +
# len(REF) - 1, and no END entry may follow.
def ev2(+g: Bool, +b2: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +pos: U32, +rl: U32, +j: U32, +seen: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == True{} : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == False{} : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == False{} : Bool},
  +hg: {M.GOOD(True{}, seen, M.Nv.ok(NV(len, t, to, j)), M.Nv.v(NV(len, t, to, j)), pos, rl) == g : Bool},
  +hb2: {U32.is_eq(K.SM(len, t, to, j), to) == b2 : Bool},
  +hok: {M.EG(q, len, t, to, pos, rl, M.EW(g, True{}, b2, K.SM(len, t, to, j))) == True{} : Bool},
  ih: EIH(q, len, t, to, pos, rl)) ->
  HE(seen, len, t, to, pos, rl, j):
  match g b2:
    case False{} _:
      no(M.EG(q, len, t, to, pos, rl, M.EW(False{}, True{}, b2, K.SM(len, t, to, j))), HE(seen, len, t, to, pos, rl, j),
        ew_false(b2, q, len, t, to, pos, rl, K.SM(len, t, to, j), True{}), hok)
    case True{} True{}:
      +E = EV0(pos, rl)
      +sq = SEQt(len, t, d, to, j, h, hto, hjt, hk)
      +p = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j))))
      +hv = end_val(len, t, d, to, j, pos, rl, seen, h, hto, hjt, hk, hen, hse, hg)
      +hs = gd_seen(seen, M.Nv.ok(NV(len, t, to, j)), M.Nv.v(NV(len, t, to, j)), pos, rl, hg)
      he_one(seen, ENDS(len, t, to, j), E, Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, Nil{}), Some{E} <> Nil{},
        e_eq_t(len, t, d, to, j, h, hto, hjt, hen, hse, hb2), put_t(SEQ(len, t, to, j), p, Nil{}, E, sq, hv, {==})), hs)
    case True{} False{}:
      +E = EV0(pos, rl)
      +sq = SEQt(len, t, d, to, j, h, hto, hjt, hk)
      +p = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(K.F59(len, t, to, j), n(j))))
      +hv = end_val(len, t, d, to, j, pos, rl, seen, h, hto, hjt, hk, hen, hse, hg)
      +hs = gd_seen(seen, M.Nv.ok(NV(len, t, to, j)), M.Nv.v(NV(len, t, to, j)), pos, rl, hg)
      +sm = K.SM(len, t, to, j)
      +lt = K.sm_lt(len, t, d, to, j, h, hto, hjt, hb2)
      hr = ih((sm + 1 : U32), True{}, K.c1_le(len, t, d, to, sm, h, N.lt_le_trans(n(sm), n(to), n(len), lt, hto), lt), hok)
      he_one(seen, ENDS(len, t, to, j), E, Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, ENDS(len, t, to, (sm + 1 : U32))), Some{E} <> Nil{},
        e_eq_f(len, t, d, to, j, h, hto, hjt, hen, hse, hb2), put_t(SEQ(len, t, to, j), p, ENDS(len, t, to, (sm + 1 : U32)), E, sq, hv, hr)), hs)

# One step of the scan from an entry at j (ok so far).
def estep(+isend: Bool, +en: Bool, +se: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +pos: U32, +rl: U32, +j: U32, +seen: Bool,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hk: {M.KEY3(len, t, j, (K.KE(len, t, to, j) - j : U32)) == isend : Bool},
  +hen: {U32.is_eq(K.KE(len, t, to, j), to) == en : Bool},
  +hse: {U32.is_eq(C.AT(len, t, K.KE(len, t, to, j)), 59) == se : Bool},
  +hok: {M.EG(q, len, t, to, pos, rl, M.EE(True{}, seen, isend, en, se, len, t, K.KE(len, t, to, j), to, pos, rl)) == True{} : Bool},
  ih: EIH(q, len, t, to, pos, rl)) ->
  HE(seen, len, t, to, pos, rl, j):
  match isend en se:
    case False{} True{} _:
      +p = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(n(to), n(j))))
      he_nil(seen, ENDS(len, t, to, j), EV0(pos, rl), Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), p, Nil{}), Nil{},
        e_end(len, t, d, to, j, h, hto, hjt, hen), put_f(SEQ(len, t, to, j), p, Nil{}, SEQf(len, t, d, to, j, h, hto, hjt, hk))))
    case False{} False{} True{}:
      +ke = K.KE(len, t, to, j)
      +pk = Norm.chars(D.slice(Q.xs(len, t), n(j), Nat.sub(n(ke), n(j))))
      he_eq(seen, ENDS(len, t, to, j), ENDS(len, t, to, (ke + 1 : U32)), EV0(pos, rl),
        Equal.trans(ML(), ENDS(len, t, to, j), B.Info.ends.put(SEQ(len, t, to, j), pk, ENDS(len, t, to, (ke + 1 : U32))), ENDS(len, t, to, (ke + 1 : U32)),
          e_semi(len, t, d, to, j, h, hto, hjt, hen, hse), put_f(SEQ(len, t, to, j), pk, ENDS(len, t, to, (ke + 1 : U32)), SEQf(len, t, d, to, j, h, hto, hjt, hk))),
        ih((ke + 1 : U32), seen, K.c1_le(len, t, d, to, ke, h, K.ke_len(len, t, d, to, j, h, hto, hjt, hen), K.ke_lt(len, t, d, to, j, h, hto, hjt, hen)), hok))
    case False{} False{} False{}:
      eeq2(U32.is_eq(K.SM(len, t, to, j), to), q, len, t, d, to, pos, rl, j, seen, h, hto, hjt, hk, hen, hse, {==}, hok, ih)
    case True{} False{} False{}:
      ev2(M.GOOD(True{}, seen, M.Nv.ok(NV(len, t, to, j)), M.Nv.v(NV(len, t, to, j)), pos, rl), U32.is_eq(K.SM(len, t, to, j), to), q, len, t, d, to, pos, rl, j, seen, h, hto, hjt, hk, hen, hse, {==}, {==}, hok, ih)
    case True{} True{} _:
      +ke = K.KE(len, t, to, j)
      no(M.EG(q, len, t, to, pos, rl, M.ED{ke, False{}, seen, False{}}), HE(seen, len, t, to, pos, rl, j), ef_ed(q, len, t, to, pos, rl, ke, seen), hok)
    case True{} False{} True{}:
      +ke = K.KE(len, t, to, j)
      no(M.EG(q, len, t, to, pos, rl, M.ED{ke, False{}, seen, False{}}), HE(seen, len, t, to, pos, rl, j), ef_ed(q, len, t, to, pos, rl, ke, seen), hok)

def eloop(+k: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +to: U32, +pos: U32, +rl: U32, +j: U32, +seen: Bool, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hto: {Nat.is_le(n(to), n(len)) == True{} : Bool}, +hjt: {Nat.is_le(n(j), n(to)) == True{} : Bool},
  +hok: {M.EG(k, len, t, to, pos, rl, M.ED{j, True{}, seen, True{}}) == True{} : Bool}) ->
  HE(seen, len, t, to, pos, rl, j):
  match k:
    case 0n:
      Empty.absurd(HE(seen, len, t, to, pos, rl, j), LS.ft(hok))
    case 1n+q:
      +ke = K.KE(len, t, to, j)
      estep(M.KEY3(len, t, j, (ke - j : U32)), U32.is_eq(ke, to), U32.is_eq(C.AT(len, t, ke), 59), q, len, t, d, to, pos, rl, j, seen, h, hto, hjt, {==}, {==}, {==}, hok,
        +jj => +sn => +a => +b => eloop(q, len, t, d, to, pos, rl, jj, sn, h, hto, a, b))

# INFO (bytes e6 + 1 .. e7 - 1) passed NF.endok for POS pos and a REF of rl
# bytes: B.Info.end_ok holds for POS + len(REF) - 1.
def info_end(+len: U32, +t: AT.Tree<U32>, +d: Nat, +e6: U32, +e7: U32, +pos: U32, +rl: U32, +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +h6: {Nat.is_lt(n(e6), n(len)) == True{} : Bool}, +h67: {Nat.is_le(n((e6 + 1 : U32)), n(e7)) == True{} : Bool}, +h7: {Nat.is_le(n(e7), n(len)) == True{} : Bool},
  +hn: {M.EK(len, t, (e6 + 1 : U32), e7, pos, rl) == True{} : Bool}) ->
  {B.Info.end_ok(Q.fld(Q.xs(len, t), Q.nx(e6), n(e7)), EV0(pos, rl)) == True{} : Bool}:
  +X = Q.xs(len, t)
  +ys = D.slice(X, Nat.add(n(e6), 1n), Nat.sub(n(e7), Nat.add(n(e6), 1n)))
  %Equal.sym(List<&2, String>, String.split(Norm.chars(ys), ';'), AL.mapc(FD.split(ys, 59)), K.csplit_g(ys, 59)) :
    {B.Info.end_ok.go(B.Info.ends.go(_), EV0(pos, rl)) == True{} : Bool}
  AB.subst(Nat, z => {B.Info.end_ok.go(B.Info.ends.go(AL.mapc(FD.split(D.slice(X, z, Nat.sub(n(e7), z)), 59))), EV0(pos, rl)) == True{} : Bool}, n((e6 + 1 : U32)), Nat.add(n(e6), 1n),
    LP.inc_len(len, t, d, e6, h, h6), eloop(n((e7 - (e6 + 1 : U32) + 2 : U32)), len, t, d, e7, pos, rl, (e6 + 1 : U32), False{}, h, h7, h67, hn))
