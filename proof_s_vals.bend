import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_cut.bend as K
import ./proof_s_scan.bend as SC
import ./proof_s_read.bend as RD
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-fields@0.1.1.0/LAWS.bend as FL
import lawful-fields@0.1.1.0/PROOF.bend as FP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's per-allele values (norm_split.bend's pick, picks, vals)
# write what B.Vals.split gives. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def Ss() -> Data:
  List<&2, String>

def Ns() -> Data:
  List<&2, Nat>

def LL() -> Data:
  List<&2, List<&2, U32>>

def MS() -> Data:
  Maybe<&2, String>

def STR(+m: MS()) -> String:
  match m:
    case Some{+s}:
      s
    case None{}:
      ""

def ISS(+m: MS()) -> Bool:
  match m:
    case Some{+s}:
      True{}
    case None{}:
      False{}

# The values of x (separated by ',').
def VS(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg) -> Ss():
  String.split(WT.TX(len, t, x), ',')

# ---------------------------------------------------------------------------
# Lists of texts
# ---------------------------------------------------------------------------

def split_chs(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +c: U32, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}) ->
  {String.split(WT.TX(len, t, NS.Rg{a, z}), Chr{c}) == K.CHS(K.SP(len, t, a, z, c)) : Ss()}:
  +xs = D.slice(W.V(len, t), n(a), Nat.sub(n(z), n(a)))
  %Equal.sym(String, WT.TX(len, t, NS.Rg{a, z}), NR.chars(xs), RD.tx_eq(len, t, a, z, haz)) : {String.split(_, Chr{c}) == K.CHS(K.SP(len, t, a, z, c)) : Ss()}
  %K.text_chars(xs) : {String.split(_, Chr{c}) == K.CHS(K.SP(len, t, a, z, c)) : Ss()}
  %Equal.sym(Ss(), String.split(FD.text(xs), Chr{c}), FD.texts(FD.split(xs, c)), FL.split_text(xs, c)) : {_ == K.CHS(K.SP(len, t, a, z, c)) : Ss()}
  K.texts_chs(FD.split(xs, c))

def MCH(+m: Maybe<&2, List<&2, U32>>) -> MS():
  match m:
    case Some{+p}:
      Some{NR.chars(p)}
    case None{}:
      None{}

law get_chs:
  for +ps: LL()
  for +j: Nat
  {List.get(&2, String, K.CHS(ps), j) == MCH(List.get(&2, List<&2, U32>, ps, j)) : MS()}

def get_chs(ps, j):
  match ps j:
    case Nil{} _:
      {==}
    case Con{+p, +r} 0n:
      {==}
    case Con{+p, +r} 1n+q:
      get_chs(r, q)

law len_chs:
  for +ps: LL()
  {List.length(&2, String, K.CHS(ps)) == List.length(&2, List<&2, U32>, ps) : Nat}

def len_chs(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %Equal.sym(Nat, List.length(&2, String, K.CHS(r)), List.length(&2, List<&2, U32>, r), len_chs(r)) : {1n+_ == 1n+List.length(&2, List<&2, U32>, r) : Nat}
      {==}

law get_some:
  for +vs: Ss()
  for +j: Nat
  for +h: {Nat.is_lt(j, List.length(&2, String, vs)) == True{} : Bool}
  {List.get(&2, String, vs, j) == Some{STR(List.get(&2, String, vs, j))} : MS()}

def get_some(vs, j, h):
  match vs j:
    case Nil{} _:
      Empty.absurd({List.get(&2, String, Nil{}, j) == Some{STR(List.get(&2, String, Nil{}, j))} : MS()},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, N.lt_zero(j)), h)))
    case Con{+v, +r} 0n:
      {==}
    case Con{+v, +r} 1n+q:
      get_some(r, q, h)

# The values whose places are js, separated by ',' (sep before all but the first).
def PKS(+vs: Ss(), js: Ns(), +first: Bool) -> String:
  match js:
    case Nil{}:
      ""
    case Con{+j, r}:
      String.append(WT.SEPS(first, 44), String.append(STR(List.get(&2, String, vs, j)), PKS(vs, r, False{})))

def GETS(+vs: Ss(), js: Ns()) -> Ss():
  match js:
    case Nil{}:
      Nil{}
    case Con{+j, r}:
      Con{STR(List.get(&2, String, vs, j)), GETS(vs, r)}

# Every place is at most k.
def ALE(js: Ns(), +k: Nat) -> Bool:
  match js:
    case Nil{}:
      True{}
    case Con{+j, r}:
      Bool.and(Nat.is_le(j, k), ALE(r, k))

law vpick:
  for +vs: Ss()
  for +js: Ns()
  for +k: Nat
  for +hl: {List.length(&2, String, vs) == 1n+k : Nat}
  for +ha: {ALE(js, k) == True{} : Bool}
  {B.Vals.pick(vs, js) == Some{GETS(vs, js)} : Maybe<&2, Ss()>}

def vpick(vs, js, k, hl, ha):
  match js:
    case Nil{}:
      {==}
    case Con{+j, +r}:
      +hj = N.and_true_l(Nat.is_le(j, k), ALE(r, k), ha)
      +hr = N.and_true_r(Nat.is_le(j, k), ALE(r, k), ha)
      +hlt = {%Equal.sym(Nat, List.length(&2, String, vs), 1n+k, hl) : {Nat.is_lt(j, _) == True{} : Bool}; %N.le_succ_lt(j, 1n+k) : {_ == True{} : Bool}; hj : {Nat.is_lt(j, List.length(&2, String, vs)) == True{} : Bool}}
      %Equal.sym(MS(), List.get(&2, String, vs, j), Some{STR(List.get(&2, String, vs, j))}, get_some(vs, j, hlt)) : {B.Vals.pick.cons(_, B.Vals.pick(vs, r)) == Some{GETS(vs, Con{j, r})} : Maybe<&2, Ss()>}
      %Equal.sym(Maybe<&2, Ss()>, B.Vals.pick(vs, r), Some{GETS(vs, r)}, vpick(vs, r, k, hl, hr)) : {B.Vals.pick.cons(Some{STR(List.get(&2, String, vs, j))}, _) == Some{GETS(vs, Con{j, r})} : Maybe<&2, Ss()>}
      {==}

law jg_gets:
  for +vs: Ss()
  for +js: Ns()
  for +h: String
  {String.join.go(GETS(vs, js), h, ",") == String.append(h, PKS(vs, js, False{})) : String}

def jg_gets(vs, js, h):
  match js:
    case Nil{}:
      Equal.sym(String, String.append(h, ""), h, MN.str_nil(h))
    case Con{+j, +r}:
      +y = STR(List.get(&2, String, vs, j))
      %Equal.sym(String, String.join.go(GETS(vs, r), y, ","), String.append(y, PKS(vs, r, False{})), jg_gets(vs, r, y)) : {String.append(h, String.append(",", _)) == String.append(h, PKS(vs, Con{j, r}, False{})) : String}
      {==}

law join_gets:
  for +vs: Ss()
  for +js: Ns()
  {String.join(GETS(vs, js), ",") == PKS(vs, js, True{}) : String}

def join_gets(vs, js):
  match js:
    case Nil{}:
      {==}
    case Con{+j, +r}:
      jg_gets(vs, r, STR(List.get(&2, String, vs, j)))

# ---------------------------------------------------------------------------
# pick, picks
# ---------------------------------------------------------------------------

def tx_slr(+len: U32, +t: AT.Tree<U32>, +r: NS.Rg) -> {WT.TX(len, t, r) == NR.chars(SC.SLR(len, t, r)) : String}:
  match r:
    case NS.Rg{+a, +z}:
      {==}

def pick.got(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +j: Nat, +R: NS.Rg, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  +hg: {List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), j) == Some{SC.SLR(len, t, R)} : Maybe<&2, List<&2, U32>>}) ->
  {WT.TX(len, t, R) == STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)) : String}:
  %Equal.sym(Ss(), String.split(WT.TX(len, t, NS.Rg{a, z}), ','), K.CHS(K.SP(len, t, a, z, 44)), split_chs(len, t, a, z, 44, haz)) :
    {WT.TX(len, t, R) == STR(List.get(&2, String, _, j)) : String}
  %Equal.sym(MS(), List.get(&2, String, K.CHS(K.SP(len, t, a, z, 44)), j), MCH(List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), j)), get_chs(K.SP(len, t, a, z, 44), j)) :
    {WT.TX(len, t, R) == STR(_) : String}
  %Equal.sym(Maybe<&2, List<&2, U32>>, List.get(&2, List<&2, U32>, K.SP(len, t, a, z, 44), j), Some{SC.SLR(len, t, R)}, hg) :
    {WT.TX(len, t, R) == STR(MCH(_)) : String}
  tx_slr(len, t, R)

def pick.in(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32, +j: Nat,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool},
  nt: SC.NTR(len, t, a, z, j, NS.nth(C.BT(len, t), NS.Rg{a, z}, j))) ->
  S.WS(len, t, NS.pick.w(NS.nth(C.BT(len, t), NS.Rg{a, z}, j), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), True{}):
  (+R, e) = nt
  (eq, e2) = e
  (hg, hpR) = e2
  %Equal.sym(D.Bytes & NS.Rg, NS.nth(C.BT(len, t), NS.Rg{a, z}, j), (C.BT(len, t), R), eq) :
    S.WS(len, t, NS.pick.w(_, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), True{})
  S.ws_eq(len, t, NS.cpr(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, R), W.Wm{W.V(l2, t2), p, ok}, WT.TX(len, t, R), STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), True{}, True{},
    pick.got(len, t, a, z, j, R, haz, hg), {==},
    S.ws_cpr(len, t, d, hl, R, hpR, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp)))

def pick.c(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +k: Nat, +hk: {Nat.add(k, 1n) == SC.NP(len, t, a, z, 44) : Nat}, +j: Nat,
  +hc: {Nat.is_le(j, k) == c : Bool}, -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.pick.if(c, w, NS.Rg{a, z}, j), m0, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), c):
  match c:
    case True{}:
      +haz = W.pv_a(len, a, z, hpx)
      +hzl = W.pv_z(len, a, z, hpx)
      +hj = {%hk : {Nat.is_lt(j, _) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, N.add_one(k)) : {Nat.is_lt(j, _) == True{} : Bool};
        %N.le_succ_lt(j, 1n+k) : {_ == True{} : Bool};
        hc : {Nat.is_lt(j, SC.NP(len, t, a, z, 44)) == True{} : Bool}}
      S.ws_at(len, t, w, v => NS.pick.if(True{}, v, NS.Rg{a, z}, j), m0, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), True{}, r,
        +l2 => +t2 => +p => +ok => +h => +hp => pick.in(len, t, d, hl, a, z, j, l2, t2, p, ok, h, hp, haz, SC.nth_t(len, t, d, a, z, j, hl, haz, hzl, hj)))
    case False{}:
      S.ws_fail(len, t, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), False{}, w, m0, r)

# Value j (of k + 1) of x.
def ws_pick(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +k: Nat, +hk: {Nat.add(k, 1n) == SC.NP(len, t, a, z, 44) : Nat}, +j: Nat,
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.pick(w, NS.Rg{a, z}, k, j), m0, STR(List.get(&2, String, VS(len, t, NS.Rg{a, z}), j)), Nat.is_le(j, k)):
  pick.c(Nat.is_le(j, k), len, t, d, hl, a, z, hpx, k, hk, j, {==}, w, m0, r)

law picks_t:
  for +js: Ns()
  for +first: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +a: U32
  for +z: U32
  for +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}
  for +k: Nat
  for +hk: {Nat.add(k, 1n) == SC.NP(len, t, a, z, 44) : Nat}
  for -w: NS.Sw
  for +m0: W.Wm
  for r: W.Rel(len, t, w, m0)
  S.WS(len, t, NS.picks(js, w, NS.Rg{a, z}, k, first), m0, PKS(VS(len, t, NS.Rg{a, z}), js, first), ALE(js, k))

def picks_t(js, first, len, t, d, hl, a, z, hpx, k, hk, w, m0, r):
  match js:
    case Nil{}:
      S.ws_ret(len, t, w, m0, r)
    case Con{+j, +rr}:
      +x = {NS.Rg{a, z} : NS.Rg}
      +vs = VS(len, t, x)
      +sj = STR(List.get(&2, String, vs, j))
      S.ws_seq(len, t, NS.sep(w, first, 44), v => NS.picks(rr, NS.pick(v, x, k, j), x, k, False{}), m0,
        WT.SEPS(first, 44), String.append(sj, PKS(vs, rr, False{})), True{}, Bool.and(Nat.is_le(j, k), ALE(rr, k)),
        S.ws_sep(len, t, d, hl, first, 44, {==}, w, m0, r),
        +m1 => r1 => S.ws_seq(len, t, NS.pick(NS.sep(w, first, 44), x, k, j), v => NS.picks(rr, v, x, k, False{}), m1,
          sj, PKS(vs, rr, False{}), Nat.is_le(j, k), ALE(rr, k),
          ws_pick(len, t, d, hl, a, z, hpx, k, hk, j, NS.sep(w, first, 44), m1, r1),
          +m2 => r2 => picks_t(rr, False{}, len, t, d, hl, a, z, hpx, k, hk, NS.pick(NS.sep(w, first, 44), x, k, j), m2, r2)))

# pix: the picks of B.Vals.idx, written out.
def pix_g(+c: Bool, -w: NS.Sw, +x: NS.Rg, +k: Nat, +i: Nat) ->
  {NS.pix.g(c, w, x, k, i) == NS.picks(Bool.pick(Ns(), c, [0n, i], [0n, B.Gt.index(0n, i), B.Gt.index(i, i)]), w, x, k, True{}) : NS.Sw}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pix_eq(+num: B.Num, +p: Nat, +i: Nat, -w: NS.Sw, +x: NS.Rg, +k: Nat) ->
  {NS.pix(num, p, i, w, x, k) == NS.picks(B.Vals.idx(num, p, i), w, x, k, True{}) : NS.Sw}:
  match num:
    case B.NumA{}:
      {==}
    case B.NumR{}:
      {==}
    case B.NumG{}:
      pix_g(Nat.is_eq(p, 1n), w, x, k, i)
    case B.NumOther{}:
      {==}
    case B.NumUnknown{}:
      {==}

# ---------------------------------------------------------------------------
# vals (B.Vals.split)
# ---------------------------------------------------------------------------

def VSPL(+num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +len: U32, +t: AT.Tree<U32>, +x: NS.Rg) -> MS():
  B.Vals.split(num, na, cp, i, WT.TX(len, t, x))

def KEEP(+num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +vs: Ss(), +L: Nat) -> MS():
  Bool.pick(MS(), B.Vals.fits(B.Vals.expected_count(num, na, B.Vals.copies(cp, na, L)), L),
    B.Vals.join(B.Vals.pick(vs, B.Vals.idx(num, B.Vals.copies(cp, na, L), i))), None{})

# The places kept are all values: the record's values, joined.
def vals.got(+vs: Ss(), +js: Ns(), +k: Nat, +V0: MS(),
  +eL: {List.length(&2, String, vs) == 1n+k : Nat}, +ha: {ALE(js, k) == True{} : Bool},
  +ev2: {V0 == B.Vals.join(B.Vals.pick(vs, js)) : MS()}) ->
  ({ISS(V0) == True{} : Bool} & {PKS(vs, js, True{}) == STR(V0) : String}):
  +e3 = {%vpick(vs, js, k, eL, ha) : {V0 == B.Vals.join(_) : MS()}; ev2 : {V0 == Some{String.join(GETS(vs, js), ",")} : MS()}}
  +e4 = {%join_gets(vs, js) : {V0 == Some{_} : MS()}; e3 : {V0 == Some{PKS(vs, js, True{})} : MS()}}
  ({%Equal.sym(MS(), V0, Some{PKS(vs, js, True{})}, e4) : {ISS(_) == True{} : Bool}; {==} : {ISS(V0) == True{} : Bool}}, {%Equal.sym(MS(), V0, Some{PKS(vs, js, True{})}, e4) : {PKS(vs, js, True{}) == STR(_) : String}; {==} : {PKS(vs, js, True{}) == STR(V0) : String}})

def vfit(+f: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +k: Nat,
  +hk: {Nat.add(k, 1n) == SC.NP(len, t, a, z, 44) : Nat},
  +eL: {List.length(&2, String, VS(len, t, NS.Rg{a, z})) == 1n+k : Nat},
  +hf: {B.Vals.fits(B.Vals.expected_count(num, na, B.Vals.copies(cp, na, 1n+k)), 1n+k) == f : Bool},
  +ev: {VSPL(num, na, cp, i, len, t, NS.Rg{a, z}) == KEEP(num, na, cp, i, VS(len, t, NS.Rg{a, z}), 1n+k) : MS()},
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.vals.fit(f, w, num, B.Vals.copies(cp, na, 1n+k), i, NS.Rg{a, z}, k), m0,
    STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  match f:
    case True{}:
      +vs = VS(len, t, NS.Rg{a, z})
      +q = B.Vals.copies(cp, na, 1n+k)
      +js = B.Vals.idx(num, q, i)
      +V0 = VSPL(num, na, cp, i, len, t, NS.Rg{a, z})
      %Equal.sym(NS.Sw, NS.pix(num, q, i, w, NS.Rg{a, z}, k), NS.picks(js, w, NS.Rg{a, z}, k, True{}), pix_eq(num, q, i, w, NS.Rg{a, z}, k)) :
        S.WS(len, t, _, m0, STR(V0), ISS(V0))
      +ev2 = {%hf :
          {V0 == Bool.pick(MS(), _, B.Vals.join(B.Vals.pick(vs, js)), None{}) : MS()};
        ev : {V0 == B.Vals.join(B.Vals.pick(vs, js)) : MS()}}
      S.ws_imp(len, t, NS.picks(js, w, NS.Rg{a, z}, k, True{}), m0, PKS(vs, js, True{}), ALE(js, k), STR(V0), ISS(V0),
        ha => vals.got(vs, js, k, V0, eL, ha, ev2),
        picks_t(js, True{}, len, t, d, hl, a, z, hpx, k, hk, w, m0, r))
    case False{}:
      +V0 = VSPL(num, na, cp, i, len, t, NS.Rg{a, z})
      S.ws_fail(len, t, STR(V0), ISS(V0), w, m0, r)

def vals.cnt2(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hd: {String.eq(WT.TX(len, t, NS.Rg{a, z}), ".") == False{} : Bool},
  +k: Nat, eq: {NS.count(C.BT(len, t), NS.Rg{a, z}, 44) == (C.BT(len, t), k) : D.Bytes & Nat},
  +ek: {Nat.add(k, 1n) == Nat.add(0n, SC.NP(len, t, a, z, 44)) : Nat}) ->
  S.WS(len, t, NS.vals.c(num, na, cp, i, NS.Rg{a, z}, NS.count(C.BT(len, t), NS.Rg{a, z}, 44), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  +x = {NS.Rg{a, z} : NS.Rg}
  +vs = VS(len, t, x)
  +V0 = VSPL(num, na, cp, i, len, t, x)
  +haz = W.pv_a(len, a, z, hpx)
  +eL = {%Equal.sym(Ss(), String.split(WT.TX(len, t, x), ','), K.CHS(K.SP(len, t, a, z, 44)), split_chs(len, t, a, z, 44, haz)) : {List.length(&2, String, _) == 1n+k : Nat};
    %Equal.sym(Nat, List.length(&2, String, K.CHS(K.SP(len, t, a, z, 44))), List.length(&2, List<&2, U32>, K.SP(len, t, a, z, 44)), len_chs(K.SP(len, t, a, z, 44))) : {_ == 1n+k : Nat};
    %N.add_one(k) : {SC.NP(len, t, a, z, 44) == _ : Nat};
    Equal.sym(Nat, Nat.add(k, 1n), SC.NP(len, t, a, z, 44), ek) : {List.length(&2, String, vs) == 1n+k : Nat}}
  +ev0 = {%Equal.sym(Bool, String.eq(WT.TX(len, t, x), "."), False{}, hd) : {B.Vals.split.if(_, num, na, cp, i, WT.TX(len, t, x)) == KEEP(num, na, cp, i, vs, List.length(&2, String, vs)) : MS()};
    {==} : {V0 == KEEP(num, na, cp, i, vs, List.length(&2, String, vs)) : MS()}}
  +ev = Equal.trans(MS(), V0, KEEP(num, na, cp, i, vs, List.length(&2, String, vs)), KEEP(num, na, cp, i, vs, 1n+k), ev0,
    Equal.cong(Nat, MS(), L => KEEP(num, na, cp, i, vs, L), List.length(&2, String, vs), 1n+k, eL))
  %Equal.sym(D.Bytes & Nat, NS.count(C.BT(len, t), x, 44), (C.BT(len, t), k), eq) :
    S.WS(len, t, NS.vals.c(num, na, cp, i, x, _, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, STR(V0), ISS(V0))
  vfit(B.Vals.fits(B.Vals.expected_count(num, na, B.Vals.copies(cp, na, 1n+k)), 1n+k), len, t, d, hl, a, z, hpx, num, na, cp, i, k, ek, eL, {==}, ev,
    NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp))

def vals.cnt(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hd: {String.eq(WT.TX(len, t, NS.Rg{a, z}), ".") == False{} : Bool},
  cnt: SC.CNT(len, t, 0n, a, z, 44, NS.count(C.BT(len, t), NS.Rg{a, z}, 44))) ->
  S.WS(len, t, NS.vals.c(num, na, cp, i, NS.Rg{a, z}, NS.count(C.BT(len, t), NS.Rg{a, z}, 44), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  (+k, e) = cnt
  (eq, ek) = e
  vals.cnt2(len, t, d, hl, a, z, hpx, num, na, cp, i, l2, t2, p, ok, h, hp, hd, k, eq, ek)

def vals.d(+dot: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool},
  +hd: {String.eq(WT.TX(len, t, NS.Rg{a, z}), ".") == dot : Bool}) ->
  S.WS(len, t, NS.vals.dot(dot, num, na, cp, i, NS.Rg{a, z}, C.BT(len, t), C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok},
    STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  match dot:
    case True{}:
      +x = {NS.Rg{a, z} : NS.Rg}
      +V0 = VSPL(num, na, cp, i, len, t, x)
      +ev = {%Equal.sym(Bool, String.eq(WT.TX(len, t, x), "."), True{}, hd) : {B.Vals.split.if(_, num, na, cp, i, WT.TX(len, t, x)) == Some{"."} : MS()};
        {==} : {V0 == Some{"."} : MS()}}
      S.ws_eq(len, t, NS.ch(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, 46), W.Wm{W.V(l2, t2), p, ok}, NR.chars([46]), STR(V0), True{}, ISS(V0),
        %Equal.sym(MS(), V0, Some{"."}, ev) : {NR.chars([46]) == STR(_) : String}; {==},
        %Equal.sym(MS(), V0, Some{"."}, ev) : {True{} == ISS(_) : Bool}; {==},
        S.ws_ch(len, t, d, hl, 46, {==}, NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, W.Wm{W.V(l2, t2), p, ok}, W.refl(len, l2, t, t2, p, ok, h, hp)))
    case False{}:
      vals.cnt(len, t, d, hl, a, z, hpx, num, na, cp, i, l2, t2, p, ok, h, hp, hd,
        SC.count_t(len, t, d, a, z, 44, hl, W.pv_a(len, a, z, hpx), W.pv_z(len, a, z, hpx), {==}))

def vals.in(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg, +ok: Bool, +h: {W.OK(l2, t2) == True{} : Bool}, +hp: {W.PV(len, p) == True{} : Bool}) ->
  S.WS(len, t, NS.vals(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, num, na, cp, i, NS.Rg{a, z}), W.Wm{W.V(l2, t2), p, ok},
    STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  +x = {NS.Rg{a, z} : NS.Rg}
  +V0 = VSPL(num, na, cp, i, len, t, x)
  %Equal.sym(D.Bytes & Bool, NS.is1(C.BT(len, t), x, 46), (C.BT(len, t), RD.IS1(len, t, x, 46)), RD.is1_t(len, t, x, 46)) :
    S.WS(len, t, NS.vals.k(num, na, cp, i, x, _, C.BT(l2, t2), p, ok), W.Wm{W.V(l2, t2), p, ok}, STR(V0), ISS(V0))
  vals.d(RD.IS1(len, t, x, 46), len, t, d, hl, a, z, hpx, num, na, cp, i, l2, t2, p, ok, h, hp,
    Equal.sym(Bool, RD.IS1(len, t, x, 46), String.eq(WT.TX(len, t, x), "."), RD.is1_v(len, t, d, x, 46, hl, hpx)))

# A per-allele value x in the record for ALT i of na, for copies cp: what
# B.Vals.split gives, when it gives a value.
def vals_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hpx: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +num: B.Num, +na: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  -w: NS.Sw, +m0: W.Wm, r: W.Rel(len, t, w, m0)) ->
  S.WS(len, t, NS.vals(w, num, na, cp, i, NS.Rg{a, z}), m0, STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z}))):
  S.ws_at(len, t, w, v => NS.vals(v, num, na, cp, i, NS.Rg{a, z}), m0, STR(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), ISS(VSPL(num, na, cp, i, len, t, NS.Rg{a, z})), r,
    +l2 => +t2 => +p => +ok => +h => +hp => vals.in(len, t, d, hl, a, z, hpx, num, na, cp, i, l2, t2, p, ok, h, hp))
