import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./norm_split.bend as NS
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_ws.bend as S
import ./proof_s_cut.bend as K
import ./proof_s_read.bend as RD
import ./proof_s_gtspec.bend as G
import ./proof_s_kinds.bend as KD
import ./proof_s_fmt.bend as FM
import ./proof_s_top.bend as TOP
import ./proof_s_rec.bend as RC
import ./proof_s_when.bend as WH
import ./proof_b_alleles_loop.bend as AL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's refusals (norm_split.bend's refuse, after the writer
# gives up): the code it gives is the line's first problem after its ALTs
# (proof_s_when.bend's PROBF), read from INFO's text and, per sample, from
# the writer (a sample it writes has no problem) or from the sample's text.
# Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def Ss() -> Data:
  List<&2, String>

def Rgs() -> Data:
  List<&2, NS.Rg>

def Tags() -> Data:
  List<&2, B.Tag>

def MC() -> Data:
  Maybe<&2, B.Code>

def Ms() -> Data:
  List<&2, Maybe<&2, B.Code>>

# ---------------------------------------------------------------------------
# The copies of LAWS.bend's problems are LAWS.bend's
# ---------------------------------------------------------------------------

law first_eq:
  for +ms: Ms()
  {NS.first(ms) == L.first_code(ms) : MC()}

def first_eq(ms):
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      match m:
        case None{}:
          %Equal.sym(MC(), NS.first(t), L.first_code(t), first_eq(t)) : {_ == L.first_code(t) : MC()}
          {==}
        case Some{+c}:
          {==}

def count_eq(+num: B.Num, +nn: Nat, +cp: Maybe<&2, Nat>, +v: String) -> {NS.count_problem(num, nn, cp, v) == L.count_problem(num, nn, cp, v) : MC()}:
  {==}

def info_of_eq(+m: Maybe<&2, B.Num>, +e: String, +nn: Nat) -> {NS.info_problem.of(m, e, nn) == L.info_problem.of(m, e, nn) : MC()}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case B.NumA{}:
          {==}
        case B.NumR{}:
          {==}
        case B.NumG{}:
          {==}
        case B.NumOther{}:
          {==}
        case B.NumUnknown{}:
          {==}

def info_eq(+m: Maybe<&2, B.Num>, +e: String, +nn: Nat) -> {NS.info_problem(m, e, nn) == L.info_problem(m, e, nn) : MC()}:
  %Equal.sym(MC(), NS.info_problem.of(m, e, nn), L.info_problem.of(m, e, nn), info_of_eq(m, e, nn)) :
    {Bool.pick(MC(), L.has_value(e), _, Bool.pick(MC(), B.Num.per_allele(m), Some{B.BadCount{}}, None{})) == L.info_problem(m, e, nn) : MC()}
  {==}

law infos_eq:
  for +es: Ss()
  for +tags: Tags()
  for +nn: Nat
  {NS.info_problems(es, tags, nn) == L.info_problems(es, tags, nn) : Ms()}

def infos_eq(es, tags, nn):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +m = B.Tags.find(tags, B.Info.key(e))
      %Equal.sym(MC(), NS.info_problem(m, e, nn), L.info_problem(m, e, nn), info_eq(m, e, nn)) : {Con{_, NS.info_problems(t, tags, nn)} == L.info_problems(Con{e, t}, tags, nn) : Ms()}
      %Equal.sym(Ms(), NS.info_problems(t, tags, nn), L.info_problems(t, tags, nn), infos_eq(t, tags, nn)) : {Con{L.info_problem(m, e, nn), _} == L.info_problems(Con{e, t}, tags, nn) : Ms()}
      {==}

law gt_cut_eq:
  for +xs: Ss()
  {NS.gt_cut(xs) == L.gt_cut(xs) : Ss()}

def gt_cut_eq(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Ss(), NS.gt_cut(t), L.gt_cut(t), gt_cut_eq(t)) : {List.append(&2, String, String.split(x, '|'), _) == L.gt_cut(Con{x, t}) : Ss()}
      {==}

law gt_ok_eq:
  for +ts: Ss()
  for +nn: Nat
  {NS.gt_ok.go(ts, nn) == L.gt_ok.go(ts, nn) : Bool}

def gt_ok_eq(ts, nn):
  match ts:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Bool, NS.gt_ok.go(r, nn), L.gt_ok.go(r, nn), gt_ok_eq(r, nn)) :
        {Bool.and(Bool.or(String.eq(x, "."), Bool.and(B.Gt.canon(x), Nat.is_le(Maybe.default(&2, Nat, B.Pos.read(x), 0n), nn))), _) == L.gt_ok.go(Con{x, r}, nn) : Bool}
      {==}

def gt_eq(+nn: Nat, +g: String) -> {NS.gt_problem(nn, g) == L.gt_problem(nn, g) : MC()}:
  +xs = String.split(g, '/')
  %Equal.sym(Ss(), NS.gt_cut(xs), L.gt_cut(xs), gt_cut_eq(xs)) : {Bool.pick(MC(), NS.gt_ok.go(_, nn), None{}, Some{B.BadGt{}}) == L.gt_problem(nn, g) : MC()}
  %Equal.sym(Bool, NS.gt_ok.go(L.gt_cut(xs), nn), L.gt_ok.go(L.gt_cut(xs), nn), gt_ok_eq(L.gt_cut(xs), nn)) : {Bool.pick(MC(), _, None{}, Some{B.BadGt{}}) == L.gt_problem(nn, g) : MC()}
  {==}

def fmt_eq(+m: Maybe<&2, B.Num>, +k: String, +v: String, +nn: Nat, +p: Maybe<&2, Nat>) -> {NS.format_problem(m, k, v, nn, p) == L.format_problem(m, k, v, nn, p) : MC()}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case B.NumA{}:
          {==}
        case B.NumR{}:
          {==}
        case B.NumG{}:
          {==}
        case B.NumOther{}:
          {==}
        case B.NumUnknown{}:
          {==}

law sps_eq:
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: Tags()
  for +nn: Nat
  for +p: Maybe<&2, Nat>
  {NS.sample_problems(ks, vs, fmt, nn, p) == L.sample_problems(ks, vs, fmt, nn, p) : Ms()}

def sps_eq(ks, vs, fmt, nn, p):
  match ks vs:
    case Nil{} Nil{}:
      {==}
    case Con{+k, +kt} Nil{}:
      {==}
    case Nil{} Con{+v, +vt}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      %Equal.sym(MC(), NS.gt_problem(nn, v), L.gt_problem(nn, v), gt_eq(nn, v)) :
        {Con{Bool.pick(MC(), String.eq(k, "GT"), _, NS.format_problem(B.Tags.find(fmt, k), k, v, nn, p)), NS.sample_problems(kt, vt, fmt, nn, p)} == L.sample_problems(Con{k, kt}, Con{v, vt}, fmt, nn, p) : Ms()}
      %Equal.sym(MC(), NS.format_problem(B.Tags.find(fmt, k), k, v, nn, p), L.format_problem(B.Tags.find(fmt, k), k, v, nn, p), fmt_eq(B.Tags.find(fmt, k), k, v, nn, p)) :
        {Con{Bool.pick(MC(), String.eq(k, "GT"), L.gt_problem(nn, v), _), NS.sample_problems(kt, vt, fmt, nn, p)} == L.sample_problems(Con{k, kt}, Con{v, vt}, fmt, nn, p) : Ms()}
      %Equal.sym(Ms(), NS.sample_problems(kt, vt, fmt, nn, p), L.sample_problems(kt, vt, fmt, nn, p), sps_eq(kt, vt, fmt, nn, p)) :
        {Con{Bool.pick(MC(), String.eq(k, "GT"), L.gt_problem(nn, v), L.format_problem(B.Tags.find(fmt, k), k, v, nn, p)), _} == L.sample_problems(Con{k, kt}, Con{v, vt}, fmt, nn, p) : Ms()}
      {==}

# ---------------------------------------------------------------------------
# A sample: the writer's run on it alone, or its text
# ---------------------------------------------------------------------------

# A writer's run: where it ends, and when its flag is set, g.
def OKC(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +g: Bool) -> Type:
  &l2: U32 -> &t2: AT.Tree<U32> -> &p: NS.Rg -> &ok: Bool ->
    ({w == NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok} : NS.Sw} & ({ok == True{} : Bool} -> {g == True{} : Bool}))

def mid(-A: Type, -B0: Type, -C0: Type, x: A & (B0 & C0)) -> B0:
  (a, q) = x
  (b, c) = q
  b

def okc.k(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, +s: String, +g: Bool, +m1: W.Wm,
  q: W.Rel(len, t, w, m1) & ({W.Wm.ok(m1) == True{} : Bool} -> ({W.Wm.ok(m0) == True{} : Bool} & ({g == True{} : Bool} & {WT.T(len, t, m1) == String.append(WT.T(len, t, m0), s) : String})))) ->
  OKC(len, t, w, g):
  match m1:
    case W.Wm{+out, +p, +ok}:
      (r1, imp) = q
      (+l2, q1) = r1
      (+t2, q2) = q1
      (eq, q3) = q2
      (l2, (t2, (p, (ok, (eq, h => mid({W.Wm.ok(m0) == True{} : Bool}, {g == True{} : Bool}, {WT.T(len, t, W.Wm{out, p, ok}) == String.append(WT.T(len, t, m0), s) : String}, imp(h)))))))

def okc(+len: U32, +t: AT.Tree<U32>, -w: NS.Sw, +m0: W.Wm, +s: String, +g: Bool, x: S.WS(len, t, w, m0, s, g)) -> OKC(len, t, w, g):
  (+m1, q) = x
  okc.k(len, t, w, m0, s, g, m1, q)

def gok_gc(+g: B.Got, +h: {G.GOK(g) == True{} : Bool}) -> {WH.GC(g) == None{} : MC()}:
  match g:
    case B.Got{+x}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({WH.GC(B.Refuse{c}) == None{} : MC()}, N.false_ne_true(h))

def TXR(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  WT.TX(len, t, NS.Rg{a, z})

def VS(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> Ss():
  String.split(TXR(len, t, a, z), ':')

# The sample's first problem (sample_problems, its copies from its GT).
def SPL(+len: U32, +t: AT.Tree<U32>, +ks: Ss(), +fmt: Tags(), +nn: Nat, +a: U32, +z: U32) -> Ms():
  L.sample_problems(ks, VS(len, t, a, z), fmt, nn, B.Gt.copies(B.Fmt.gt(ks, VS(len, t, a, z))))

def SPC(+len: U32, +t: AT.Tree<U32>, +ks: Ss(), +fmt: Tags(), +nn: Nat, +a: U32, +z: U32) -> MC():
  L.first_code(SPL(len, t, ks, fmt, nn, a, z))

# The writer's run on the sample alone, in the record for ALT 1.
def W1(+len: U32, +t: AT.Tree<U32>, +ks: Ss(), +fmt: Tags(), +nn: Nat, +a: U32, +z: U32) -> NS.Sw:
  NS.sample(NS.Sw{C.BT(len, t), BY.empty(0n), NS.Rg{a, a}, True{}}, KD.MAPF(fmt, ks), NS.Rg{a, z}, False{}, nn, 1n)

def FS1(+len: U32, +t: AT.Tree<U32>, +ks: Ss(), +fmt: Tags(), +nn: Nat, +a: U32, +z: U32) -> B.Got:
  FM.FS(len, t, fmt, ks, False{}, nn, 1n, a, z)

def sprob.ok(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +ks: Ss(), +fmt: Tags(), +nn: Nat, +hn: {Nat.is_le(1n, nn) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>, +p: NS.Rg,
  gi: {ok == True{} : Bool} -> {G.GOK(FS1(len, t, ks, fmt, nn, a, z)) == True{} : Bool}) ->
  {NS.sprob.w(NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, NS.Rg{a, z}, ks, fmt, nn) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}:
  match ok:
    case True{}:
      +hg = gok_gc(FS1(len, t, ks, fmt, nn, a, z), gi({==}))
      +hc = WH.col_gc(ks, TXR(len, t, a, z), fmt, False{}, nn, 1n, {==}, hn)
      +e = Equal.trans(MC(), SPC(len, t, ks, fmt, nn, a, z), WH.GC(FS1(len, t, ks, fmt, nn, a, z)), None{}, Equal.sym(MC(), WH.GC(FS1(len, t, ks, fmt, nn, a, z)), SPC(len, t, ks, fmt, nn, a, z), hc), hg)
      %Equal.sym(MC(), SPC(len, t, ks, fmt, nn, a, z), None{}, e) : {(C.BT(len, t), None{}) == (C.BT(len, t), _) : D.Bytes & MC()}
      {==}
    case False{}:
      +V = VS(len, t, a, z)
      +CP = B.Gt.copies(B.Fmt.gt(ks, V))
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), NS.Rg{a, z}), (C.BT(len, t), TXR(len, t, a, z)), RD.txt_t(len, t, d, NS.Rg{a, z}, hl, hp)) :
        {NS.sprob.str(_, ks, fmt, nn) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}
      %Equal.sym(Ms(), NS.sample_problems(ks, V, fmt, nn, CP), L.sample_problems(ks, V, fmt, nn, CP), sps_eq(ks, V, fmt, nn, CP)) :
        {(C.BT(len, t), NS.first(_)) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}
      %Equal.sym(MC(), NS.first(L.sample_problems(ks, V, fmt, nn, CP)), L.first_code(L.sample_problems(ks, V, fmt, nn, CP)), first_eq(L.sample_problems(ks, V, fmt, nn, CP))) :
        {(C.BT(len, t), _) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}
      {==}

def sprob.c(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +z: U32, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}, +ks: Ss(), +fmt: Tags(), +nn: Nat, +hn: {Nat.is_le(1n, nn) == True{} : Bool},
  c: OKC(len, t, W1(len, t, ks, fmt, nn, a, z), G.GOK(FS1(len, t, ks, fmt, nn, a, z)))) ->
  {NS.sprob(C.BT(len, t), NS.Rg{a, z}, ks, KD.MAPF(fmt, ks), fmt, nn) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}:
  (+l2, q1) = c
  (+t2, q2) = q1
  (+p, q3) = q2
  (+ok, q4) = q3
  (eq, gi) = q4
  %Equal.sym(NS.Sw, W1(len, t, ks, fmt, nn, a, z), NS.Sw{C.BT(len, t), C.BT(l2, t2), p, ok}, eq) :
    {NS.sprob.w(_, NS.Rg{a, z}, ks, fmt, nn) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}
  sprob.ok(ok, len, t, d, hl, a, z, hp, ks, fmt, nn, hn, l2, t2, p, gi)

# The writer's run on the sample alone: what B.Fmt.split gives.
def sample_ws(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +ks: Ss(), +fmt: Tags(), +nn: Nat, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, +hs: {W.PV(len, NS.Rg{a, a}) == True{} : Bool}) ->
  S.WS(len, t, W1(len, t, ks, fmt, nn, a, z), TOP.W0(a), G.GSTR(FS1(len, t, ks, fmt, nn, a, z)), G.GOK(FS1(len, t, ks, fmt, nn, a, z))):
  FM.sample_t(len, t, d, hl, fmt, ks, False{}, nn, 1n, a, z, haz, hz, bd, hbd, NS.Sw{C.BT(len, t), BY.empty(0n), NS.Rg{a, a}, True{}}, TOP.W0(a), TOP.rel0(len, t, a, hs))
def sample_okc(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +ks: Ss(), +fmt: Tags(), +nn: Nat, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}, +hs: {W.PV(len, NS.Rg{a, a}) == True{} : Bool}) ->
  OKC(len, t, W1(len, t, ks, fmt, nn, a, z), G.GOK(FS1(len, t, ks, fmt, nn, a, z))):
  okc(len, t, W1(len, t, ks, fmt, nn, a, z), TOP.W0(a), G.GSTR(FS1(len, t, ks, fmt, nn, a, z)), G.GOK(FS1(len, t, ks, fmt, nn, a, z)), sample_ws(len, t, d, hl, a, z, haz, hz, ks, fmt, nn, bd, hbd, hs))

# A sample's column a .. z-1 (z within the line): its first problem.
def sprob_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +a: U32, +z: U32, +haz: {U32.is_le(a, z) == True{} : Bool}, +hz: {Nat.is_lt(n(z), n(len)) == True{} : Bool},
  +ks: Ss(), +fmt: Tags(), +nn: Nat, +hn: {Nat.is_le(1n, nn) == True{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}) ->
  {NS.sprob(C.BT(len, t), NS.Rg{a, z}, ks, KD.MAPF(fmt, ks), fmt, nn) == (C.BT(len, t), SPC(len, t, ks, fmt, nn, a, z)) : D.Bytes & MC()}:
  +hza = Equal.trans(Bool, Nat.is_le(n(a), n(z)), U32.is_le(a, z), True{}, Equal.sym(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), U.is_le_to_nat(a, z)), haz)
  +hzl = N.lt_to_le(n(z), n(len), hz)
  sprob.c(len, t, d, hl, a, z, W.pv_mk(len, a, z, hza, hzl), ks, fmt, nn, hn,
    sample_okc(len, t, d, hl, a, z, haz, hz, ks, fmt, nn, bd, hbd, W.pv_mk(len, a, a, N.le_refl(n(a)), N.le_trans(n(a), n(z), n(len), hza, hzl))))

# ---------------------------------------------------------------------------
# The samples, and the line
# ---------------------------------------------------------------------------

def FCS(+len: U32, +t: AT.Tree<U32>, +ks: Ss(), +fmt: Tags(), +nn: Nat, +cols: Rgs()) -> MC():
  L.first_code(L.samples_problems(K.TXS(len, t, cols), ks, fmt, nn))

# The samples cols (within bb, before the end of the line), after the
# problem m found so far: the first problem.
law sprobs_t:
  for +cols: Rgs()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ks: Ss()
  for +fmt: Tags()
  for +nn: Nat
  for +hn: {Nat.is_le(1n, nn) == True{} : Bool}
  for +bb: U32
  for +hpc: {K.ALLPV(bb, cols) == True{} : Bool}
  for +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool}
  for +bd: Nat
  for +hbd: {Nat.pow(2n, 32n) == bd : Nat}
  for +m: MC()
  {NS.sprobs(cols, (C.BT(len, t), m), ks, KD.MAPF(fmt, ks), fmt, nn) == (C.BT(len, t), L.first_code.put(m, FCS(len, t, ks, fmt, nn, cols))) : D.Bytes & MC()}

def sprobs_t(cols, len, t, d, hl, ks, fmt, nn, hn, bb, hpc, hbl, bd, hbd, m):
  match cols:
    case Nil{}:
      %Equal.sym(MC(), L.first_code.put(m, None{}), m, WH.fc_none(m)) : {(C.BT(len, t), m) == (C.BT(len, t), _) : D.Bytes & MC()}
      {==}
    case Con{NS.Rg{+a, +z}, +rr}:
      match m:
        case Some{+c}:
          +hr = N.and_true_r(W.PV(bb, NS.Rg{a, z}), K.ALLPV(bb, rr), hpc)
          sprobs_t(rr, len, t, d, hl, ks, fmt, nn, hn, bb, hr, hbl, bd, hbd, Some{c})
        case None{}:
          +hp = N.and_true_l(W.PV(bb, NS.Rg{a, z}), K.ALLPV(bb, rr), hpc)
          +hr = N.and_true_r(W.PV(bb, NS.Rg{a, z}), K.ALLPV(bb, rr), hpc)
          +P = SPC(len, t, ks, fmt, nn, a, z)
          +SR = L.samples_problems(K.TXS(len, t, rr), ks, fmt, nn)
          %Equal.sym(D.Bytes & MC(), NS.sprob(C.BT(len, t), NS.Rg{a, z}, ks, KD.MAPF(fmt, ks), fmt, nn), (C.BT(len, t), P),
            sprob_t(len, t, d, hl, a, z, AL.le_u(a, z, W.pv_a(bb, a, z, hp)), RC.pv_lt(len, bb, a, z, hp, hbl), ks, fmt, nn, hn, bd, hbd)) :
            {NS.sprobs(rr, _, ks, KD.MAPF(fmt, ks), fmt, nn) == (C.BT(len, t), L.first_code(List.append(&2, Maybe<&2, B.Code>, SPL(len, t, ks, fmt, nn, a, z), SR))) : D.Bytes & MC()}
          %Equal.sym(D.Bytes & MC(), NS.sprobs(rr, (C.BT(len, t), P), ks, KD.MAPF(fmt, ks), fmt, nn), (C.BT(len, t), L.first_code.put(P, FCS(len, t, ks, fmt, nn, rr))),
            sprobs_t(rr, len, t, d, hl, ks, fmt, nn, hn, bb, hr, hbl, bd, hbd, P)) :
            {_ == (C.BT(len, t), L.first_code(List.append(&2, Maybe<&2, B.Code>, SPL(len, t, ks, fmt, nn, a, z), SR))) : D.Bytes & MC()}
          %Equal.sym(MC(), L.first_code(List.append(&2, Maybe<&2, B.Code>, SPL(len, t, ks, fmt, nn, a, z), SR)), L.first_code.put(P, L.first_code(SR)), WH.fc_app(SPL(len, t, ks, fmt, nn, a, z), SR)) :
            {(C.BT(len, t), L.first_code.put(P, FCS(len, t, ks, fmt, nn, rr))) == (C.BT(len, t), _) : D.Bytes & MC()}
          {==}

# What refuse gives for a first problem m.
def RF(+len: U32, +t: AT.Tree<U32>, +m: MC(), +f0: NS.Rg, +f1: NS.Rg) -> NS.Ans:
  NS.refuse.m(m, C.BT(len, t), f0, f1)

def IP(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +nn: Nat, +a7: U32, +z7: U32) -> Ms():
  L.info_problems(String.split(WT.TX(len, t, NS.Rg{a7, z7}), ';'), B.Defs.info(defs), nn)

def FS8(+f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32) -> Rgs():
  RC.FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Nil{})

# A line without FORMAT: its INFO's first problem.
def refuse_t8(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32,
  +h7: {W.PV(len, NS.Rg{a7, z7}) == True{} : Bool}, +fks: List<&2, NS.Fk>, +defs: B.Defs, +nn: Nat) ->
  {NS.refuse(C.BT(len, t), FS8(f0, f1, f2, f3, f4, f5, f6, a7, z7), fks, nn, defs) ==
    RF(len, t, WH.PROBF(K.TXS(len, t, FS8(f0, f1, f2, f3, f4, f5, f6, a7, z7)), defs, nn), f0, f1) : NS.Ans}:
  +I = IP(len, t, defs, nn, a7, z7)
  -RHS = RF(len, t, L.first_code(List.append(&2, Maybe<&2, B.Code>, I, Nil{})), f0, f1)
  %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), NS.Rg{a7, z7}), (C.BT(len, t), WT.TX(len, t, NS.Rg{a7, z7})), RD.txt_t(len, t, d, NS.Rg{a7, z7}, hl, h7)) :
    {NS.refuse.info(_, f0, f1, Nil{}, fks, nn, defs) == RHS : NS.Ans}
  %Equal.sym(Ms(), NS.info_problems(String.split(WT.TX(len, t, NS.Rg{a7, z7}), ';'), B.Defs.info(defs), nn), I, infos_eq(String.split(WT.TX(len, t, NS.Rg{a7, z7}), ';'), B.Defs.info(defs), nn)) :
    {RF(len, t, NS.first(_), f0, f1) == RHS : NS.Ans}
  %Equal.sym(MC(), NS.first(I), L.first_code(I), first_eq(I)) :
    {RF(len, t, _, f0, f1) == RHS : NS.Ans}
  %Equal.sym(MC(), L.first_code(List.append(&2, Maybe<&2, B.Code>, I, Nil{})), L.first_code.put(L.first_code(I), None{}), WH.fc_app(I, Nil{})) :
    {RF(len, t, L.first_code(I), f0, f1) == RF(len, t, _, f0, f1) : NS.Ans}
  %Equal.sym(MC(), L.first_code.put(L.first_code(I), None{}), L.first_code(I), WH.fc_none(L.first_code(I))) :
    {RF(len, t, L.first_code(I), f0, f1) == RF(len, t, _, f0, f1) : NS.Ans}
  {==}
def FS9(+f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32, +f8: NS.Rg, +cols: Rgs()) -> Rgs():
  RC.FSX(f0, f1, f2, f3, f4, f5, f6, a7, z7, Con{f8, cols})

def drop0(+xs: Ss()) -> {List.drop(&2, String, xs, 0n) == xs : Ss()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      {==}

# PROBF of a line with FORMAT (f8) and samples cols, unfolded.
def probf9(+len: U32, +t: AT.Tree<U32>,
  +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32, +f8: NS.Rg, +cols: Rgs(),
  +defs: B.Defs, +nn: Nat) ->
  {WH.PROBF(K.TXS(len, t, FS9(f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols)), defs, nn) ==
   L.first_code(List.append(&2, Maybe<&2, B.Code>, IP(len, t, defs, nn, a7, z7), L.samples_problems(K.TXS(len, t, cols), String.split(WT.TX(len, t, f8), ':'), B.Defs.fmt(defs), nn))) : MC()}:
  %Equal.sym(Ss(), List.drop(&2, String, K.TXS(len, t, cols), 0n), K.TXS(len, t, cols), drop0(K.TXS(len, t, cols))) :
    {L.first_code(List.append(&2, Maybe<&2, B.Code>, IP(len, t, defs, nn, a7, z7), L.samples_problems(_, String.split(WT.TX(len, t, f8), ':'), B.Defs.fmt(defs), nn))) ==
     L.first_code(List.append(&2, Maybe<&2, B.Code>, IP(len, t, defs, nn, a7, z7), L.samples_problems(K.TXS(len, t, cols), String.split(WT.TX(len, t, f8), ':'), B.Defs.fmt(defs), nn))) : MC()}
  {==}

# A line with FORMAT (f8) and samples cols: its first problem after its ALTs
# (the writer's FORMAT kinds are those of FORMAT's keys).
def refuse_t9(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +a7: U32, +z7: U32, +f8: NS.Rg, +cols: Rgs(),
  +h7: {W.PV(len, NS.Rg{a7, z7}) == True{} : Bool}, +h8: {W.PV(len, f8) == True{} : Bool},
  +bb: U32, +hpc: {K.ALLPV(bb, cols) == True{} : Bool}, +hbl: {Nat.is_lt(n(bb), n(len)) == True{} : Bool},
  +defs: B.Defs, +nn: Nat, +hn: {Nat.is_le(1n, nn) == True{} : Bool}, +bd: Nat, +hbd: {Nat.pow(2n, 32n) == bd : Nat}) ->
  {NS.refuse(C.BT(len, t), FS9(f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols), KD.MAPF(B.Defs.fmt(defs), String.split(WT.TX(len, t, f8), ':')), nn, defs) ==
    RF(len, t, WH.PROBF(K.TXS(len, t, FS9(f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols)), defs, nn), f0, f1) : NS.Ans}:
  +KS = String.split(WT.TX(len, t, f8), ':')
  +FK = KD.MAPF(B.Defs.fmt(defs), KS)
  +I = IP(len, t, defs, nn, a7, z7)
  +SP = L.samples_problems(K.TXS(len, t, cols), KS, B.Defs.fmt(defs), nn)
  -RHS = RF(len, t, L.first_code(List.append(&2, Maybe<&2, B.Code>, I, SP)), f0, f1)
  %Equal.sym(MC(), WH.PROBF(K.TXS(len, t, FS9(f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols)), defs, nn), L.first_code(List.append(&2, Maybe<&2, B.Code>, I, SP)),
    probf9(len, t, f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols, defs, nn)) :
    {NS.refuse(C.BT(len, t), FS9(f0, f1, f2, f3, f4, f5, f6, a7, z7, f8, cols), FK, nn, defs) == RF(len, t, _, f0, f1) : NS.Ans}
  %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), NS.Rg{a7, z7}), (C.BT(len, t), WT.TX(len, t, NS.Rg{a7, z7})), RD.txt_t(len, t, d, NS.Rg{a7, z7}, hl, h7)) :
    {NS.refuse.info(_, f0, f1, Con{f8, cols}, FK, nn, defs) == RHS : NS.Ans}
  %Equal.sym(Ms(), NS.info_problems(String.split(WT.TX(len, t, NS.Rg{a7, z7}), ';'), B.Defs.info(defs), nn), I, infos_eq(String.split(WT.TX(len, t, NS.Rg{a7, z7}), ';'), B.Defs.info(defs), nn)) :
    {NS.refuse.out(NS.refuse.ks(NS.txt(C.BT(len, t), f8), NS.first(_), cols, FK, B.Defs.fmt(defs), nn), f0, f1) == RHS : NS.Ans}
  %Equal.sym(MC(), NS.first(I), L.first_code(I), first_eq(I)) :
    {NS.refuse.out(NS.refuse.ks(NS.txt(C.BT(len, t), f8), _, cols, FK, B.Defs.fmt(defs), nn), f0, f1) == RHS : NS.Ans}
  %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), f8), (C.BT(len, t), WT.TX(len, t, f8)), RD.txt_t(len, t, d, f8, hl, h8)) :
    {NS.refuse.out(NS.refuse.ks(_, L.first_code(I), cols, FK, B.Defs.fmt(defs), nn), f0, f1) == RHS : NS.Ans}
  %Equal.sym(D.Bytes & MC(), NS.sprobs(cols, (C.BT(len, t), L.first_code(I)), KS, FK, B.Defs.fmt(defs), nn), (C.BT(len, t), L.first_code.put(L.first_code(I), FCS(len, t, KS, B.Defs.fmt(defs), nn, cols))),
    sprobs_t(cols, len, t, d, hl, KS, B.Defs.fmt(defs), nn, hn, bb, hpc, hbl, bd, hbd, L.first_code(I))) :
    {NS.refuse.out(_, f0, f1) == RHS : NS.Ans}
  %Equal.sym(MC(), L.first_code(List.append(&2, Maybe<&2, B.Code>, I, SP)), L.first_code.put(L.first_code(I), L.first_code(SP)), WH.fc_app(I, SP)) :
    {RF(len, t, L.first_code.put(L.first_code(I), FCS(len, t, KS, B.Defs.fmt(defs), nn, cols)), f0, f1) == RF(len, t, _, f0, f1) : NS.Ans}
  {==}

