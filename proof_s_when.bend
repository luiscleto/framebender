import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_site.bend as SI
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_tri.bend as TR
import ./proof_s_ient.bend as IE
import ./proof_s_gtl.bend as GL
import ./proof_run_base.bend as RB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_when: with -m, a line that is not MALFORMED and has two or more
# ALTs is split exactly when split_problem finds nothing wrong, and refused
# with the code split_problem gives otherwise. The refusal of a result list
# is its first refusal (FR); every refusal of a record does not depend on
# which ALT it is for, so the first record's is the line's first problem.
# Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def Ms() -> Data:
  List<&2, Maybe<&2, B.Code>>

# A result's refusal.
def GC(g: B.Got) -> Maybe<&2, B.Code>:
  match g:
    case B.Got{x}:
      None{}
    case B.Refuse{c}:
      Some{c}

def FR(gs: Gs()) -> Maybe<&2, B.Code>:
  match gs:
    case Nil{}:
      None{}
    case g <> t:
      L.first_code.put(GC(g), FR(t))

# Results joined: the first refusal.
law cat_gc:
  for +a: B.Got
  for +sep: String
  for +b: B.Got
  {GC(B.Got.cat(a, sep, b)) == L.first_code.put(GC(a), GC(b)) : Maybe<&2, B.Code>}

def cat_gc(a, sep, b):
  match a b:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+x} B.Refuse{+c}:
      {==}
    case B.Got{+x} B.Got{+y}:
      {==}

def fc_none(+m: Maybe<&2, B.Code>) -> {L.first_code.put(m, None{}) == m : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      {==}

def jg.k(+g: B.Got, +t: Gs(), +sep: String, +ih: {GC(B.Got.join(t, sep)) == FR(t) : Maybe<&2, B.Code>}) ->
  {GC(B.Got.join(Con{g, t}, sep)) == FR(Con{g, t}) : Maybe<&2, B.Code>}:
  match t:
    case Nil{}:
      Equal.sym(Maybe<&2, B.Code>, L.first_code.put(GC(g), None{}), GC(g), fc_none(GC(g)))
    case Con{+g2, +t2}:
      Equal.trans(Maybe<&2, B.Code>, GC(B.Got.cat(g, sep, B.Got.join(Con{g2, t2}, sep))), L.first_code.put(GC(g), GC(B.Got.join(Con{g2, t2}, sep))), FR(Con{g, Con{g2, t2}}),
        cat_gc(g, sep, B.Got.join(Con{g2, t2}, sep)),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(GC(g), z), GC(B.Got.join(Con{g2, t2}, sep)), FR(Con{g2, t2}), ih))

law join_gc:
  for +gs: Gs()
  for +sep: String
  {GC(B.Got.join(gs, sep)) == FR(gs) : Maybe<&2, B.Code>}

def join_gc(gs, sep):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      jg.k(g, t, sep, join_gc(t, sep))


# Parts.of: Pieces when nothing is refused, else Unsplit with the first
# refusal.
law po:
  for +gs: Gs()
  {L.refusal(B.Parts.of(gs)) == Some{FR(gs)} : Maybe<&2, Maybe<&2, B.Code>>}

def po.k(+g: B.Got, +r: B.Parts, +m: Maybe<&2, B.Code>, +h: {L.refusal(r) == Some{m} : Maybe<&2, Maybe<&2, B.Code>>}) ->
  {L.refusal(B.Parts.cons(g, r)) == Some{L.first_code.put(GC(g), m)} : Maybe<&2, Maybe<&2, B.Code>>}:
  match g r:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+x} B.Pieces{+ps}:
      {%Equal.cong(Maybe<&2, Maybe<&2, B.Code>>, Maybe<&2, B.Code>, z => Maybe.default(&2, Maybe<&2, B.Code>, z, None{}), Some{None{}}, Some{m}, h) : {L.refusal(B.Pieces{Con{x, ps}}) == Some{_} : Maybe<&2, Maybe<&2, B.Code>>};
       {==} : {L.refusal(B.Parts.cons(B.Got{x}, B.Pieces{ps})) == Some{L.first_code.put(GC(B.Got{x}), m)} : Maybe<&2, Maybe<&2, B.Code>>}}
    case B.Got{+x} B.Unsplit{+c}:
      h
    case B.Got{+x} B.Whole{}:
      Empty.absurd({L.refusal(B.Parts.cons(B.Got{x}, B.Whole{})) == Some{L.first_code.put(GC(B.Got{x}), m)} : Maybe<&2, Maybe<&2, B.Code>>},
        AB.false_ne_true(Equal.cong(Maybe<&2, Maybe<&2, B.Code>>, Bool, z => Maybe.is_some(&2, Maybe<&2, B.Code>, z), None{}, Some{m}, h)))

def po(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      po.k(g, B.Parts.of(t), FR(t), po(t))

def fa.k(+m: Maybe<&2, B.Code>, +a: Maybe<&2, B.Code>, +b: Maybe<&2, B.Code>, +x: Maybe<&2, B.Code>, +h: {x == L.first_code.put(a, b) : Maybe<&2, B.Code>}) ->
  {L.first_code.put(m, x) == L.first_code.put(L.first_code.put(m, a), b) : Maybe<&2, B.Code>}:
  match m:
    case Some{+c}:
      {==}
    case None{}:
      h

law fc_app:
  for +xs: Ms()
  for +ys: Ms()
  {L.first_code(List.append(&2, Maybe<&2, B.Code>, xs, ys)) == L.first_code.put(L.first_code(xs), L.first_code(ys)) : Maybe<&2, B.Code>}

def fc_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      fa.k(m, L.first_code(t), L.first_code(ys), L.first_code(List.append(&2, Maybe<&2, B.Code>, t, ys)), fc_app(t, ys))


# ---------------------------------------------------------------------------
# A per-allele value: refused exactly when count_problem says
# ---------------------------------------------------------------------------

def ALT(ks: List<&2, Nat>, +c: Nat) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, t}:
      Nat.is_lt(k, c) && ALT(t, c)

law get_lt:
  for +vs: Ss()
  for +k: Nat
  for +h: {Nat.is_lt(k, List.length(&2, String, vs)) == True{} : Bool}
  {Maybe.is_some(&2, String, List.get(&2, String, vs, k)) == True{} : Bool}

def get_lt(vs, k, h):
  match vs k:
    case Nil{} _:
      Empty.absurd({Maybe.is_some(&2, String, List.get(&2, String, Nil{}, k)) == True{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, N.lt_zero(k)), h)))
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+(+p):
      get_lt(t, p, h)

def pcs(m: Maybe<&2, String>, r: Maybe<&2, Ss()>, +hm: {Maybe.is_some(&2, String, m) == True{} : Bool}, +hr: {Maybe.is_some(&2, Ss(), r) == True{} : Bool}) ->
  {Maybe.is_some(&2, Ss(), B.Vals.pick.cons(m, r)) == True{} : Bool}:
  match m r:
    case Some{+x} Some{+xs}:
      {==}
    case Some{+x} None{}:
      Empty.absurd({Maybe.is_some(&2, Ss(), B.Vals.pick.cons(Some{x}, None{})) == True{} : Bool}, N.false_ne_true(hr))
    case None{} _:
      Empty.absurd({Maybe.is_some(&2, Ss(), B.Vals.pick.cons(None{}, r)) == True{} : Bool}, N.false_ne_true(hm))

# Places within the values: the pick succeeds.
law pk_some:
  for +vs: Ss()
  for +ks: List<&2, Nat>
  for +h: {ALT(ks, List.length(&2, String, vs)) == True{} : Bool}
  {Maybe.is_some(&2, Ss(), B.Vals.pick(vs, ks)) == True{} : Bool}

def pk_some(vs, ks, h):
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      +L0 = List.length(&2, String, vs)
      pcs(List.get(&2, String, vs, k), B.Vals.pick(vs, t),
        get_lt(vs, k, AB.and_true_l(Nat.is_lt(k, L0), ALT(t, L0), h)),
        pk_some(vs, t, AB.and_true_r(Nat.is_lt(k, L0), ALT(t, L0), h)))

def FITS(+num: B.Num, +n: Nat, +q: Nat, +c: Nat) -> Bool:
  B.Vals.fits(B.Vals.expected_count(num, n, q), c)

def ceq(+x: Nat, +c: Nat, +h: {Nat.is_eq(x, c) == True{} : Bool}) -> {x == c : Nat}:
  N.eq_sound(x, c, h)

# ALT i (1 to n) and REF: places below 1 + n.
def r_ok(+i: Nat, +n: Nat, +hin: {Nat.is_le(i, n) == True{} : Bool}) -> {ALT([0n, i], 1n+n) == True{} : Bool}:
  SM.and_tt(Nat.is_lt(0n, 1n+n), ALT([i], 1n+n), {==},
    SM.and_tt(Nat.is_lt(i, 1n+n), True{}, Equal.trans(Bool, Nat.is_lt(i, 1n+n), Nat.is_le(i, n), True{}, N.lt_succ_iff(i, n), hin), {==}))

def g2_ok(+i: Nat, +n: Nat, +hin: {Nat.is_le(i, n) == True{} : Bool}) -> {ALT([0n, B.Gt.index(0n, i), B.Gt.index(i, i)], B.Gt.count(n)) == True{} : Bool}:
  SM.and_tt(Nat.is_lt(0n, B.Gt.count(n)), ALT([B.Gt.index(0n, i), B.Gt.index(i, i)], B.Gt.count(n)), TR.idx_00(n),
    SM.and_tt(Nat.is_lt(B.Gt.index(0n, i), B.Gt.count(n)), ALT([B.Gt.index(i, i)], B.Gt.count(n)), TR.idx_0i(i, n, hin),
      SM.and_tt(Nat.is_lt(B.Gt.index(i, i), B.Gt.count(n)), True{}, TR.idx_ii(i, n, hin), {==})))

def g.k(+b1: Bool, +b2: Bool, +n: Nat, +q: Nat, +c: Nat, +i: Nat,
  +hin: {Nat.is_le(i, n) == True{} : Bool},
  +hf: {B.Vals.fits(Bool.pick(Maybe<&2, Nat>, b1, Some{1n+n}, Bool.pick(Maybe<&2, Nat>, b2, Some{B.Gt.count(n)}, None{})), c) == True{} : Bool}) ->
  {ALT(Bool.pick(List<&2, Nat>, b1, [0n, i], [0n, B.Gt.index(0n, i), B.Gt.index(i, i)]), c) == True{} : Bool}:
  match b1 b2:
    case True{} _:
      {%ceq(1n+n, c, hf) : {ALT([0n, i], _) == True{} : Bool}; r_ok(i, n, hin) : {ALT([0n, i], c) == True{} : Bool}}
    case False{} True{}:
      {%ceq(B.Gt.count(n), c, hf) : {ALT([0n, B.Gt.index(0n, i), B.Gt.index(i, i)], _) == True{} : Bool}; g2_ok(i, n, hin) : {ALT([0n, B.Gt.index(0n, i), B.Gt.index(i, i)], c) == True{} : Bool}}
    case False{} False{}:
      Empty.absurd({ALT([0n, B.Gt.index(0n, i), B.Gt.index(i, i)], c) == True{} : Bool}, N.false_ne_true(hf))

# A count that fits: the record keeps values within them (1 <= i <= n).
def idx_ok(+num: B.Num, +n: Nat, +q: Nat, +c: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool},
  +hpa: {L.per_allele_num(num) == True{} : Bool},
  +hf: {FITS(num, n, q, c) == True{} : Bool}) -> {ALT(B.Vals.idx(num, q, i), c) == True{} : Bool}:
  match num i:
    case B.NumA{} 0n:
      Empty.absurd({ALT(B.Vals.idx(B.NumA{}, q, 0n), c) == True{} : Bool}, N.false_ne_true(hi))
    case B.NumA{} 1n+(+j):
      {%ceq(n, c, hf) : {ALT([Nat.sub(1n+j, 1n)], _) == True{} : Bool};
       %Equal.sym(Nat, Nat.sub(j, 0n), j, N.sub_zero(j)) : {Bool.and(Nat.is_lt(_, n), True{}) == True{} : Bool};
       SM.and_tt(Nat.is_lt(j, n), True{}, Equal.trans(Bool, Nat.is_lt(j, n), Nat.is_le(1n+j, n), True{}, Equal.sym(Bool, Nat.is_le(1n+j, n), Nat.is_lt(j, n), N.le_succ_lt(j, n)), hin), {==}) :
       {ALT(B.Vals.idx(B.NumA{}, q, 1n+j), c) == True{} : Bool}}
    case B.NumR{} _:
      {%ceq(1n+n, c, hf) : {ALT([0n, i], _) == True{} : Bool}; r_ok(i, n, hin) : {ALT(B.Vals.idx(B.NumR{}, q, i), c) == True{} : Bool}}
    case B.NumG{} _:
      g.k(Nat.is_eq(q, 1n), Nat.is_eq(q, 2n), n, q, c, i, hin, hf)
    case B.NumOther{} _:
      Empty.absurd({ALT(B.Vals.idx(B.NumOther{}, q, i), c) == True{} : Bool}, N.false_ne_true(hpa))
    case B.NumUnknown{} _:
      Empty.absurd({ALT(B.Vals.idx(B.NumUnknown{}, q, i), c) == True{} : Bool}, N.false_ne_true(hpa))

def jsome(m: Maybe<&2, Ss()>, +h: {Maybe.is_some(&2, Ss(), m) == True{} : Bool}) -> {GC(B.Got.of(B.Vals.join(m), B.BadCount{})) == None{} : Maybe<&2, B.Code>}:
  match m:
    case Some{+ys}:
      {==}
    case None{}:
      Empty.absurd({GC(B.Got.of(B.Vals.join(None{}), B.BadCount{})) == None{} : Maybe<&2, B.Code>}, N.false_ne_true(h))

def vs.f(+f: Bool, +num: B.Num, +n: Nat, +q: Nat, +i: Nat, +vs: Ss(),
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool},
  +hpa: {L.per_allele_num(num) == True{} : Bool},
  +ef: {FITS(num, n, q, List.length(&2, String, vs)) == f : Bool}) ->
  {GC(B.Got.of(Bool.pick(Maybe<&2, String>, f, B.Vals.join(B.Vals.pick(vs, B.Vals.idx(num, q, i))), None{}), B.BadCount{})) == Bool.pick(Maybe<&2, B.Code>, f, None{}, Some{B.BadCount{}}) : Maybe<&2, B.Code>}:
  match f:
    case False{}:
      {==}
    case True{}:
      jsome(B.Vals.pick(vs, B.Vals.idx(num, q, i)), pk_some(vs, B.Vals.idx(num, q, i), idx_ok(num, n, q, List.length(&2, String, vs), i, hi, hin, hpa, ef)))

def vs.d(+d: Bool, +num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +v: String,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool},
  +hpa: {L.per_allele_num(num) == True{} : Bool}) ->
  {GC(B.Got.of(B.Vals.split.if(d, num, n, cp, i, v), B.BadCount{})) == Bool.pick(Maybe<&2, B.Code>, d || FITS(num, n, B.Vals.copies(cp, n, List.length(&2, String, L.values(v))), List.length(&2, String, L.values(v))), None{}, Some{B.BadCount{}}) : Maybe<&2, B.Code>}:
  match d:
    case True{}:
      {==}
    case False{}:
      +vs = String.split(v, ',')
      +q = B.Vals.copies(cp, n, List.length(&2, String, vs))
      vs.f(FITS(num, n, q, List.length(&2, String, vs)), num, n, q, i, vs, hi, hin, hpa, {==})

# A per-allele value in the record for ALT i (1 to n): refused exactly when
# count_problem says (BAD_COUNT).
law vs_gc:
  for +num: B.Num
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +v: String
  for +hi: {Nat.is_le(1n, i) == True{} : Bool}
  for +hin: {Nat.is_le(i, n) == True{} : Bool}
  for +hpa: {L.per_allele_num(num) == True{} : Bool}
  {GC(B.Got.of(B.Vals.split(num, n, cp, i, v), B.BadCount{})) == L.count_problem(num, n, cp, v) : Maybe<&2, B.Code>}

def vs_gc(num, n, cp, i, v, hi, hin, hpa):
  vs.d(String.eq(v, "."), num, n, cp, i, v, hi, hin, hpa)

# ---------------------------------------------------------------------------
# An INFO entry, a FORMAT value (not GT): refused as their problems say
# ---------------------------------------------------------------------------

def ieq_gc(+m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(B.Info.split.eq(m, B.Info.key(e), e, n, i)) == L.info_problem.of(m, e, n) : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      match num:
        case B.NumUnknown{}:
          {==}
        case B.NumOther{}:
          {==}
        case B.NumA{}:
          Equal.trans(Maybe<&2, B.Code>, GC(B.Got.cat(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumA{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{}))), GC(B.Got.of(B.Vals.split(B.NumA{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), L.count_problem(B.NumA{}, n, Some{2n}, L.value_text(e)),
            cat_gc(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumA{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), vs_gc(B.NumA{}, n, Some{2n}, i, L.value_text(e), hi, hin, {==}))
        case B.NumR{}:
          Equal.trans(Maybe<&2, B.Code>, GC(B.Got.cat(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumR{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{}))), GC(B.Got.of(B.Vals.split(B.NumR{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), L.count_problem(B.NumR{}, n, Some{2n}, L.value_text(e)),
            cat_gc(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumR{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), vs_gc(B.NumR{}, n, Some{2n}, i, L.value_text(e), hi, hin, {==}))
        case B.NumG{}:
          Equal.trans(Maybe<&2, B.Code>, GC(B.Got.cat(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumG{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{}))), GC(B.Got.of(B.Vals.split(B.NumG{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), L.count_problem(B.NumG{}, n, Some{2n}, L.value_text(e)),
            cat_gc(B.Got{B.Info.key(e)}, "=", B.Got.of(B.Vals.split(B.NumG{}, n, Some{2n}, i, L.value_text(e)), B.BadCount{})), vs_gc(B.NumG{}, n, Some{2n}, i, L.value_text(e), hi, hin, {==}))

def in.c(+c: Bool, +hv: Bool, +pa: Bool, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat,
  +ec: {String.eq(B.Info.key(e), e) == c : Bool},
  +ehv: {L.has_value(e) == hv : Bool},
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(Bool.pick(B.Got, c, Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, B.Info.key(e), e, n, i)))
    == Bool.pick(Maybe<&2, B.Code>, hv, L.info_problem.of(m, e, n), Bool.pick(Maybe<&2, B.Code>, pa, Some{B.BadCount{}}, None{})) : Maybe<&2, B.Code>}:
  match c hv:
    case True{} True{}:
      Empty.absurd({GC(Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{e})) == L.info_problem.of(m, e, n) : Maybe<&2, B.Code>},
        N.false_ne_true(Equal.trans(Bool, False{}, String.eq(B.Info.key(e), e), True{}, Equal.sym(Bool, String.eq(B.Info.key(e), e), False{}, IE.hv_ne(e, ehv)), ec)))
    case True{} False{}:
      match pa:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{} True{}:
      ieq_gc(m, e, n, i, hi, hin)
    case False{} False{}:
      Empty.absurd({GC(B.Info.split.eq(m, B.Info.key(e), e, n, i)) == Bool.pick(Maybe<&2, B.Code>, pa, Some{B.BadCount{}}, None{}) : Maybe<&2, B.Code>},
        N.false_ne_true(Equal.trans(Bool, False{}, L.has_value(e), True{}, Equal.sym(Bool, L.has_value(e), False{}, ehv), IE.ne_hv(e, ec))))

# An INFO entry in the record for ALT i (1 to n): refused as info_problem says.
law in_gc:
  for +m: Maybe<&2, B.Num>
  for +e: String
  for +n: Nat
  for +i: Nat
  for +hi: {Nat.is_le(1n, i) == True{} : Bool}
  for +hin: {Nat.is_le(i, n) == True{} : Bool}
  {GC(B.Info.split.num(m, e, n, i)) == L.info_problem(m, e, n) : Maybe<&2, B.Code>}

def in_gc(m, e, n, i, hi, hin):
  in.c(String.eq(B.Info.key(e), e), L.has_value(e), B.Num.per_allele(m), m, e, n, i, {==}, {==}, hi, hin)

# A FORMAT value (not GT): refused as format_problem says.
def fn_gc(+m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(B.Fmt.split.num(m, k, v, n, cp, i)) == L.format_problem(m, k, v, n, cp) : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      match num:
        case B.NumUnknown{}:
          {==}
        case B.NumOther{}:
          {==}
        case B.NumA{}:
          vs_gc(B.NumA{}, n, cp, i, v, hi, hin, {==})
        case B.NumR{}:
          vs_gc(B.NumR{}, n, cp, i, v, hi, hin, {==})
        case B.NumG{}:
          vs_gc(B.NumG{}, n, cp, i, v, hi, hin, {==})

# ---------------------------------------------------------------------------
# A genotype: BAD_GT exactly when gt_problem says
# ---------------------------------------------------------------------------

def dig_some(+h: Char, +hd: {Char.is_digit(h) == True{} : Bool}) -> {Maybe.is_some(&2, Nat, B.Pos.digit(h)) == True{} : Bool}:
  match h:
    case Chr{+x}:
      {%Equal.sym(Bool, Char.is_digit(Chr{x}), True{}, hd) : {Maybe.is_some(&2, Nat, B.Pos.digit.if(x, _)) == True{} : Bool}; {==} : {Maybe.is_some(&2, Nat, B.Pos.digit(Chr{x})) == True{} : Bool}}

def push_some(+x: Nat, d: Maybe<&2, Nat>, +hd: {Maybe.is_some(&2, Nat, d) == True{} : Bool}) -> {B.Pos.read.push(Some{x}, d) == Some{Maybe.default(&2, Nat, B.Pos.read.push(Some{x}, d), 0n)} : Maybe<&2, Nat>}:
  match d:
    case Some{+k}:
      {==}
    case None{}:
      Empty.absurd({B.Pos.read.push(Some{x}, None{}) == Some{0n} : Maybe<&2, Nat>}, N.false_ne_true(hd))

law rg_some:
  for +s: String
  for +x: Nat
  for +hd: {B.Text.all_digits(s) == True{} : Bool}
  {Maybe.is_some(&2, Nat, B.Pos.read.go(s, Some{x})) == True{} : Bool}

def rg_some(s, x, hd):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      +P = B.Pos.read.push(Some{x}, B.Pos.digit(h))
      +y = Maybe.default(&2, Nat, P, 0n)
      {%Equal.sym(Maybe<&2, Nat>, P, Some{y}, push_some(x, B.Pos.digit(h), dig_some(h, AB.and_true_l(Char.is_digit(h), B.Text.all_digits(t), hd)))) : {Maybe.is_some(&2, Nat, B.Pos.read.go(t, _)) == True{} : Bool};
       rg_some(t, y, AB.and_true_r(Char.is_digit(h), B.Text.all_digits(t), hd)) : {Maybe.is_some(&2, Nat, B.Pos.read.go(SCon{h, t}, Some{x})) == True{} : Bool}}

def canon_some.k(s: String, +hd: {B.Text.all_digits(s) == True{} : Bool}, +he: {String.is_empty(s) == False{} : Bool}) -> {Maybe.is_some(&2, Nat, B.Pos.read(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Maybe.is_some(&2, Nat, B.Pos.read(SNil{})) == True{} : Bool}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, he)))
    case SCon{+h, +t}:
      rg_some(SCon{h, t}, 0n, hd)

# A canonical allele number reads as a number.
def canon_some(+s: String, +hc: {B.Gt.canon(s) == True{} : Bool}) -> {Maybe.is_some(&2, Nat, B.Pos.read(s)) == True{} : Bool}:
  +E = Bool.not(String.is_empty(s))
  +D = B.Text.all_digits(s)
  +Z = String.eq(s, "0") || Bool.not(String.starts_with(s, "0"))
  +h12 = AB.and_true_l(Bool.and(E, D), Z, hc)
  canon_some.k(s, AB.and_true_r(E, D, h12), SM.not_true(String.is_empty(s), AB.and_true_l(E, D, h12)))

def PB(+b: Bool) -> Maybe<&2, B.Code>:
  Bool.pick(Maybe<&2, B.Code>, b, None{}, Some{B.BadGt{}})

def TOKOK(+t: String, +n: Nat) -> Bool:
  String.eq(t, ".") || (B.Gt.canon(t) && Nat.is_le(Maybe.default(&2, Nat, B.Pos.read(t), 0n), n))

def tokg.b(+o0: Bool, +n: Nat, +i: Nat, +a: Nat, +b: Bool) ->
  {GC(Bool.pick(B.Got, b, B.Got{B.Gt.show(B.Gt.rule(o0, i, Some{a}))}, B.Refuse{B.BadGt{}})) == PB(b) : Maybe<&2, B.Code>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tokg.k(+o0: Bool, +n: Nat, +i: Nat, +c1: Bool, +c2: Bool, +m: Maybe<&2, Nat>,
  +hm: {Bool.or(Bool.not(c2), Maybe.is_some(&2, Nat, m)) == True{} : Bool}) ->
  {GC(GL.ALK(o0, n, i, c1, c2, m)) == PB(c1 || (c2 && Nat.is_le(Maybe.default(&2, Nat, m, 0n), n))) : Maybe<&2, B.Code>}:
  match c1 c2:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      match m:
        case None{}:
          Empty.absurd({GC(GL.ALK(o0, n, i, False{}, True{}, None{})) == PB(Nat.is_le(0n, n)) : Maybe<&2, B.Code>}, N.false_ne_true(hm))
        case Some{+a}:
          tokg.b(o0, n, i, a, Nat.is_le(a, n))

def cs_hm(+c: Bool, +t: String, +ec: {B.Gt.canon(t) == c : Bool}) -> {Bool.or(Bool.not(c), Maybe.is_some(&2, Nat, B.Pos.read(t))) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      canon_some(t, ec)

# One allele of a genotype: BAD_GT exactly when it is not '.' nor a number
# from 0 to n written canonically.
def tokg(+o0: Bool, +n: Nat, +i: Nat, +t: String) -> {GC(GL.AL(o0, n, i, t)) == PB(TOKOK(t, n)) : Maybe<&2, B.Code>}:
  tokg.k(o0, n, i, String.eq(t, "."), B.Gt.canon(t), B.Pos.read(t), cs_hm(B.Gt.canon(t), t, {==}))

def pand(+a: Bool, +b: Bool) -> {PB(a && b) == L.first_code.put(PB(a), PB(b)) : Maybe<&2, B.Code>}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def GRT(+n: Nat, +tks: Ss(), +tk: String, +rs: B.Got) -> Type:
  {tks == Con{tk, GL.tl(tks)} : Ss()} & {GC(rs) == PB(L.gt_ok.go(GL.tl(tks), n)) : Maybe<&2, B.Code>}

def GR(+o0: Bool, +n: Nat, +i: Nat, +g: String, r: B.Gp) -> Type:
  match r:
    case B.Gp{+tk, +rs}:
      GRT(n, GL.TKS(g), tk, rs)

def gr.t(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got, q: GRT(n, GL.TKS(t), tk, rs)) ->
  GRT(n, Con{"", GL.TKS(t)}, "", GL.RSP(o0, n, i, c, tk, rs)):
  match q:
    case (e1, e2):
      +R = GL.tl(GL.TKS(t))
      +A = GL.AL(o0, n, i, tk)
      +X = B.Got.cat(B.Got{SCon{c, SNil{}}}, "", A)
      ({==},
       Equal.trans(Maybe<&2, B.Code>, GC(GL.RSP(o0, n, i, c, tk, rs)), L.first_code.put(GC(X), GC(rs)), PB(L.gt_ok.go(GL.TKS(t), n)),
         cat_gc(X, "", rs),
         Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(X), GC(rs)), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), PB(L.gt_ok.go(GL.TKS(t), n)),
           Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(X), GC(rs)), L.first_code.put(GC(X), PB(L.gt_ok.go(R, n))), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))),
             Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(GC(X), z), GC(rs), PB(L.gt_ok.go(R, n)), e2),
             Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, PB(L.gt_ok.go(R, n))), GC(X), PB(TOKOK(tk, n)),
               Equal.trans(Maybe<&2, B.Code>, GC(X), GC(A), PB(TOKOK(tk, n)), cat_gc(B.Got{SCon{c, SNil{}}}, "", A), tokg(o0, n, i, tk)))),
           Equal.trans(Maybe<&2, B.Code>, L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), PB(L.gt_ok.go(Con{tk, R}, n)), PB(L.gt_ok.go(GL.TKS(t), n)),
             Equal.sym(Maybe<&2, B.Code>, PB(L.gt_ok.go(Con{tk, R}, n)), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), pand(TOKOK(tk, n), L.gt_ok.go(R, n))),
             Equal.cong(Ss(), Maybe<&2, B.Code>, z => PB(L.gt_ok.go(z, n)), Con{tk, R}, GL.TKS(t), Equal.sym(Ss(), GL.TKS(t), Con{tk, R}, e1))))))

def gr.f(+n: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got, q: GRT(n, GL.TKS(t), tk, rs)) ->
  GRT(n, String.split.push(c, GL.TKS(t)), SCon{c, tk}, rs):
  match q:
    case (e1, e2):
      +T0 = GL.TKS(t)
      +TT = GL.tl(GL.TKS(t))
      +sy = Equal.sym(Ss(), T0, Con{tk, TT}, e1)
      ({%sy : {String.split.push(c, _) == Con{SCon{c, tk}, GL.tl(String.split.push(c, _))} : Ss()}; {==} : {String.split.push(c, T0) == Con{SCon{c, tk}, GL.tl(String.split.push(c, T0))} : Ss()}},
       {%sy : {GC(rs) == PB(L.gt_ok.go(GL.tl(String.split.push(c, _)), n)) : Maybe<&2, B.Code>}; e2 : {GC(rs) == PB(L.gt_ok.go(GL.tl(String.split.push(c, T0)), n)) : Maybe<&2, B.Code>}})

def gr.k(+o0: Bool, +n: Nat, +i: Nat, +b: Bool, +c: Char, +t: String, r: B.Gp,
  +eb: {GL.sep(c) == b : Bool},
  ih: GR(o0, n, i, t, r)) -> GR(o0, n, i, SCon{c, t}, B.Gt.go.put(b, c, r, o0, n, i)):
  match b r:
    case True{} B.Gp{+tk, +rs}:
      %Equal.sym(Bool, GL.sep(c), True{}, eb) : GRT(n, GL.tks.put(_, c, GL.TKS(t)), "", GL.RSP(o0, n, i, c, tk, rs))
      gr.t(o0, n, i, c, t, tk, rs, ih)
    case False{} B.Gp{+tk, +rs}:
      %Equal.sym(Bool, GL.sep(c), False{}, eb) : GRT(n, GL.tks.put(_, c, GL.TKS(t)), SCon{c, tk}, rs)
      gr.f(n, c, t, tk, rs, ih)

law gr:
  for +g: String
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  GR(o0, n, i, g, B.Gt.go(g, o0, n, i))

def gr(g, o0, n, i):
  match g:
    case SNil{}:
      ({==}, {==})
    case SCon{+c, +t}:
      gr.k(o0, n, i, GL.sep(c), c, t, B.Gt.go(t, o0, n, i), {==}, gr(t, o0, n, i))

def gt_gc.q(+o0: Bool, +n: Nat, +i: Nat, +g: String, +tk: String, +rs: B.Got, q: GRT(n, GL.TKS(g), tk, rs)) ->
  {GC(B.Got.cat(GL.AL(o0, n, i, tk), "", rs)) == PB(L.gt_ok.go(GL.TKS(g), n)) : Maybe<&2, B.Code>}:
  match q:
    case (e1, e2):
      +R = GL.tl(GL.TKS(g))
      Equal.trans(Maybe<&2, B.Code>, GC(B.Got.cat(GL.AL(o0, n, i, tk), "", rs)), L.first_code.put(GC(GL.AL(o0, n, i, tk)), GC(rs)), PB(L.gt_ok.go(GL.TKS(g), n)),
        cat_gc(GL.AL(o0, n, i, tk), "", rs),
        Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(GL.AL(o0, n, i, tk)), GC(rs)), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), PB(L.gt_ok.go(GL.TKS(g), n)),
          Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(GL.AL(o0, n, i, tk)), GC(rs)), L.first_code.put(GC(GL.AL(o0, n, i, tk)), PB(L.gt_ok.go(R, n))), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))),
            Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(GC(GL.AL(o0, n, i, tk)), z), GC(rs), PB(L.gt_ok.go(R, n)), e2),
            Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, PB(L.gt_ok.go(R, n))), GC(GL.AL(o0, n, i, tk)), PB(TOKOK(tk, n)), tokg(o0, n, i, tk))),
          Equal.trans(Maybe<&2, B.Code>, L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), PB(L.gt_ok.go(Con{tk, R}, n)), PB(L.gt_ok.go(GL.TKS(g), n)),
            Equal.sym(Maybe<&2, B.Code>, PB(L.gt_ok.go(Con{tk, R}, n)), L.first_code.put(PB(TOKOK(tk, n)), PB(L.gt_ok.go(R, n))), pand(TOKOK(tk, n), L.gt_ok.go(R, n))),
            Equal.cong(Ss(), Maybe<&2, B.Code>, z => PB(L.gt_ok.go(z, n)), Con{tk, R}, GL.TKS(g), Equal.sym(Ss(), GL.TKS(g), Con{tk, R}, e1)))))

def gt_gc.k(+o0: Bool, +n: Nat, +i: Nat, +g: String, r: B.Gp, q: GR(o0, n, i, g, r)) ->
  {GC(B.Gt.split.of(r, o0, n, i)) == PB(L.gt_ok.go(GL.TKS(g), n)) : Maybe<&2, B.Code>}:
  match r:
    case B.Gp{+tk, +rs}:
      gt_gc.q(o0, n, i, g, tk, rs, q)

# A genotype in the record for ALT i: BAD_GT exactly when gt_problem says.
law gt_gc:
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +g: String
  {GC(B.Gt.split(o0, n, i, g)) == L.gt_problem(n, g) : Maybe<&2, B.Code>}

def gt_gc(o0, n, i, g):
  %Equal.sym(Ss(), L.gt_tokens(g), GL.TKS(g), GL.tk_eq(g)) : {GC(B.Gt.split(o0, n, i, g)) == PB(L.gt_ok.go(_, n)) : Maybe<&2, B.Code>}
  gt_gc.k(o0, n, i, g, B.Gt.go(g, o0, n, i), gr(g, o0, n, i))

# ---------------------------------------------------------------------------
# Columns and records
# ---------------------------------------------------------------------------

def fo.b(+b: Bool, +k: String, +v: String, +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(Bool.pick(B.Got, b, B.Gt.split(o0, n, i, v), B.Fmt.split.num(B.Tags.find(fmt, k), k, v, n, cp, i))) == Bool.pick(Maybe<&2, B.Code>, b, L.gt_problem(n, v), L.format_problem(B.Tags.find(fmt, k), k, v, n, cp)) : Maybe<&2, B.Code>}:
  match b:
    case True{}:
      gt_gc(o0, n, i, v)
    case False{}:
      fn_gc(B.Tags.find(fmt, k), k, v, n, cp, i, hi, hin)

law fgo_fr:
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +o0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +hi: {Nat.is_le(1n, i) == True{} : Bool}
  for +hin: {Nat.is_le(i, n) == True{} : Bool}
  {FR(B.Fmt.split.go(ks, vs, fmt, o0, n, cp, i)) == L.first_code(L.sample_problems(ks, vs, fmt, n, cp)) : Maybe<&2, B.Code>}

def fgo_fr(ks, vs, fmt, o0, n, cp, i, hi, hin):
  match ks vs:
    case _ Nil{}:
      {==}
    case Nil{} Con{+v, +t}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      +A = GC(B.Fmt.split.one(k, v, fmt, o0, n, cp, i))
      +A2 = Bool.pick(Maybe<&2, B.Code>, String.eq(k, "GT"), L.gt_problem(n, v), L.format_problem(B.Tags.find(fmt, k), k, v, n, cp))
      Equal.trans(Maybe<&2, B.Code>, L.first_code.put(A, FR(B.Fmt.split.go(kt, vt, fmt, o0, n, cp, i))), L.first_code.put(A2, FR(B.Fmt.split.go(kt, vt, fmt, o0, n, cp, i))), L.first_code.put(A2, L.first_code(L.sample_problems(kt, vt, fmt, n, cp))),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, FR(B.Fmt.split.go(kt, vt, fmt, o0, n, cp, i))), A, A2, fo.b(String.eq(k, "GT"), k, v, fmt, o0, n, cp, i, hi, hin)),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(A2, z), FR(B.Fmt.split.go(kt, vt, fmt, o0, n, cp, i)), L.first_code(L.sample_problems(kt, vt, fmt, n, cp)), fgo_fr(kt, vt, fmt, o0, n, cp, i, hi, hin)))

# A sample column in the record for ALT i: refused as its problems say.
def col_gc(+ks: Ss(), +col: String, +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(B.Fmt.split(ks, col, fmt, o0, n, i)) == L.first_code(L.sample_problems(ks, String.split(col, ':'), fmt, n, B.Gt.copies(B.Fmt.gt(ks, String.split(col, ':'))))) : Maybe<&2, B.Code>}:
  +vs = String.split(col, ':')
  +cp = B.Gt.copies(B.Fmt.gt(ks, vs))
  Equal.trans(Maybe<&2, B.Code>, GC(B.Fmt.split(ks, col, fmt, o0, n, i)), FR(B.Fmt.split.go(ks, vs, fmt, o0, n, cp, i)), L.first_code(L.sample_problems(ks, vs, fmt, n, cp)),
    join_gc(B.Fmt.split.go(ks, vs, fmt, o0, n, cp, i), ":"), fgo_fr(ks, vs, fmt, o0, n, cp, i, hi, hin))

law igo_fr:
  for +es: Ss()
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +hi: {Nat.is_le(1n, i) == True{} : Bool}
  for +hin: {Nat.is_le(i, n) == True{} : Bool}
  {FR(B.Info.split.go(es, tags, n, i)) == L.first_code(L.info_problems(es, tags, n)) : Maybe<&2, B.Code>}

def igo_fr(es, tags, n, i, hi, hin):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +m = B.Tags.find(tags, B.Info.key(e))
      Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(B.Info.split.num(m, e, n, i)), FR(B.Info.split.go(t, tags, n, i))), L.first_code.put(L.info_problem(m, e, n), FR(B.Info.split.go(t, tags, n, i))), L.first_code.put(L.info_problem(m, e, n), L.first_code(L.info_problems(t, tags, n))),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, FR(B.Info.split.go(t, tags, n, i))), GC(B.Info.split.num(m, e, n, i)), L.info_problem(m, e, n), in_gc(m, e, n, i, hi, hin)),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(L.info_problem(m, e, n), z), FR(B.Info.split.go(t, tags, n, i)), L.first_code(L.info_problems(t, tags, n)), igo_fr(t, tags, n, i, hi, hin)))

# INFO in the record for ALT i: refused as its entries' problems say.
def info_gc(+info: String, +tags: List<&2, B.Tag>, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {GC(B.Info.split(info, tags, n, i)) == L.first_code(L.info_problems(String.split(info, ';'), tags, n)) : Maybe<&2, B.Code>}:
  Equal.trans(Maybe<&2, B.Code>, GC(B.Info.split(info, tags, n, i)), FR(B.Info.split.go(String.split(info, ';'), tags, n, i)), L.first_code(L.info_problems(String.split(info, ';'), tags, n)),
    join_gc(B.Info.split.go(String.split(info, ';'), tags, n, i), ";"), igo_fr(String.split(info, ';'), tags, n, i, hi, hin))

def KSF(+fs: Ss()) -> Ss():
  String.split(B.Rec.field(fs, 8n), ':')

# What is wrong with a line of fields fs, after its ALTs: its INFO entries,
# then its samples (split_problem without ALT_DUP).
def PROBF(+fs: Ss(), +defs: B.Defs, +n: Nat) -> Maybe<&2, B.Code>:
  L.first_code(List.append(&2, Maybe<&2, B.Code>, L.info_problems(String.split(B.Rec.field(fs, 7n), ';'), B.Defs.info(defs), n),
    L.samples_problems(List.drop(&2, String, fs, 9n), KSF(fs), B.Defs.fmt(defs), n)))

def ne.k(+b: Bool, +j: Nat, +x: Nat, +eb: {Nat.is_eq(j, x) == b : Bool}, +hj: {Nat.is_le(9n, j) == True{} : Bool}, +hx: {Nat.is_le(9n, x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +e = N.eq_sound(j, x, eb)
      +c = Equal.cong(Nat, Bool, z => Nat.is_le(9n, z), j, x, e)
      +h2 = Equal.trans(Bool, Nat.is_le(9n, x), Nat.is_le(9n, j), True{}, Equal.sym(Bool, Nat.is_le(9n, j), Nat.is_le(9n, x), c), hj)
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(9n, x), True{}, Equal.sym(Bool, Nat.is_le(9n, x), False{}, hx), h2)))

# Field j >= 9 of a record: a sample column, split.
def pf9(+j: Nat, +hj: {Nat.is_le(9n, j) == True{} : Bool}, +f: String, +a: String, +defs: B.Defs, +ks: Ss(), +o0: Bool, +n: Nat, +i: Nat) ->
  {B.Rec.piece.field(j, f, a, defs, ks, o0, n, i) == B.Fmt.split(ks, f, B.Defs.fmt(defs), o0, n, i) : B.Got}:
  +F = B.Fmt.split(ks, f, B.Defs.fmt(defs), o0, n, i)
  +I = B.Info.split(f, B.Defs.info(defs), n, i)
  %Equal.sym(Bool, Nat.is_eq(j, 4n), False{}, ne.k(Nat.is_eq(j, 4n), j, 4n, {==}, hj, {==})) :
    {Bool.pick(B.Got, _, B.Got{a}, Bool.pick(B.Got, Nat.is_eq(j, 7n), I, Bool.pick(B.Got, Nat.is_le(9n, j), F, B.Got{f}))) == F : B.Got}
  %Equal.sym(Bool, Nat.is_eq(j, 7n), False{}, ne.k(Nat.is_eq(j, 7n), j, 7n, {==}, hj, {==})) :
    {Bool.pick(B.Got, _, I, Bool.pick(B.Got, Nat.is_le(9n, j), F, B.Got{f})) == F : B.Got}
  %Equal.sym(Bool, Nat.is_le(9n, j), True{}, hj) : {Bool.pick(B.Got, _, F, B.Got{f}) == F : B.Got}
  {==}

def le9s(+j: Nat, +hj: {Nat.is_le(9n, j) == True{} : Bool}) -> {Nat.is_le(9n, 1n+j) == True{} : Bool}:
  N.le_trans(9n, j, 1n+j, hj, N.lt_to_le(j, 1n+j, Equal.trans(Bool, Nat.is_lt(j, 1n+j), Nat.is_le(j, j), True{}, N.lt_succ_iff(j, j), N.le_refl(j))))

law cols_fr:
  for +cols: Ss()
  for +j: Nat
  for +hj: {Nat.is_le(9n, j) == True{} : Bool}
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +hi: {Nat.is_le(1n, i) == True{} : Bool}
  for +hin: {Nat.is_le(i, n) == True{} : Bool}
  {FR(B.Rec.piece.go(cols, j, a, defs, ks, o0, n, i)) == L.first_code(L.samples_problems(cols, ks, B.Defs.fmt(defs), n)) : Maybe<&2, B.Code>}

def cols_fr(cols, j, hj, a, defs, ks, o0, n, i, hi, hin):
  match cols:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +fmt = B.Defs.fmt(defs)
      +vs = String.split(c, ':')
      +SP1 = L.sample_problems(ks, vs, fmt, n, B.Gt.copies(B.Fmt.gt(ks, vs)))
      +RST = L.samples_problems(t, ks, fmt, n)
      Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(B.Rec.piece.field(j, c, a, defs, ks, o0, n, i)), FR(B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(SP1), L.first_code(RST)), L.first_code(List.append(&2, Maybe<&2, B.Code>, SP1, RST)),
        Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(B.Rec.piece.field(j, c, a, defs, ks, o0, n, i)), FR(B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(SP1), FR(B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(SP1), L.first_code(RST)),
          Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, FR(B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i))), GC(B.Rec.piece.field(j, c, a, defs, ks, o0, n, i)), L.first_code(SP1),
            Equal.trans(Maybe<&2, B.Code>, GC(B.Rec.piece.field(j, c, a, defs, ks, o0, n, i)), GC(B.Fmt.split(ks, c, fmt, o0, n, i)), L.first_code(SP1),
              Equal.cong(B.Got, Maybe<&2, B.Code>, z => GC(z), B.Rec.piece.field(j, c, a, defs, ks, o0, n, i), B.Fmt.split(ks, c, fmt, o0, n, i), pf9(j, hj, c, a, defs, ks, o0, n, i)),
              col_gc(ks, c, fmt, o0, n, i, hi, hin))),
          Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(L.first_code(SP1), z), FR(B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i)), L.first_code(RST), cols_fr(t, 1n+j, le9s(j, hj), a, defs, ks, o0, n, i, hi, hin))),
        Equal.sym(Maybe<&2, B.Code>, L.first_code(List.append(&2, Maybe<&2, B.Code>, SP1, RST)), L.first_code.put(L.first_code(SP1), L.first_code(RST)), fc_app(SP1, RST)))

def r9(cols: Ss(), +a: String, +defs: B.Defs, +ks: Ss(), +o0: Bool, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {FR(B.Rec.piece.go(cols, 9n, a, defs, ks, o0, n, i)) == L.first_code(L.samples_problems(List.drop(&2, String, cols, 0n), ks, B.Defs.fmt(defs), n)) : Maybe<&2, B.Code>}:
  match cols:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      cols_fr(Con{c, t}, 9n, {==}, a, defs, ks, o0, n, i, hi, hin)

def r8(r: Ss(), +a: String, +defs: B.Defs, +ks: Ss(), +o0: Bool, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool}) ->
  {FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i)) == L.first_code(L.samples_problems(List.drop(&2, String, r, 1n), ks, B.Defs.fmt(defs), n)) : Maybe<&2, B.Code>}:
  match r:
    case Nil{}:
      {==}
    case Con{+f8, +cols}:
      r9(cols, a, defs, ks, o0, n, i, hi, hin)

# A record of a line of fields fs (not MALFORMED), for ALT i (1 to n): refused
# with the line's first problem after its ALTs.
def piece_gc(fs: Ss(), +a: String, +defs: B.Defs, +o0: Bool, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hin: {Nat.is_le(i, n) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) -> {GC(B.Rec.piece(fs, a, defs, o0, n, i)) == PROBF(fs, defs, n) : Maybe<&2, B.Code>}:
  match fs:
    case Nil{}:
      Empty.absurd({GC(B.Rec.piece(Nil{}, a, defs, o0, n, i)) == PROBF(Nil{}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Nil{}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Nil{}}, a, defs, o0, n, i)) == PROBF(Con{f0, Nil{}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Nil{}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Nil{}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Con{f2, Nil{}}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Con{f2, Nil{}}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({GC(B.Rec.piece(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, a, defs, o0, n, i)) == PROBF(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, defs, n) : Maybe<&2, B.Code>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +r}}}}}}}}:
      +FS8 = SM.F8(f0, f1, f2, f3, f4, f5, f6, f7, r)
      +ks = KSF(FS8)
      +IP = L.info_problems(String.split(f7, ';'), B.Defs.info(defs), n)
      +SP = L.samples_problems(List.drop(&2, String, r, 1n), ks, B.Defs.fmt(defs), n)
      Equal.trans(Maybe<&2, B.Code>, GC(B.Rec.piece(FS8, a, defs, o0, n, i)), L.first_code.put(L.first_code(IP), L.first_code(SP)), PROBF(FS8, defs, n),
        Equal.trans(Maybe<&2, B.Code>, GC(B.Rec.piece(FS8, a, defs, o0, n, i)), L.first_code.put(GC(B.Info.split(f7, B.Defs.info(defs), n, i)), FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(IP), L.first_code(SP)),
          join_gc(B.Rec.piece.go(FS8, 0n, a, defs, ks, o0, n, i), "\t"),
          Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(B.Info.split(f7, B.Defs.info(defs), n, i)), FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(IP), FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i))), L.first_code.put(L.first_code(IP), L.first_code(SP)),
            Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(z, FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i))), GC(B.Info.split(f7, B.Defs.info(defs), n, i)), L.first_code(IP), info_gc(f7, B.Defs.info(defs), n, i, hi, hin)),
            Equal.cong(Maybe<&2, B.Code>, Maybe<&2, B.Code>, z => L.first_code.put(L.first_code(IP), z), FR(B.Rec.piece.go(r, 8n, a, defs, ks, o0, n, i)), L.first_code(SP), r8(r, a, defs, ks, o0, n, i, hi, hin)))),
        Equal.sym(Maybe<&2, B.Code>, PROBF(FS8, defs, n), L.first_code.put(L.first_code(IP), L.first_code(SP)), fc_app(IP, SP)))

def put_idem(+m: Maybe<&2, B.Code>) -> {L.first_code.put(m, m) == m : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      {==}

# The records of a line for ALTs a, t... (from ALT i on, i >= 1, the last at
# most n): their first refusal is the line's first problem after its ALTs.
def pfr(t: Ss(), +a: String, +fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +i: Nat,
  +hi: {Nat.is_le(1n, i) == True{} : Bool},
  +hb: {Nat.is_le(Nat.add(i, List.length(&2, String, t)), n) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) ->
  {FR(B.Rec.pieces.go(Con{a, t}, fs, defs, o0, n, i)) == PROBF(fs, defs, n) : Maybe<&2, B.Code>}:
  match t:
    case Nil{}:
      +hin = N.le_trans(i, Nat.add(i, 0n), n, N.le_add_r(i, 0n), hb)
      Equal.trans(Maybe<&2, B.Code>, L.first_code.put(GC(B.Rec.piece(fs, a, defs, o0, n, i)), None{}), GC(B.Rec.piece(fs, a, defs, o0, n, i)), PROBF(fs, defs, n),
        fc_none(GC(B.Rec.piece(fs, a, defs, o0, n, i))), piece_gc(fs, a, defs, o0, n, i, hi, hin, hl))
    case Con{+b, +u}:
      +hin = N.le_trans(i, Nat.add(i, 1n+List.length(&2, String, u)), n, N.le_add_r(i, 1n+List.length(&2, String, u)), hb)
      +hb2 = Equal.trans(Bool, Nat.is_le(1n+Nat.add(i, List.length(&2, String, u)), n), Nat.is_le(Nat.add(i, 1n+List.length(&2, String, u)), n), True{},
        Equal.cong(Nat, Bool, z => Nat.is_le(z, n), 1n+Nat.add(i, List.length(&2, String, u)), Nat.add(i, 1n+List.length(&2, String, u)),
          Equal.sym(Nat, Nat.add(i, 1n+List.length(&2, String, u)), 1n+Nat.add(i, List.length(&2, String, u)), N.add_succ(i, List.length(&2, String, u)))),
        hb)
      +P = PROBF(fs, defs, n)
      %Equal.sym(Maybe<&2, B.Code>, GC(B.Rec.piece(fs, a, defs, o0, n, i)), P, piece_gc(fs, a, defs, o0, n, i, hi, hin, hl)) :
        {L.first_code.put(_, FR(B.Rec.pieces.go(Con{b, u}, fs, defs, o0, n, 1n+i))) == P : Maybe<&2, B.Code>}
      %Equal.sym(Maybe<&2, B.Code>, FR(B.Rec.pieces.go(Con{b, u}, fs, defs, o0, n, 1n+i)), P, pfr(u, b, fs, defs, o0, n, 1n+i, N.le_zero_l(i), hb2, hl)) :
        {L.first_code.put(P, _) == P : Maybe<&2, B.Code>}
      put_idem(P)

def orf(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      h

# Split ALTs (two or more, no duplicates): refused with the first problem.
def ws.p(alts: Ss(), +fs: Ss(), +defs: B.Defs, +o0: Bool,
  +h2: {Nat.is_le(2n, List.length(&2, String, alts)) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) ->
  {L.refusal(B.Parts.of(B.Rec.pieces.go(alts, fs, defs, o0, List.length(&2, String, alts), 1n))) == Some{PROBF(fs, defs, List.length(&2, String, alts))} : Maybe<&2, Maybe<&2, B.Code>>}:
  match alts:
    case Nil{}:
      Empty.absurd({L.refusal(B.Parts.of(B.Rec.pieces.go(Nil{}, fs, defs, o0, 0n, 1n))) == Some{PROBF(fs, defs, 0n)} : Maybe<&2, Maybe<&2, B.Code>>}, N.false_ne_true(h2))
    case Con{+a, +t}:
      +gs = B.Rec.pieces.go(Con{a, t}, fs, defs, o0, 1n+List.length(&2, String, t), 1n)
      Equal.trans(Maybe<&2, Maybe<&2, B.Code>>, L.refusal(B.Parts.of(gs)), Some{FR(gs)}, Some{PROBF(fs, defs, 1n+List.length(&2, String, t))},
        po(gs),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, Maybe<&2, B.Code>>, z => Some{z}, FR(gs), PROBF(fs, defs, 1n+List.length(&2, String, t)),
          pfr(t, a, fs, defs, o0, 1n+List.length(&2, String, t), 1n, {==}, N.le_refl(List.length(&2, String, t)), hl)))

def ws.k(d: Bool, +fs: Ss(), +defs: B.Defs, +o0: Bool,
  +h2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) ->
  {L.refusal(B.Rec.parts.split(d, B.Rec.alts(fs), fs, defs, o0)) ==
   Some{L.first_code(Con{Bool.pick(Maybe<&2, B.Code>, d, None{}, Some{B.DupAlts{}}),
     List.append(&2, Maybe<&2, B.Code>, L.info_problems(String.split(B.Rec.field(fs, 7n), ';'), B.Defs.info(defs), List.length(&2, String, B.Rec.alts(fs))),
       L.samples_problems(List.drop(&2, String, fs, 9n), KSF(fs), B.Defs.fmt(defs), List.length(&2, String, B.Rec.alts(fs))))})} : Maybe<&2, Maybe<&2, B.Code>>}:
  match d:
    case False{}:
      {==}
    case True{}:
      ws.p(B.Rec.alts(fs), fs, defs, o0, h2, hl)

# split_problem with a CR in the line: BAD_CR; without one: the rest.
def sp_t(+defs: B.Defs, +body: String, +ecr: {B.Text.has_cr(body) == True{} : Bool}) -> {L.split_problem(defs, body) == Some{B.BadCr{}} : Maybe<&2, B.Code>}:
  %Equal.sym(Bool, B.Text.has_cr(body), True{}, ecr) :
    {L.first_code(Bool.pick(Maybe<&2, B.Code>, _, Some{B.BadCr{}}, None{}) <> Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))) == Some{B.BadCr{}} : Maybe<&2, B.Code>}
  {==}

def sp_f(+defs: B.Defs, +body: String, +ecr: {B.Text.has_cr(body) == False{} : Bool}) ->
  {L.split_problem(defs, body) == L.first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))) : Maybe<&2, B.Code>}:
  %Equal.sym(Bool, B.Text.has_cr(body), False{}, ecr) :
    {L.first_code(Bool.pick(Maybe<&2, B.Code>, _, Some{B.BadCr{}}, None{}) <> Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))) == L.first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))) : Maybe<&2, B.Code>}
  {==}

def ws.c(cr: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ecr: {B.Text.has_cr(body) == cr : Bool},
  +h2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, B.Rec.fields(body)), 8n) == False{} : Bool}) ->
  {L.refusal(B.Rec.parts.cr(cr, defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}:
  match cr:
    case True{}:
      Equal.cong(Maybe<&2, B.Code>, Maybe<&2, Maybe<&2, B.Code>>, z => Some{z}, Some{B.BadCr{}}, L.split_problem(defs, body),
        Equal.sym(Maybe<&2, B.Code>, L.split_problem(defs, body), Some{B.BadCr{}}, sp_t(defs, body, ecr)))
    case False{}:
      +fs = B.Rec.fields(body)
      Equal.trans(Maybe<&2, Maybe<&2, B.Code>>, L.refusal(B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(fs)), B.Rec.alts(fs), fs, defs, o0)), Some{L.first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body))))}, Some{L.split_problem(defs, body)},
        ws.k(B.Alts.distinct(B.Rec.alts(fs)), fs, defs, o0, h2, hl),
        Equal.cong(Maybe<&2, B.Code>, Maybe<&2, Maybe<&2, B.Code>>, z => Some{z}, L.first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))), L.split_problem(defs, body),
          Equal.sym(Maybe<&2, B.Code>, L.split_problem(defs, body), L.first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, L.info_problems(L.info_entries(body), B.Defs.info(defs), L.n_alts(body)),
         L.samples_problems(List.drop(&2, String, B.Rec.fields(body), 9n), L.format_keys(body), B.Defs.fmt(defs), L.n_alts(body)))), sp_f(defs, body, ecr))))

def ws.n(+defs: B.Defs, +o0: Bool, +body: String, +h2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, B.Rec.fields(body)), 8n) == False{} : Bool}) ->
  {L.refusal(B.Rec.parts.if(Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}:
  %Equal.sym(Bool, Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), True{}, h2) : {L.refusal(B.Rec.parts.if(_, B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}
  ws.c(B.Text.has_cr(body), defs, o0, body, {==}, h2, hl)

def ws.m(m: Bool, +hm: {m == False{} : Bool}, +defs: B.Defs, +o0: Bool, +body: String, +h2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, B.Rec.fields(body)), 8n) == False{} : Bool}) ->
  {L.refusal(B.Rec.parts.if(Bool.not(m) && Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}:
  match m:
    case True{}:
      Empty.absurd({L.refusal(B.Rec.parts.if(Bool.not(True{}) && Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hm)))
    case False{}:
      ws.n(defs, o0, body, h2, hl)

def ws.s(s: Bool, +hs: {s == True{} : Bool}, +m: Bool, +hm: {m == False{} : Bool}, +defs: B.Defs, +o0: Bool, +body: String, +h2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, B.Rec.fields(body)), 8n) == False{} : Bool}) ->
  {L.refusal(B.Rec.parts.if(s && Bool.not(m) && Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}:
  match s:
    case False{}:
      Empty.absurd({L.refusal(B.Rec.parts.if(False{} && Bool.not(m) && Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))), B.Text.has_cr(body), defs, o0, B.Rec.fields(body))) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}, N.false_ne_true(hs))
    case True{}:
      ws.m(m, hm, defs, o0, body, h2, hl)

law split_when_p:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +hs: {R.Opts.split(o) == True{} : Bool}
  for +hm: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool}
  for +hn: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}
  {L.refusal(B.Rec.parts(defs, o, body)) == Some{L.split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}

def split_when_p(defs, o, body, hs, hm, hn):
  match o:
    case B.Opts{+s, +w, +split, +over0, +args}:
      +fs = B.Rec.fields(body)
      +h4 = orf(Bool.or(Bool.or(Bool.or(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n)))), B.Text.any_empty(B.Rec.alts(fs)), hm)
      +h3 = orf(Bool.or(Bool.or(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n))), h4)
      +h2 = orf(Bool.or(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n))), h3)
      +hl = orf(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n)), h2)
      ws.s(split, hs, B.Rec.malformed(fs), hm, defs, over0, body, hn, hl)
