import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_ient.bend as IE
import ./proof_s_ikeys.bend as IK
import ./proof_s_when.bend as W
import ./proof_s_tri.bend as TR
import ./proof_s_change.bend as SC
import ./proof_s_valid.bend as V
import ./proof_run_line.bend as NL
import ./proof_run_rejudge.bend as J
import ./proof_run_rec.bend as C
import ./proof_run_steps.bend as T
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_normalized: when the whole line would be normalized, so is every
# record. The END entries come through unchanged (a per-allele END that reads
# as a number has one value, too few to split), so END stays fine; the rest
# follows from split_site, split_alts and split_valid. Every variable is
# reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def Ms() -> Data:
  List<&2, Maybe<&2, Nat>>

# A number has no comma
# =====================

def push_none(acc: Maybe<&2, Nat>) -> {B.Pos.read.push(acc, None{}) == None{} : Maybe<&2, Nat>}:
  match acc:
    case Some{+a}:
      {==}
    case None{}:
      {==}

def push_n0(d: Maybe<&2, Nat>) -> {B.Pos.read.push(None{}, d) == None{} : Maybe<&2, Nat>}:
  match d:
    case Some{+a}:
      {==}
    case None{}:
      {==}

law rg_none:
  for +t: String
  {B.Pos.read.go(t, None{}) == None{} : Maybe<&2, Nat>}

def rg_none(t):
  match t:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(Maybe<&2, Nat>, B.Pos.read.push(None{}, B.Pos.digit(h)), None{}, push_n0(B.Pos.digit(h))) : {B.Pos.read.go(r, _) == None{} : Maybe<&2, Nat>}
      rg_none(r)

def some_none(+d: Nat, +h: {Some{d} == None{} : Maybe<&2, Nat>}) -> Empty:
  AB.false_ne_true(Equal.cong(Maybe<&2, Nat>, Bool, z => Maybe.is_some(&2, Nat, z), None{}, Some{d}, Equal.sym(Maybe<&2, Nat>, Some{d}, None{}, h)))

def pn.x(b: Bool, +x: U32, +t: String, acc: Maybe<&2, Nat>, +d: Nat,
  +eb: {U32.is_eq(x, 44) == b : Bool},
  +h: {B.Pos.read.go(t, B.Pos.read.push(acc, B.Pos.digit(Chr{x}))) == Some{d} : Maybe<&2, Nat>},
  ih: @acc2: Maybe<&2, Nat> -> {B.Pos.read.go(t, acc2) == Some{d} : Maybe<&2, Nat>} -> {ST.noc(t, ',') == True{} : Bool}) ->
  {ST.noc(SCon{Chr{x}, t}, ',') == True{} : Bool}:
  match b:
    case True{}:
      +ex = U.is_eq_true(x, 44, eb)
      +h2 = {(%ex : {B.Pos.read.go(t, B.Pos.read.push(acc, B.Pos.digit(Chr{_}))) == Some{d} : Maybe<&2, Nat>}; h) :
        {B.Pos.read.go(t, B.Pos.read.push(acc, None{})) == Some{d} : Maybe<&2, Nat>}}
      +h3 = {(%push_none(acc) : {B.Pos.read.go(t, _) == Some{d} : Maybe<&2, Nat>}; h2) : {B.Pos.read.go(t, None{}) == Some{d} : Maybe<&2, Nat>}}
      Empty.absurd({ST.noc(SCon{Chr{x}, t}, ',') == True{} : Bool},
        some_none(d, Equal.trans(Maybe<&2, Nat>, Some{d}, B.Pos.read.go(t, None{}), None{}, Equal.sym(Maybe<&2, Nat>, B.Pos.read.go(t, None{}), Some{d}, h3), rg_none(t))))
    case False{}:
      %Equal.sym(Bool, U32.is_eq(x, 44), False{}, eb) : {Bool.and(Bool.not(_), ST.noc(t, ',')) == True{} : Bool}
      ih(B.Pos.read.push(acc, B.Pos.digit(Chr{x})), h)

def pn.c(c: Char, +t: String, acc: Maybe<&2, Nat>, +d: Nat,
  +h: {B.Pos.read.go(SCon{c, t}, acc) == Some{d} : Maybe<&2, Nat>},
  ih: @acc2: Maybe<&2, Nat> -> {B.Pos.read.go(t, acc2) == Some{d} : Maybe<&2, Nat>} -> {ST.noc(t, ',') == True{} : Bool}) ->
  {ST.noc(SCon{c, t}, ',') == True{} : Bool}:
  match c:
    case Chr{+x}:
      pn.x(U32.is_eq(x, 44), x, t, acc, d, {==}, h, ih)

law pos_noc:
  for +s: String
  for +acc: Maybe<&2, Nat>
  for +d: Nat
  for +h: {B.Pos.read.go(s, acc) == Some{d} : Maybe<&2, Nat>}
  {ST.noc(s, ',') == True{} : Bool}

def pos_noc(s, acc, d, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      pn.c(c, t, acc, d, h, acc2 => h2 => pos_noc(t, acc2, d, h2))

def pos_noc1(v: String, +d: Nat, +h: {B.Pos.read(v) == Some{d} : Maybe<&2, Nat>}) -> {ST.noc(v, ',') == True{} : Bool}:
  match v:
    case SNil{}:
      Empty.absurd({ST.noc(SNil{}, ',') == True{} : Bool}, some_none(d, Equal.sym(Maybe<&2, Nat>, None{}, Some{d}, h)))
    case SCon{+c, +t}:
      pos_noc(SCon{c, t}, Some{0n}, d, h)

# A per-allele END that reads as a number cannot split
# ====================================================

def cnt_ne1(+m: Nat) -> {Nat.is_eq(B.Gt.count(1n+(1n+m)), 1n) == False{} : Bool}:
  +T = TR.tri(1n+(1n+m))
  %Equal.sym(Nat, B.Gt.count(1n+(1n+m)), Nat.add(T, 1n+(1n+(1n+m))), TR.cnt_eq(1n+(1n+m))) : {Nat.is_eq(_, 1n) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(T, 1n+(1n+(1n+m))), 1n+Nat.add(T, 1n+(1n+m)), N.add_succ(T, 1n+(1n+m))) : {Nat.is_eq(_, 1n) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(T, 1n+(1n+m)), 1n+Nat.add(T, 1n+m), N.add_succ(T, 1n+m)) : {Nat.is_eq(1n+_, 1n) == False{} : Bool}
  {==}

def fit1.k(num: B.Num, +m: Nat, +ha: {B.Num.per_allele(Some{num}) == True{} : Bool}) ->
  {B.Vals.fits(B.Vals.expected_count(num, 1n+(1n+m), 2n), 1n) == False{} : Bool}:
  match num:
    case B.NumA{}:
      {==}
    case B.NumR{}:
      {==}
    case B.NumG{}:
      cnt_ne1(m)
    case B.NumOther{}:
      Empty.absurd({B.Vals.fits(B.Vals.expected_count(B.NumOther{}, 1n+(1n+m), 2n), 1n) == False{} : Bool}, AB.false_ne_true(ha))
    case B.NumUnknown{}:
      Empty.absurd({B.Vals.fits(B.Vals.expected_count(B.NumUnknown{}, 1n+(1n+m), 2n), 1n) == False{} : Bool}, AB.false_ne_true(ha))

# One value does not fit a per-allele count when there are two ALTs or more.
def fit1(n: Nat, +num: B.Num, +ha: {B.Num.per_allele(Some{num}) == True{} : Bool}, +hn: {Nat.is_le(2n, n) == True{} : Bool}) ->
  {B.Vals.fits(B.Vals.expected_count(num, n, 2n), 1n) == False{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({B.Vals.fits(B.Vals.expected_count(num, 0n, 2n), 1n) == False{} : Bool}, AB.false_ne_true(hn))
    case 1n+(0n):
      Empty.absurd({B.Vals.fits(B.Vals.expected_count(num, 1n, 2n), 1n) == False{} : Bool}, AB.false_ne_true(hn))
    case 1n+(1n+(+m)):
      fit1.k(num, m, ha)

def dot_none(+v: String, +d: Nat, +hp: {B.Pos.read(v) == Some{d} : Maybe<&2, Nat>}, c: Bool, +ec: {String.eq(v, ".") == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e = Q.str_eq_sound(v, ".", ec)
      +h2 = {(%e : {B.Pos.read(_) == Some{d} : Maybe<&2, Nat>}; hp) : {B.Pos.read(".") == Some{d} : Maybe<&2, Nat>}}
      Empty.absurd({True{} == False{} : Bool}, some_none(d, Equal.sym(Maybe<&2, Nat>, B.Pos.read("."), Some{d}, h2)))

# The values v of a per-allele entry that read as a number: refused.
def vs_none(+num: B.Num, +n: Nat, +i: Nat, +v: String, +d: Nat,
  +ha: {B.Num.per_allele(Some{num}) == True{} : Bool}, +hn: {Nat.is_le(2n, n) == True{} : Bool},
  +hp: {B.Pos.read(v) == Some{d} : Maybe<&2, Nat>}) ->
  {B.Vals.split(num, n, Some{2n}, i, v) == None{} : Maybe<&2, String>}:
  %Equal.sym(Bool, String.eq(v, "."), False{}, dot_none(v, d, hp, String.eq(v, "."), {==})) :
    {B.Vals.split.if(_, num, n, Some{2n}, i, v) == None{} : Maybe<&2, String>}
  %Equal.sym(Ss(), String.split(v, ','), [v], ST.split_noc(v, ',', pos_noc1(v, d, hp))) :
    {B.Vals.keep(num, n, B.Vals.copies(Some{2n}, n, List.length(&2, String, _)), i, _) == None{} : Maybe<&2, String>}
  %Equal.sym(Bool, B.Vals.fits(B.Vals.expected_count(num, n, 2n), 1n), False{}, fit1(n, num, ha, hn)) :
    {Bool.pick(Maybe<&2, String>, _, B.Vals.join(B.Vals.pick([v], B.Vals.idx(num, 2n, i))), None{}) == None{} : Maybe<&2, String>}
  {==}

# END entries come through
# ========================

def ye_flag(pa: Bool, +e: String, +y: String, +h: {Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{e}) == B.Got{y} : B.Got}) -> {y == e : String}:
  match pa:
    case True{}:
      Empty.absurd({y == e : String}, IK.ref_ne(B.BadCount{}, y, h))
    case False{}:
      Equal.sym(String, e, y, Equal.cong(B.Got, String, z => SI.gtext(z), B.Got{e}, B.Got{y}, h))

# A per-allele END (num) that reads as a number: refused.
def ye_pa(+num: B.Num, +k: String, +e: String, +n: Nat, +i: Nat, +y: String, +d: Nat,
  +ha: {B.Num.per_allele(Some{num}) == True{} : Bool},
  +hk: {k == "END" : String},
  +hp: {B.Pos.read(String.drop(e, 4n)) == Some{d} : Maybe<&2, Nat>},
  +hn: {Nat.is_le(2n, n) == True{} : Bool},
  +h: {B.Got.cat(B.Got{k}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{})) == B.Got{y} : B.Got}) -> Empty:
  +h2 = {(%hk : {B.Got.cat(B.Got{_}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(_), 1n))), B.BadCount{})) == B.Got{y} : B.Got}; h) :
    {B.Got.cat(B.Got{"END"}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, String.drop(e, 4n)), B.BadCount{})) == B.Got{y} : B.Got}}
  +h3 = {(%vs_none(num, n, i, String.drop(e, 4n), d, ha, hn, hp) : {B.Got.cat(B.Got{"END"}, "=", B.Got.of(_, B.BadCount{})) == B.Got{y} : B.Got}; h2) :
    {B.Got.cat(B.Got{"END"}, "=", B.Got.of(None{}, B.BadCount{})) == B.Got{y} : B.Got}}
  IK.ref_ne(B.BadCount{}, y, h3)

def ye_num(x: B.Num, +k: String, +e: String, +n: Nat, +i: Nat, +y: String, +d: Nat,
  +hk: {k == "END" : String},
  +hp: {B.Pos.read(String.drop(e, 4n)) == Some{d} : Maybe<&2, Nat>},
  +hn: {Nat.is_le(2n, n) == True{} : Bool},
  +h: {B.Info.split.eq(Some{x}, k, e, n, i) == B.Got{y} : B.Got}) -> {y == e : String}:
  match x:
    case B.NumA{}:
      Empty.absurd({y == e : String}, ye_pa(B.NumA{}, k, e, n, i, y, d, {==}, hk, hp, hn, h))
    case B.NumR{}:
      Empty.absurd({y == e : String}, ye_pa(B.NumR{}, k, e, n, i, y, d, {==}, hk, hp, hn, h))
    case B.NumG{}:
      Empty.absurd({y == e : String}, ye_pa(B.NumG{}, k, e, n, i, y, d, {==}, hk, hp, hn, h))
    case B.NumOther{}:
      Equal.sym(String, e, y, Equal.cong(B.Got, String, z => SI.gtext(z), B.Got{e}, B.Got{y}, h))
    case B.NumUnknown{}:
      Empty.absurd({y == e : String}, IK.ref_ne(B.UndefinedTag{"INFO/" ++ k}, y, h))

def ye_m(m: Maybe<&2, B.Num>, +k: String, +e: String, +n: Nat, +i: Nat, +y: String, +d: Nat,
  +hk: {k == "END" : String},
  +hp: {B.Pos.read(String.drop(e, 4n)) == Some{d} : Maybe<&2, Nat>},
  +hn: {Nat.is_le(2n, n) == True{} : Bool},
  +h: {B.Info.split.eq(m, k, e, n, i) == B.Got{y} : B.Got}) -> {y == e : String}:
  match m:
    case None{}:
      Empty.absurd({y == e : String}, IK.ref_ne(B.UndefinedTag{"INFO/" ++ k}, y, h))
    case Some{+x}:
      ye_num(x, k, e, n, i, y, d, hk, hp, hn, h)

# An END entry that reads as a number: its result is itself.
def ye(c: Bool, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String, +d: Nat,
  +ec: {String.eq(B.Info.key(e), e) == c : Bool},
  +hk: {B.Info.key(e) == "END" : String},
  +hp: {B.Pos.read(String.drop(e, 4n)) == Some{d} : Maybe<&2, Nat>},
  +hn: {Nat.is_le(2n, n) == True{} : Bool},
  +h: {B.Info.split.num(m, e, n, i) == B.Got{y} : B.Got}) -> {y == e : String}:
  match c:
    case True{}:
      ye_flag(B.Num.per_allele(m), e, y,
        {(%ec : {Bool.pick(B.Got, _, Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, B.Info.key(e), e, n, i)) == B.Got{y} : B.Got}; h) :
          {Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}) == B.Got{y} : B.Got}})
    case False{}:
      ye_m(m, B.Info.key(e), e, n, i, y, d, hk, hp, hn,
        {(%ec : {Bool.pick(B.Got, _, Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, B.Info.key(e), e, n, i)) == B.Got{y} : B.Got}; h) :
          {B.Info.split.eq(m, B.Info.key(e), e, n, i) == B.Got{y} : B.Got}})

def ee.r(mr: Maybe<&2, Nat>, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String, +r: Ms(),
  +er: {B.Pos.read(String.drop(e, 4n)) == mr : Maybe<&2, Nat>},
  +hk: {B.Info.key(e) == "END" : String},
  +hg: {B.Info.split.num(m, e, n, i) == B.Got{y} : B.Got},
  +hs: {Maybe.is_some(&2, Nat, mr) == True{} : Bool},
  +hn: {Nat.is_le(2n, n) == True{} : Bool}) ->
  {B.Info.ends.put(True{}, y, r) == B.Info.ends.put(True{}, e, r) : Ms()}:
  match mr:
    case None{}:
      Empty.absurd({B.Info.ends.put(True{}, y, r) == B.Info.ends.put(True{}, e, r) : Ms()}, AB.false_ne_true(hs))
    case Some{+d}:
      Equal.cong(String, Ms(), z => B.Info.ends.put(True{}, z, r), y, e, ye(String.eq(B.Info.key(e), e), m, e, n, i, y, d, {==}, hk, er, hn, hg))

def ee(b: Bool, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String, +r: Ms(),
  +eb: {String.eq(B.Info.key(e), "END") == b : Bool},
  +hg: {B.Info.split.num(m, e, n, i) == B.Got{y} : B.Got},
  +hs: {Bool.or(Bool.not(b), Maybe.is_some(&2, Nat, B.Pos.read(String.drop(e, 4n)))) == True{} : Bool},
  +hn: {Nat.is_le(2n, n) == True{} : Bool}) ->
  {B.Info.ends.put(b, y, r) == B.Info.ends.put(b, e, r) : Ms()}:
  match b:
    case False{}:
      {==}
    case True{}:
      ee.r(B.Pos.read(String.drop(e, 4n)), m, e, n, i, y, r, {==}, Q.str_eq_sound(B.Info.key(e), "END", eb), hg, hs, hn)

# One entry's result, for the END list: as the entry.
def ent_end(+m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String, +r: Ms(),
  +hg: {B.Info.split.num(m, e, n, i) == B.Got{y} : B.Got},
  +hs: {Bool.or(Bool.not(String.eq(B.Info.key(e), "END")), Maybe.is_some(&2, Nat, B.Pos.read(String.drop(e, 4n)))) == True{} : Bool},
  +hn: {Nat.is_le(2n, n) == True{} : Bool}) ->
  {B.Info.ends.put(String.eq(B.Info.key(y), "END"), y, r) == B.Info.ends.put(String.eq(B.Info.key(e), "END"), e, r) : Ms()}:
  %Equal.sym(String, B.Info.key(y), B.Info.key(e), IK.kn(m, e, n, i, y, hg)) :
    {B.Info.ends.put(String.eq(_, "END"), y, r) == B.Info.ends.put(String.eq(B.Info.key(e), "END"), e, r) : Ms()}
  ee(String.eq(B.Info.key(e), "END"), m, e, n, i, y, r, {==}, hg, hs, hn)

# No END entry fails to read as a number.
def NN(ms: Ms()) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Maybe.is_some(&2, Nat, m) && NN(t)

def nn_l(b: Bool, +e: String, +r: Ms(), +h: {NN(B.Info.ends.put(b, e, r)) == True{} : Bool}) ->
  {Bool.or(Bool.not(b), Maybe.is_some(&2, Nat, B.Pos.read(String.drop(e, 4n)))) == True{} : Bool}:
  match b:
    case True{}:
      P.and_true_l(Maybe.is_some(&2, Nat, B.Pos.read(String.drop(e, 4n))), NN(r), h)
    case False{}:
      {==}

def nn_r(b: Bool, +e: String, +r: Ms(), +h: {NN(B.Info.ends.put(b, e, r)) == True{} : Bool}) -> {NN(r) == True{} : Bool}:
  match b:
    case True{}:
      P.and_true_r(Maybe.is_some(&2, Nat, B.Pos.read(String.drop(e, 4n))), NN(r), h)
    case False{}:
      h

def put_l(m: Maybe<&2, B.Code>, +r: Maybe<&2, B.Code>, +h: {L.first_code.put(m, r) == None{} : Maybe<&2, B.Code>}) -> {m == None{} : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      h

def put_r(m: Maybe<&2, B.Code>, +r: Maybe<&2, B.Code>, +h: {L.first_code.put(m, r) == None{} : Maybe<&2, B.Code>}) -> {r == None{} : Maybe<&2, B.Code>}:
  match m:
    case None{}:
      h
    case Some{+c}:
      Empty.absurd({r == None{} : Maybe<&2, B.Code>}, AB.false_ne_true(Equal.cong(Maybe<&2, B.Code>, Bool, z => Maybe.is_none(&2, B.Code, z), Some{c}, None{}, h)))

def gc_got(g: B.Got, +h: {W.GC(g) == None{} : Maybe<&2, B.Code>}) -> {g == B.Got{SI.gtext(g)} : B.Got}:
  match g:
    case B.Got{+x}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{SI.gtext(B.Refuse{c})} : B.Got}, AB.false_ne_true(Equal.cong(Maybe<&2, B.Code>, Bool, z => Maybe.is_none(&2, B.Code, z), Some{c}, None{}, h)))

law ends_tx:
  for +es: Ss()
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +hfr: {W.FR(IE.IGO(es, tags, n, i)) == None{} : Maybe<&2, B.Code>}
  for +hnn: {NN(B.Info.ends.go(es)) == True{} : Bool}
  for +hn: {Nat.is_le(2n, n) == True{} : Bool}
  {B.Info.ends.go(SM.TX(IE.IGO(es, tags, n, i))) == B.Info.ends.go(es) : Ms()}

def ends_tx(es, tags, n, i, hfr, hnn, hn):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +m = B.Tags.find(tags, B.Info.key(e))
      +g = B.Info.split.num(m, e, n, i)
      +R0 = W.FR(IE.IGO(t, tags, n, i))
      +isE = String.eq(B.Info.key(e), "END")
      +hg = gc_got(g, put_l(W.GC(g), R0, hfr))
      +ih = ends_tx(t, tags, n, i, put_r(W.GC(g), R0, hfr), nn_r(isE, e, B.Info.ends.go(t), hnn), hn)
      Equal.trans(Ms(), B.Info.ends.put(String.eq(B.Info.key(SI.gtext(g)), "END"), SI.gtext(g), B.Info.ends.go(SM.TX(IE.IGO(t, tags, n, i)))),
        B.Info.ends.put(String.eq(B.Info.key(SI.gtext(g)), "END"), SI.gtext(g), B.Info.ends.go(t)),
        B.Info.ends.put(isE, e, B.Info.ends.go(t)),
        Equal.cong(Ms(), Ms(), z => B.Info.ends.put(String.eq(B.Info.key(SI.gtext(g)), "END"), SI.gtext(g), z), B.Info.ends.go(SM.TX(IE.IGO(t, tags, n, i))), B.Info.ends.go(t), ih),
        ent_end(m, e, n, i, SI.gtext(g), B.Info.ends.go(t), hg, nn_l(isE, e, B.Info.ends.go(t), hnn), hn))

def nn_ok.k(m: Maybe<&2, Nat>, t: Ms(), +x: Nat, +h: {B.Info.end_ok.go(Con{m, t}, x) == True{} : Bool}) -> {NN(Con{m, t}) == True{} : Bool}:
  match m t:
    case Some{+v} Nil{}:
      {==}
    case Some{+v} Con{+m2, +t2}:
      Empty.absurd({NN(Con{Some{v}, Con{m2, t2}}) == True{} : Bool}, AB.false_ne_true(h))
    case None{} _:
      Empty.absurd({NN(Con{None{}, t}) == True{} : Bool}, AB.false_ne_true(h))

# END is fine: then no END entry fails to read.
def nn_ok(ms: Ms(), +x: Nat, +h: {B.Info.end_ok.go(ms, x) == True{} : Bool}) -> {NN(ms) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      nn_ok.k(m, t, x, h)


# Lists
# =====

def none_some(+y: String, +h: {None{} == Some{y} : Maybe<&2, String>}) -> Empty:
  AB.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, z => Maybe.is_some(&2, String, z), None{}, Some{y}, h))

def tl(xs: Ss()) -> Ss():
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      t

def is_con(xs: Ss()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      True{}

def drop0(xs: Ss()) -> {List.drop(&2, String, xs, 0n) == xs : Ss()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

law dg:
  for +ps: Ss()
  for +j: Nat
  for +p: String
  for +t: Ss()
  for +h: {List.drop(&2, String, ps, j) == Con{p, t} : Ss()}
  {List.get(&2, String, ps, j) == Some{p} : Maybe<&2, String>}

def dg(ps, j, p, t, h):
  match ps j:
    case Nil{} _:
      Empty.absurd({List.get(&2, String, Nil{}, j) == Some{p} : Maybe<&2, String>}, AB.false_ne_true(Equal.cong(Ss(), Bool, z => is_con(z), Nil{}, Con{p, t}, h)))
    case Con{+q, +r} 0n:
      Equal.cong(Ss(), Maybe<&2, String>, z => List.get(&2, String, z, 0n), Con{q, r}, Con{p, t}, h)
    case Con{+q, +r} 1n+(+k):
      dg(r, k, p, t, h)

law ds:
  for +ps: Ss()
  for +j: Nat
  for +p: String
  for +t: Ss()
  for +h: {List.drop(&2, String, ps, j) == Con{p, t} : Ss()}
  {List.drop(&2, String, ps, 1n+j) == t : Ss()}

def ds(ps, j, p, t, h):
  match ps j:
    case Nil{} _:
      Empty.absurd({List.drop(&2, String, Nil{}, 1n+j) == t : Ss()}, AB.false_ne_true(Equal.cong(Ss(), Bool, z => is_con(z), Nil{}, Con{p, t}, h)))
    case Con{+q, +r} 0n:
      Equal.trans(Ss(), List.drop(&2, String, r, 0n), r, t, drop0(r), Equal.cong(Ss(), Ss(), z => tl(z), Con{q, r}, Con{p, t}, h))
    case Con{+q, +r} 1n+(+k):
      ds(r, k, p, t, h)

law ae_get:
  for +xs: Ss()
  for +i: Nat
  for +a: String
  for +h: {B.Text.any_empty(xs) == False{} : Bool}
  for +hg: {List.get(&2, String, xs, i) == Some{a} : Maybe<&2, String>}
  {String.is_empty(a) == False{} : Bool}

def ae_get(xs, i, a, h, hg):
  match xs i:
    case Nil{} _:
      Empty.absurd({String.is_empty(a) == False{} : Bool}, none_some(a, hg))
    case Con{+q, +t} 0n:
      {(%SC.some_inj(q, a, hg) : {String.is_empty(_) == False{} : Bool}; P.or_false_inv(String.is_empty(q), B.Text.any_empty(t), h)) : {String.is_empty(a) == False{} : Bool}}
    case Con{+q, +t} 1n+(+k):
      ae_get(t, k, a, C.or_inv_r(String.is_empty(q), B.Text.any_empty(t), h), hg)

law anl_get:
  for +xs: Ss()
  for +i: Nat
  for +a: String
  for +h: {B.Text.any_not_letters(xs) == False{} : Bool}
  for +hg: {List.get(&2, String, xs, i) == Some{a} : Maybe<&2, String>}
  {Bool.not(B.Text.is_letters(a)) == False{} : Bool}

def anl_get(xs, i, a, h, hg):
  match xs i:
    case Nil{} _:
      Empty.absurd({Bool.not(B.Text.is_letters(a)) == False{} : Bool}, none_some(a, hg))
    case Con{+q, +t} 0n:
      {(%SC.some_inj(q, a, hg) : {Bool.not(B.Text.is_letters(_)) == False{} : Bool}; P.or_false_inv(Bool.not(B.Text.is_letters(q)), B.Text.any_not_letters(t), h)) : {Bool.not(B.Text.is_letters(a)) == False{} : Bool}}
    case Con{+q, +t} 1n+(+k):
      anl_get(t, k, a, C.or_inv_r(Bool.not(B.Text.is_letters(q)), B.Text.any_not_letters(t), h), hg)

def RDT(+b: String, +t: Ss(), +xs: List<&2, List<&2, B.Base>>) -> Type:
  {B.Allele.read(b) == Some{V.hdx(xs)} : Maybe<&2, List<&2, B.Base>>} & ({B.Alleles.read(t) == Some{V.tlx(xs)} : Maybe<&2, List<&2, List<&2, B.Base>>>} & {xs == Con{V.hdx(xs), V.tlx(xs)} : List<&2, List<&2, B.Base>>})

def rs0(+b: String, +t: Ss(), +a: String, +xs: List<&2, List<&2, B.Base>>, +hg: {Some{b} == Some{a} : Maybe<&2, String>}, r: RDT(b, t, xs)) ->
  {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}:
  match r:
    case (ea, q):
      {(%SC.some_inj(b, a, hg) : {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(_)) == True{} : Bool};
        %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(b), Some{V.hdx(xs)}, ea) : {Maybe.is_some(&2, List<&2, B.Base>, _) == True{} : Bool}; {==}) : {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}}

def rs1(+b: String, +t: Ss(), +a: String, +xs: List<&2, List<&2, B.Base>>, r: RDT(b, t, xs),
  k: {B.Alleles.read(t) == Some{V.tlx(xs)} : Maybe<&2, List<&2, List<&2, B.Base>>>} -> {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}) ->
  {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}:
  match r:
    case (ea, q):
      match q:
        case (et, ex):
          k(et)

# An ALT of a line whose ALTs read: it reads.
law rd_some:
  for +alts: Ss()
  for +i: Nat
  for +xs: List<&2, List<&2, B.Base>>
  for +a: String
  for +ha: {B.Alleles.read(alts) == Some{xs} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  for +hg: {List.get(&2, String, alts, i) == Some{a} : Maybe<&2, String>}
  {Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}

def rd_some(alts, i, xs, a, ha, hg):
  match alts i:
    case Nil{} _:
      Empty.absurd({Maybe.is_some(&2, List<&2, B.Base>, B.Allele.read(a)) == True{} : Bool}, none_some(a, hg))
    case Con{+b, +t} 0n:
      rs0(b, t, a, xs, hg, V.rd_k(B.Allele.read(b), B.Alleles.read(t), xs, ha))
    case Con{+b, +t} 1n+(+j):
      rs1(b, t, a, xs, V.rd_k(B.Allele.read(b), B.Alleles.read(t), xs, ha), et => rd_some(t, j, V.tlx(xs), a, et, hg))

def allv_get.k(+seq: List<&2, B.Base>, +pos: Nat, +ref: List<&2, B.Base>, +y: List<&2, B.Base>, +t: List<&2, List<&2, B.Base>>, +x: List<&2, B.Base>,
  hall: V.ALLV(seq, pos, ref, Con{y, t}), j: Nat, +hx: {List.get(&2, List<&2, B.Base>, Con{y, t}, j) == Some{x} : Maybe<&2, List<&2, B.Base>>},
  k: V.ALLV(seq, pos, ref, t) -> @j2: Nat -> {List.get(&2, List<&2, B.Base>, t, j2) == Some{x} : Maybe<&2, List<&2, B.Base>>} -> {V.VAL(seq, pos, ref, [x]) == True{} : Bool}) ->
  {V.VAL(seq, pos, ref, [x]) == True{} : Bool}:
  match hall:
    case (vh, vt):
      match j:
        case 0n:
          {(%SC.some_injb(y, x, hx) : {V.VAL(seq, pos, ref, [_]) == True{} : Bool}; vh) : {V.VAL(seq, pos, ref, [x]) == True{} : Bool}}
        case 1n+(+m):
          k(vt, m, hx)

law allv_get:
  for +xs: List<&2, List<&2, B.Base>>
  for +seq: List<&2, B.Base>
  for +pos: Nat
  for +ref: List<&2, B.Base>
  for +x: List<&2, B.Base>
  for hall: V.ALLV(seq, pos, ref, xs)
  for +j: Nat
  for +hx: {List.get(&2, List<&2, B.Base>, xs, j) == Some{x} : Maybe<&2, List<&2, B.Base>>}
  {V.VAL(seq, pos, ref, [x]) == True{} : Bool}

def allv_get(xs, seq, pos, ref, x, hall, j, hx):
  match xs:
    case Nil{}:
      Empty.absurd({V.VAL(seq, pos, ref, [x]) == True{} : Bool}, AB.false_ne_true(Equal.cong(Maybe<&2, List<&2, B.Base>>, Bool, z => Maybe.is_some(&2, List<&2, B.Base>, z), None{}, Some{x}, hx)))
    case Con{+y, +t}:
      allv_get.k(seq, pos, ref, y, t, x, hall, j, hx, vt => j2 => h2 => allv_get(t, seq, pos, ref, x, vt, j2, h2))

# A record's INFO keeps END fine
# ==============================

def eg_k(+fa: List<&2, B.Contig>, +defs: B.Defs, +body: String, +i: Nat, +p: String,
  +hok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool},
  +hn2: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool},
  r: {B.Info.split(B.Rec.field(B.Rec.fields(body), 7n), B.Defs.info(defs), L.n_alts(body), 1n+i) == B.Got{SI.gtext(B.Info.split(B.Rec.field(B.Rec.fields(body), 7n), B.Defs.info(defs), L.n_alts(body), 1n+i))} : B.Got}
    & {L.info_entries(p) == SM.TX(IE.IGO(String.split(B.Rec.field(B.Rec.fields(body), 7n), ';'), B.Defs.info(defs), L.n_alts(body), 1n+i)) : Ss()}) ->
  {B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool}:
  match r:
    case (eI, eie):
      +f7 = B.Rec.field(B.Rec.fields(body), 7n)
      +tags = B.Defs.info(defs)
      +n = L.n_alts(body)
      +es = String.split(f7, ';')
      +G = IE.IGO(es, tags, n, 1n+i)
      +hfr = Equal.trans(Maybe<&2, B.Code>, W.FR(G), W.GC(B.Info.split(f7, tags, n, 1n+i)), None{},
        Equal.sym(Maybe<&2, B.Code>, W.GC(B.Got.join(G, ";")), W.FR(G), W.join_gc(G, ";")),
        Equal.cong(B.Got, Maybe<&2, B.Code>, z => W.GC(z), B.Info.split(f7, tags, n, 1n+i), B.Got{SI.gtext(B.Info.split(f7, tags, n, 1n+i))}, eI))
      +et = ends_tx(es, tags, n, 1n+i, hfr, nn_ok(B.Info.ends(f7), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n), hok), hn2)
      %Equal.sym(Ss(), L.info_entries(p), SM.TX(G), eie) : {B.Info.end_ok.go(B.Info.ends.go(_), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool}
      %Equal.sym(Ms(), B.Info.ends.go(SM.TX(G)), B.Info.ends.go(es), et) : {B.Info.end_ok.go(_, Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool}
      hok

def eg_at(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +i: Nat, +p: String,
  +hok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool},
  +hn2: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool},
  r: AT.AT(defs, R.Opts.over0(o), body, i, p)) -> {B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool}:
  match r:
    case (+a2, q):
      match q:
        case (ha2, hg2):
          eg_k(fa, defs, body, i, p, hok, hn2,
            IE.ie_fs(AT.FS(body), defs, R.Opts.over0(o), L.n_alts(body), 1n+i, a2, p, hg2, AT.fs_tab(body), AT.alt_tab(body, i, a2, ha2), AT.parts_l8(defs, o, body, ps, h)))

# A record: normalized
# ====================

def rn.x(mx: Maybe<&2, List<&2, B.Base>>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +raw: String, +ref: List<&2, B.Base>, +xs: List<&2, List<&2, B.Base>>,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(B.Rec.fields(body))) == Some{xs} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +hok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool},
  +hvv: {L.valid(B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs}) == True{} : Bool},
  +hn2: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool},
  +i: Nat, +p: String, +a: String,
  +hmx: {B.Allele.read(a) == mx : Maybe<&2, List<&2, B.Base>>},
  +hgx: {List.get(&2, List<&2, B.Base>, xs, i) == mx : Maybe<&2, List<&2, B.Base>>},
  +hsome: {Maybe.is_some(&2, List<&2, B.Base>, mx) == True{} : Bool},
  +ea4: {B.Rec.field(B.Rec.fields(p), 4n) == a : String},
  +hca: {ST.noc(a, ',') == True{} : Bool},
  +e0: {B.Rec.field(B.Rec.fields(body), 0n) == B.Rec.field(B.Rec.fields(p), 0n) : String},
  +e1: {B.Rec.field(B.Rec.fields(body), 1n) == B.Rec.field(B.Rec.fields(p), 1n) : String},
  +e3: {B.Rec.field(B.Rec.fields(body), 3n) == B.Rec.field(B.Rec.fields(p), 3n) : String},
  +malg: {B.Rec.malformed(B.Rec.fields(p)) == False{} : Bool},
  +oosg: {B.Rec.out_of_scope(B.Rec.fields(p)) == False{} : Bool},
  +eokg: {B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool}) ->
  {L.is_normalized(L.judge(fa, p)) == True{} : Bool}:
  match mx:
    case None{}:
      Empty.absurd({L.is_normalized(L.judge(fa, p)) == True{} : Bool}, AB.false_ne_true(hsome))
    case Some{+x}:
      +GA = B.Alleles.read(B.Rec.alts(B.Rec.fields(p)))
      +hval = allv_get(xs, B.Bases.of_fasta(raw), B.Rec.pos(B.Rec.fields(body)), ref, x, V.valid_each(B.Bases.of_fasta(raw), B.Rec.pos(B.Rec.fields(body)), ref, xs, hvv), i, hgx)
      %Equal.sym(Bool, B.Rec.malformed(B.Rec.fields(p)), False{}, malg) : {L.is_normalized(L.judge.shape(_, B.Rec.out_of_scope(B.Rec.fields(p)), fa, B.Rec.fields(p), p)) == True{} : Bool}
      %Equal.sym(Bool, B.Rec.out_of_scope(B.Rec.fields(p)), False{}, oosg) : {L.is_normalized(L.judge.shape(False{}, _, fa, B.Rec.fields(p), p)) == True{} : Bool}
      %e0 : {L.is_normalized(L.judge.contig(B.Fasta.find(fa, _), B.Rec.fields(p), p)) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)), Some{raw}, ef) : {L.is_normalized(L.judge.contig(_, B.Rec.fields(p), p)) == True{} : Bool}
      %e3 : {L.is_normalized(L.judge.bases(B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(p)), String.length(_)), 1n)), B.Allele.read(_), GA, B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %e1 : {L.is_normalized(L.judge.bases(B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(_), 0n), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)), B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)), GA, B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %Equal.sym(Bool, B.Info.end_ok(B.Rec.field(B.Rec.fields(p), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)), True{}, eokg) : {L.is_normalized(L.judge.bases(_, B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)), GA, B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)), Some{ref}, er) : {L.is_normalized(L.judge.bases(True{}, _, GA, B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %Equal.sym(String, B.Rec.field(B.Rec.fields(p), 4n), a, ea4) : {L.is_normalized(L.judge.bases(True{}, Some{ref}, B.Alleles.read(String.split(_, ',')), B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hca)) : {L.is_normalized(L.judge.bases(True{}, Some{ref}, B.Alleles.read(_), B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(a), Some{x}, hmx) : {L.is_normalized(L.judge.bases(True{}, Some{ref}, B.Alleles.read.cons(_, Some{Nil{}}), B.Rec.fields(p), p, B.Bases.of_fasta(raw))) == True{} : Bool}
      %e1 : {L.is_normalized(L.problem(L.checks(True{}, B.Bases.of_fasta(raw), B.Var{Maybe.default(&2, Nat, B.Pos.read(_), 0n), ref, [x]}), B.Rec.fields(p), p, B.Bases.of_fasta(raw), B.Var{Maybe.default(&2, Nat, B.Pos.read(_), 0n), ref, [x]})) == True{} : Bool}
      %Equal.sym(Maybe<&2, B.Code>, L.checks(True{}, B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, [x]}), None{}, C.checks_valid(B.Bases.of_fasta(raw), B.Rec.pos(B.Rec.fields(body)), ref, [x], hval)) :
        {L.is_normalized(L.problem(_, B.Rec.fields(p), p, B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, [x]})) == True{} : Bool}
      {==}

def PNT(+fa: List<&2, B.Contig>, +p: String) -> Type:
  {L.is_normalized(L.judge(fa, p)) == True{} : Bool}

# The record at place i: normalized.
def pn_at(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +raw: String, +ref: List<&2, B.Base>, +xs: List<&2, List<&2, B.Base>>,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(B.Rec.fields(body))) == Some{xs} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +hok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool},
  +hvv: {L.valid(B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs}) == True{} : Bool},
  +hn2: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}, +i: Nat, +p: String,
  +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}) -> PNT(fa, p):
  +fs = B.Rec.fields(body)
  +gs = B.Rec.fields(p)
  +ss = SC.ss_get(ps, i, fs, p, SM.split_site(defs, o, body, ps, h), hp)
  +sf = P.and_true_r(Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)), L.same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n]), ss)
  +elen = P.eq_sound(List.length(&2, String, fs), List.length(&2, String, gs), P.and_true_l(Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)), L.same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n]), ss))
  +s0 = String.eq(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n))
  +s1 = String.eq(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n))
  +s2 = String.eq(B.Rec.field(fs, 2n), B.Rec.field(gs, 2n))
  +s3 = String.eq(B.Rec.field(fs, 3n), B.Rec.field(gs, 3n))
  +r0 = L.same_fields(fs, gs, [1n, 2n, 3n, 5n, 6n, 8n])
  +r1 = L.same_fields(fs, gs, [2n, 3n, 5n, 6n, 8n])
  +r2 = L.same_fields(fs, gs, [3n, 5n, 6n, 8n])
  +r3 = L.same_fields(fs, gs, [5n, 6n, 8n])
  +e0 = Q.str_eq_sound(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n), P.and_true_l(s0, r0, sf))
  +sf1 = P.and_true_r(s0, r0, sf)
  +e1 = Q.str_eq_sound(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n), P.and_true_l(s1, r1, sf1))
  +sf2 = P.and_true_r(s1, r1, sf1)
  +sf3 = P.and_true_r(s2, r2, sf2)
  +e3 = Q.str_eq_sound(B.Rec.field(fs, 3n), B.Rec.field(gs, 3n), P.and_true_l(s3, r3, sf3))
  +a = B.Rec.field(gs, 4n)
  +ga = Equal.trans(Maybe<&2, String>, List.get(&2, String, B.Rec.alts(fs), i), List.get(&2, String, L.alt_fields(ps), i), Some{a},
    Equal.sym(Maybe<&2, String>, List.get(&2, String, L.alt_fields(ps), i), List.get(&2, String, B.Rec.alts(fs), i),
      Equal.cong(Ss(), Maybe<&2, String>, z => List.get(&2, String, z, i), L.alt_fields(ps), B.Rec.alts(fs), SI.split_alts(defs, o, body, ps, h))),
    SC.get_af(ps, i, p, hp))
  +hca = SC.noc_get(B.Rec.alts(fs), i, a, ',', ST.split_all(B.Rec.field(fs, 4n), ','), ga)
  +lt = Nat.is_lt(List.length(&2, String, fs), 8n)
  +z0 = String.is_empty(B.Rec.field(fs, 0n))
  +n1 = Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))
  +l3 = Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n)))
  +or4 = Bool.or(Bool.or(Bool.or(lt, z0), n1), l3)
  +m5f = C.or_inv_r(or4, B.Text.any_empty(B.Rec.alts(fs)), em)
  +m1to4 = P.or_false_inv(or4, B.Text.any_empty(B.Rec.alts(fs)), em)
  +m4f = C.or_inv_r(Bool.or(Bool.or(lt, z0), n1), l3, m1to4)
  +m123 = P.or_false_inv(Bool.or(Bool.or(lt, z0), n1), l3, m1to4)
  +m3f = C.or_inv_r(Bool.or(lt, z0), n1, m123)
  +m12 = P.or_false_inv(Bool.or(lt, z0), n1, m123)
  +m2f = C.or_inv_r(lt, z0, m12)
  +m1f = P.or_false_inv(lt, z0, m12)
  +m1g = {(%elen : {Nat.is_lt(_, 8n) == False{} : Bool}; m1f) : {Nat.is_lt(List.length(&2, String, gs), 8n) == False{} : Bool}}
  +m2g = {(%e0 : {String.is_empty(_) == False{} : Bool}; m2f) : {String.is_empty(B.Rec.field(gs, 0n)) == False{} : Bool}}
  +m3g = {(%e1 : {Maybe.is_none(&2, Nat, B.Pos.read(_)) == False{} : Bool}; m3f) : {Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(gs, 1n))) == False{} : Bool}}
  +m4g = {(%e3 : {Bool.not(B.Text.is_letters(_)) == False{} : Bool}; m4f) : {Bool.not(B.Text.is_letters(B.Rec.field(gs, 3n))) == False{} : Bool}}
  +hae = ae_get(B.Rec.alts(fs), i, a, m5f, ga)
  +m5g = {(%Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hca)) : {B.Text.any_empty(_) == False{} : Bool};
    {(%Equal.sym(Bool, String.is_empty(a), False{}, hae) : {Bool.or(_, False{}) == False{} : Bool}; {==}) : {Bool.or(String.is_empty(a), False{}) == False{} : Bool}}) :
    {B.Text.any_empty(B.Rec.alts(gs)) == False{} : Bool}}
  +malg = J.or5(Nat.is_lt(List.length(&2, String, gs), 8n), String.is_empty(B.Rec.field(gs, 0n)), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(gs, 1n))),
    Bool.not(B.Text.is_letters(B.Rec.field(gs, 3n))), B.Text.any_empty(B.Rec.alts(gs)), m1g, m2g, m3g, m4g, m5g)
  +hanl = anl_get(B.Rec.alts(fs), i, a, eo, ga)
  +oosg = {(%Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hca)) : {B.Text.any_not_letters(_) == False{} : Bool};
    {(%Equal.sym(Bool, Bool.not(B.Text.is_letters(a)), False{}, hanl) : {Bool.or(_, False{}) == False{} : Bool}; {==}) : {Bool.or(Bool.not(B.Text.is_letters(a)), False{}) == False{} : Bool}}) :
    {B.Rec.out_of_scope(gs) == False{} : Bool}}
  +eokg = eg_at(fa, defs, o, body, ps, h, i, p, hok, hn2, AT.piece_at(defs, o, body, ps, h, i, p, hp))
  rn.x(B.Allele.read(a), fa, defs, o, body, ps, h, raw, ref, xs, em, eo, ef, er, ea, hok, hvv, hn2, i, p, a, {==},
    Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(a), List.get(&2, List<&2, B.Base>, xs, i), SC.rd_get(B.Rec.alts(fs), i, xs, a, ea, ga)),
    rd_some(B.Rec.alts(fs), i, xs, a, ea, ga), {==}, hca, e0, e1, e3, malg, oosg, eokg)

def and_tt(a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

def an_go(qs: Ss(), +j: Nat, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +raw: String, +ref: List<&2, B.Base>, +xs: List<&2, List<&2, B.Base>>,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(B.Rec.fields(body))) == Some{xs} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +hok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == True{} : Bool},
  +hvv: {L.valid(B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs}) == True{} : Bool},
  +hn2: {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool},
  +hd: {List.drop(&2, String, ps, j) == qs : Ss()}) -> {L.all_normalized(fa, qs) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      and_tt(L.is_normalized(L.judge(fa, p)), L.all_normalized(fa, t),
        pn_at(fa, defs, o, body, ps, h, raw, ref, xs, em, eo, ef, er, ea, hok, hvv, hn2, j, p, dg(ps, j, p, t, hd)),
        an_go(t, 1n+j, fa, defs, o, body, ps, h, raw, ref, xs, em, eo, ef, er, ea, hok, hvv, hn2, ds(ps, j, p, t, hd)))

def is_pcs(pt: B.Parts) -> Bool:
  match pt:
    case B.Pieces{x}:
      True{}
    case _:
      False{}

def pn2(sp: Bool, m: Bool, b: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +eb: {Nat.is_le(2n, L.n_alts(body)) == b : Bool},
  +h: {B.Rec.parts.if(sp && Bool.not(m) && b, B.Text.has_cr(body), defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}:
  match sp m b:
    case True{} False{} True{}:
      eb
    case False{} _ _:
      Empty.absurd({Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, z => is_pcs(z), B.Whole{}, B.Pieces{ps}, h)))
    case True{} True{} _:
      Empty.absurd({Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, z => is_pcs(z), B.Whole{}, B.Pieces{ps}, h)))
    case True{} False{} False{}:
      Empty.absurd({Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, z => is_pcs(z), B.Whole{}, B.Pieces{ps}, h)))

# A split line has two ALTs or more.
def pieces_n2(+defs: B.Defs, o: B.Opts, +body: String, +ps: Ss(), +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}) ->
  {Nat.is_le(2n, L.n_alts(body)) == True{} : Bool}:
  match o:
    case B.Opts{+s, +w, +sp, +o0, +a}:
      pn2(sp, B.Rec.malformed(B.Rec.fields(body)), Nat.is_le(2n, L.n_alts(body)), defs, o0, body, ps, {==}, h)

# The line's outcome, case by case: only a normalized line gets here.
def sn.problem(c: Maybe<&2, B.Code>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +raw: String, +ref: List<&2, B.Base>, +xs: List<&2, List<&2, B.Base>>, +eok: Bool,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(B.Rec.fields(body))) == Some{xs} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +heok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == eok : Bool},
  +ec: {L.checks(eok, B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs}) == c : Maybe<&2, B.Code>},
  +hn: {L.is_normalized(L.problem(c, B.Rec.fields(body), body, B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs})) == True{} : Bool}) ->
  {L.all_normalized(fa, ps) == True{} : Bool}:
  match c:
    case Some{+k}:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))
    case None{}:
      +seq = B.Bases.of_fasta(raw)
      +pp = B.Rec.pos(B.Rec.fields(body))
      +R3 = L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(pp, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{})
      +R2 = L.first(Bool.not(B.Alleles.distinct(ref <> xs)), B.AltDup{}, R3)
      +R1 = L.first(Nat.is_eq(pp, 0n), B.BadPos{}, R2)
      +hok = Equal.trans(Bool, B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)), eok, True{}, heok, P.not_false(eok, NL.first_b(Bool.not(eok), B.BadEnd{}, R1, ec)))
      +hvv = NL.nz_valid(B.Rec.fields(body), seq, ref, xs, eok, em, er, ea, ec)
      an_go(ps, 0n, fa, defs, o, body, ps, h, raw, ref, xs, em, eo, ef, er, ea, hok, hvv, pieces_n2(defs, o, body, ps, h), drop0(ps))

def sn.bases(+eok: Bool, r: Maybe<&2, List<&2, B.Base>>, am: Maybe<&2, List<&2, List<&2, B.Base>>>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}, +raw: String,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +heok: {B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)) == eok : Bool},
  +er: {B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)) == r : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(B.Rec.fields(body))) == am : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +hn: {L.is_normalized(L.judge.bases(eok, r, am, B.Rec.fields(body), body, B.Bases.of_fasta(raw))) == True{} : Bool}) ->
  {L.all_normalized(fa, ps) == True{} : Bool}:
  match r am:
    case Some{+ref} Some{+xs}:
      sn.problem(L.checks(eok, B.Bases.of_fasta(raw), B.Var{B.Rec.pos(B.Rec.fields(body)), ref, xs}), fa, defs, o, body, ps, h, raw, ref, xs, eok, em, eo, ef, er, ea, heok, {==}, hn)
    case None{} _:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))
    case Some{+ref} None{}:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))

def sn.contig(m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts},
  +em: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == m : Maybe<&2, String>},
  +hn: {L.is_normalized(L.judge.contig(m, B.Rec.fields(body), body)) == True{} : Bool}) ->
  {L.all_normalized(fa, ps) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))
    case Some{+raw}:
      sn.bases(B.Info.end_ok(B.Rec.field(B.Rec.fields(body), 7n), Nat.sub(Nat.add(B.Rec.pos(B.Rec.fields(body)), String.length(B.Rec.field(B.Rec.fields(body), 3n))), 1n)), B.Allele.read(B.Rec.field(B.Rec.fields(body), 3n)), B.Alleles.read(B.Rec.alts(B.Rec.fields(body))), fa, defs, o, body, ps, h, raw, em, eo, ef, {==}, {==}, {==}, hn)

def sn.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts},
  +em: {B.Rec.malformed(B.Rec.fields(body)) == bad : Bool},
  +eo: {B.Rec.out_of_scope(B.Rec.fields(body)) == skip : Bool},
  +hn: {L.is_normalized(L.judge.shape(bad, skip, fa, B.Rec.fields(body), body)) == True{} : Bool}) ->
  {L.all_normalized(fa, ps) == True{} : Bool}:
  match bad skip:
    case True{} _:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))
    case False{} True{}:
      Empty.absurd({L.all_normalized(fa, ps) == True{} : Bool}, AB.false_ne_true(hn))
    case False{} False{}:
      sn.contig(B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)), fa, defs, o, body, ps, h, em, eo, {==}, hn)

law split_normalized_p:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +hn: {L.is_normalized(L.judge(fa, body)) == True{} : Bool}
  {L.all_normalized(fa, ps) == True{} : Bool}

def split_normalized_p(fa, defs, o, body, ps, h, hn):
  sn.shape(B.Rec.malformed(B.Rec.fields(body)), B.Rec.out_of_scope(B.Rec.fields(body)), fa, defs, o, body, ps, h, {==}, {==}, hn)
