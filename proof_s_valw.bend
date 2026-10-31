import Base
import ./types.bend as B
import ./proof_s_chars.bend as CH
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# INFO entries (and FORMAT values) of a record keep a character class that admits ',', '=' and
# '.' (proof_s_chars.bend's INFO lemmas, without asking for ';' and ':'): so
# an entry of a record holds no ';' when the line's INFO holds none. Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def vsplitW.if(+p: CH.Cls, +miss: Bool, +num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +v: String,
  +h: {CH.ALLC(p, v) == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.MOK(p, B.Vals.split.if(miss, num, n, cp, i, v)) == True{} : Bool}:
  match miss:
    case True{}:
      hd
    case False{}:
      +vs = String.split(v, ',')
      CH.vkeep(p, num, n, B.Vals.copies(cp, n, List.length(&2, String, vs)), i, vs, CH.split_all(p, v, ',', h), hc)

def vsplitW(+p: CH.Cls, +num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +v: String,
  +h: {CH.ALLC(p, v) == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.MOK(p, B.Vals.split(num, n, cp, i, v)) == True{} : Bool}:
  vsplitW.if(p, String.eq(v, "."), num, n, cp, i, v, h, hc, hd)

def ieqW.v(+p: CH.Cls, +num: B.Num, +k: String, +e: String, +n: Nat, +i: Nat,
  +hk: {CH.ALLC(p, k) == True{} : Bool}, +he: {CH.ALLC(p, e) == True{} : Bool},
  +hq: {CH.ALLC(p, "=") == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.GOK(p, B.Got.cat(B.Got{k}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}))) == True{} : Bool}:
  CH.got_cat(p, B.Got{k}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{}), hk, hq,
    CH.got_of(p, B.Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), B.BadCount{},
      vsplitW(p, num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n)), CH.allc_drop(p, e, Nat.add(String.length(k), 1n), he), hc, hd)))

def ieqW.num(+p: CH.Cls, +num: B.Num, +k: String, +e: String, +n: Nat, +i: Nat,
  +hk: {CH.ALLC(p, k) == True{} : Bool}, +he: {CH.ALLC(p, e) == True{} : Bool},
  +hq: {CH.ALLC(p, "=") == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.GOK(p, B.Info.split.eq(Some{num}, k, e, n, i)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      he
    case B.NumA{}:
      ieqW.v(p, B.NumA{}, k, e, n, i, hk, he, hq, hc, hd)
    case B.NumR{}:
      ieqW.v(p, B.NumR{}, k, e, n, i, hk, he, hq, hc, hd)
    case B.NumG{}:
      ieqW.v(p, B.NumG{}, k, e, n, i, hk, he, hq, hc, hd)

def ieqW(+p: CH.Cls, +m: Maybe<&2, B.Num>, +k: String, +e: String, +n: Nat, +i: Nat,
  +hk: {CH.ALLC(p, k) == True{} : Bool}, +he: {CH.ALLC(p, e) == True{} : Bool},
  +hq: {CH.ALLC(p, "=") == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.GOK(p, B.Info.split.eq(m, k, e, n, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      ieqW.num(p, num, k, e, n, i, hk, he, hq, hc, hd)

def inumW(+p: CH.Cls, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +he: {CH.ALLC(p, e) == True{} : Bool},
  +hq: {CH.ALLC(p, "=") == True{} : Bool}, +hc: {CH.ALLC(p, ",") == True{} : Bool}, +hd: {CH.ALLC(p, ".") == True{} : Bool}) ->
  {CH.GOK(p, B.Info.split.num(m, e, n, i)) == True{} : Bool}:
  +k = B.Info.key(e)
  CH.pick_got(p, String.eq(k, e), Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, k, e, n, i),
    CH.pick_got(p, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}, {==}, he),
    ieqW(p, m, k, e, n, i, CH.key_all(p, e, he), he, hq, hc, hd))

law igoW:
  for +p: CH.Cls
  for +es: Ss()
  for +info: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +h: {CH.ALLS(p, es) == True{} : Bool}
  for +hq: {CH.ALLC(p, "=") == True{} : Bool}
  for +hc: {CH.ALLC(p, ",") == True{} : Bool}
  for +hd: {CH.ALLC(p, ".") == True{} : Bool}
  {CH.GOKS(p, B.Info.split.go(es, info, n, i)) == True{} : Bool}

def igoW(p, es, info, n, i, h, hq, hc, hd):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      CH.and_tt(CH.GOK(p, B.Info.split.num(B.Tags.find(info, B.Info.key(e)), e, n, i)), CH.GOKS(p, B.Info.split.go(t, info, n, i)),
        inumW(p, B.Tags.find(info, B.Info.key(e)), e, n, i, AB.and_true_l(CH.ALLC(p, e), CH.ALLS(p, t), h), hq, hc, hd),
        igoW(p, t, info, n, i, AB.and_true_r(CH.ALLC(p, e), CH.ALLS(p, t), h), hq, hc, hd))

# ---------------------------------------------------------------------------
# GT and FORMAT values of a record (proof_s_chars.bend's lemmas, asking only
# for ',', '.' and the digits): a value holds no ':' when the column holds none.
# ---------------------------------------------------------------------------

def SW(+p: CH.Cls) -> Bool:
  Bool.and(Bool.and(CH.pc(p, ','), CH.pc(p, '.')), CH.DIG(p))

def sw_comma(+p: CH.Cls, +h: {SW(p) == True{} : Bool}) -> {CH.ALLC(p, ",") == True{} : Bool}:
  CH.and_tt(CH.pc(p, ','), True{}, AB.and_true_l(CH.pc(p, ','), CH.pc(p, '.'), AB.and_true_l(Bool.and(CH.pc(p, ','), CH.pc(p, '.')), CH.DIG(p), h)), {==})

def sw_dot(+p: CH.Cls, +h: {SW(p) == True{} : Bool}) -> {CH.ALLC(p, ".") == True{} : Bool}:
  CH.and_tt(CH.pc(p, '.'), True{}, AB.and_true_r(CH.pc(p, ','), CH.pc(p, '.'), AB.and_true_l(Bool.and(CH.pc(p, ','), CH.pc(p, '.')), CH.DIG(p), h)), {==})

def sw_dig(+p: CH.Cls, +h: {SW(p) == True{} : Bool}) -> {CH.DIG(p) == True{} : Bool}:
  AB.and_true_r(Bool.and(CH.pc(p, ','), CH.pc(p, '.')), CH.DIG(p), h)

def gshowW(+p: CH.Cls, +a: Maybe<&2, Nat>, +hs: {SW(p) == True{} : Bool}) -> {CH.ALLC(p, B.Gt.show(a)) == True{} : Bool}:
  match a:
    case None{}:
      sw_dot(p, hs)
    case Some{+x}:
      CH.show_all(p, x, sw_dig(p, hs))

def gnumW(+p: CH.Cls, +m: Maybe<&2, Nat>, +over0: Bool, +n: Nat, +i: Nat, +hs: {SW(p) == True{} : Bool}) -> {CH.GOK(p, B.Gt.num(m, over0, n, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+a}:
      CH.pick_got(p, Nat.is_le(a, n), B.Got{B.Gt.show(B.Gt.rule(over0, i, Some{a}))}, B.Refuse{B.BadGt{}}, gshowW(p, B.Gt.rule(over0, i, Some{a}), hs), {==})

def galleleW(+p: CH.Cls, +over0: Bool, +n: Nat, +i: Nat, +a: String, +hs: {SW(p) == True{} : Bool}) -> {CH.GOK(p, B.Gt.allele(over0, n, i, a)) == True{} : Bool}:
  CH.pick_got(p, String.eq(a, "."), B.Got{"."}, Bool.pick(B.Got, B.Gt.canon(a), B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}}), sw_dot(p, hs),
    CH.pick_got(p, B.Gt.canon(a), B.Gt.num(B.Pos.read(a), over0, n, i), B.Refuse{B.BadGt{}}, gnumW(p, B.Pos.read(a), over0, n, i, hs), {==}))

def gputW(+p: CH.Cls, +sep: Bool, +h: Char, +r: B.Gp, +over0: Bool, +n: Nat, +i: Nat,
  +hh: {CH.pc(p, h) == True{} : Bool}, +hr: {CH.GPOK(p, r) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GPOK(p, B.Gt.go.put(sep, h, r, over0, n, i)) == True{} : Bool}:
  match sep r:
    case True{} B.Gp{+tk, +rs}:
      +hc = CH.got_cat(p, B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk), CH.and_tt(CH.pc(p, h), True{}, hh, {==}), {==}, galleleW(p, over0, n, i, tk, hs))
      CH.and_tt(True{}, CH.GOK(p, B.Got.cat(B.Got.cat(B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk)), "", rs)), {==},
        CH.got_cat(p, B.Got.cat(B.Got{SCon{h, SNil{}}}, "", B.Gt.allele(over0, n, i, tk)), "", rs, hc, {==}, AB.and_true_r(CH.ALLC(p, tk), CH.GOK(p, rs), hr)))
    case False{} B.Gp{+tk, +rs}:
      CH.and_tt(Bool.and(CH.pc(p, h), CH.ALLC(p, tk)), CH.GOK(p, rs), CH.and_tt(CH.pc(p, h), CH.ALLC(p, tk), hh, AB.and_true_l(CH.ALLC(p, tk), CH.GOK(p, rs), hr)), AB.and_true_r(CH.ALLC(p, tk), CH.GOK(p, rs), hr))

law ggoW:
  for +p: CH.Cls
  for +s: String
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +h: {CH.ALLC(p, s) == True{} : Bool}
  for +hs: {SW(p) == True{} : Bool}
  {CH.GPOK(p, B.Gt.go(s, over0, n, i)) == True{} : Bool}

def ggoW(p, s, over0, n, i, h, hs):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      gputW(p, B.Gt.is_sep(c), c, B.Gt.go(t, over0, n, i), over0, n, i, AB.and_true_l(CH.pc(p, c), CH.ALLC(p, t), h), ggoW(p, t, over0, n, i, AB.and_true_r(CH.pc(p, c), CH.ALLC(p, t), h), hs), hs)

def gofW(+p: CH.Cls, +r: B.Gp, +over0: Bool, +n: Nat, +i: Nat, +hr: {CH.GPOK(p, r) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GOK(p, B.Gt.split.of(r, over0, n, i)) == True{} : Bool}:
  match r:
    case B.Gp{+tk, +rs}:
      CH.got_cat(p, B.Gt.allele(over0, n, i, tk), "", rs, galleleW(p, over0, n, i, tk, hs), {==}, AB.and_true_r(CH.ALLC(p, tk), CH.GOK(p, rs), hr))

def gsplitW(+p: CH.Cls, +over0: Bool, +n: Nat, +i: Nat, +g: String, +h: {CH.ALLC(p, g) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GOK(p, B.Gt.split(over0, n, i, g)) == True{} : Bool}:
  gofW(p, B.Gt.go(g, over0, n, i), over0, n, i, ggoW(p, g, over0, n, i, h, hs), hs)

def fnum.kW(+p: CH.Cls, +num: B.Num, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {CH.ALLC(p, v) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GOK(p, B.Fmt.split.num(Some{num}, k, v, n, cp, i)) == True{} : Bool}:
  match num:
    case B.NumUnknown{}:
      {==}
    case B.NumOther{}:
      hv
    case B.NumA{}:
      CH.got_of(p, B.Vals.split(B.NumA{}, n, cp, i, v), B.BadCount{}, vsplitW(p, B.NumA{}, n, cp, i, v, hv, sw_comma(p, hs), sw_dot(p, hs)))
    case B.NumR{}:
      CH.got_of(p, B.Vals.split(B.NumR{}, n, cp, i, v), B.BadCount{}, vsplitW(p, B.NumR{}, n, cp, i, v, hv, sw_comma(p, hs), sw_dot(p, hs)))
    case B.NumG{}:
      CH.got_of(p, B.Vals.split(B.NumG{}, n, cp, i, v), B.BadCount{}, vsplitW(p, B.NumG{}, n, cp, i, v, hv, sw_comma(p, hs), sw_dot(p, hs)))

def fnumW(+p: CH.Cls, +m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {CH.ALLC(p, v) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GOK(p, B.Fmt.split.num(m, k, v, n, cp, i)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+num}:
      fnum.kW(p, num, k, v, n, cp, i, hv, hs)

def foneW(+p: CH.Cls, +k: String, +v: String, +fmt: List<&2, B.Tag>, +over0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +hv: {CH.ALLC(p, v) == True{} : Bool}, +hs: {SW(p) == True{} : Bool}) ->
  {CH.GOK(p, B.Fmt.split.one(k, v, fmt, over0, n, cp, i)) == True{} : Bool}:
  CH.pick_got(p, String.eq(k, "GT"), B.Gt.split(over0, n, i, v), B.Fmt.split.num(B.Tags.find(fmt, k), k, v, n, cp, i), gsplitW(p, over0, n, i, v, hv, hs), fnumW(p, B.Tags.find(fmt, k), k, v, n, cp, i, hv, hs))

law fgoW:
  for +p: CH.Cls
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +over0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +h: {CH.ALLS(p, vs) == True{} : Bool}
  for +hs: {SW(p) == True{} : Bool}
  {CH.GOKS(p, B.Fmt.split.go(ks, vs, fmt, over0, n, cp, i)) == True{} : Bool}

def fgoW(p, ks, vs, fmt, over0, n, cp, i, h, hs):
  match ks vs:
    case _ Nil{}:
      {==}
    case Nil{} Con{+v, +t}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      CH.and_tt(CH.GOK(p, B.Fmt.split.one(k, v, fmt, over0, n, cp, i)), CH.GOKS(p, B.Fmt.split.go(kt, vt, fmt, over0, n, cp, i)),
        foneW(p, k, v, fmt, over0, n, cp, i, AB.and_true_l(CH.ALLC(p, v), CH.ALLS(p, vt), h), hs),
        fgoW(p, kt, vt, fmt, over0, n, cp, i, AB.and_true_r(CH.ALLC(p, v), CH.ALLS(p, vt), h), hs))
