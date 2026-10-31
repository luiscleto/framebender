import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_chars.bend as CH
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_col.bend as CO
import ./proof_s_ikeys.bend as IK
import ./proof_run_text.bend as RT
import ./proof_run_rec.bend as RR
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_format_values: a per-allele FORMAT value (not GT, not '.') gives,
# in the record for ALT i+1, exactly the values of that record's alleles
# (lifted). Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  CO.ref_ne(c, y, h)

law an_eq:
  for +xs: Ss()
  for +c: Char
  {RT.all_noc(xs, c) == CH.ALLS(CH.NoC{c}, xs) : Bool}

def an_eq(xs, c):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, RT.no_c(x, c), CH.ALLC(CH.NoC{c}, x), Equal.trans(Bool, RT.no_c(x, c), ST.noc(x, c), CH.ALLC(CH.NoC{c}, x), AT.nc_eq(x, c), SM.noc_allc(x, c))) :
        {Bool.and(_, RT.all_noc(t, c)) == CH.ALLS(CH.NoC{c}, Con{x, t}) : Bool}
      %Equal.sym(Bool, RT.all_noc(t, c), CH.ALLS(CH.NoC{c}, t), an_eq(t, c)) : {Bool.and(CH.ALLC(CH.NoC{c}, x), _) == CH.ALLS(CH.NoC{c}, Con{x, t}) : Bool}
      {==}

# Values without commas, joined with commas, then split: the values.
def sj(ys: Ss(), +hc: {ST.is_cons(ys) == True{} : Bool}, +hn: {CH.ALLS(CH.NoC{','}, ys) == True{} : Bool}) -> {String.split(String.join(ys, ","), ',') == ys : Ss()}:
  match ys:
    case Nil{}:
      Empty.absurd({String.split(String.join(Nil{}, ","), ',') == Nil{} : Ss()}, AB.false_ne_true(hc))
    case Con{+y, +t}:
      RR.split_join(t, y, ',', IK.nc(y, ',', AB.and_true_l(CH.ALLC(CH.NoC{','}, y), CH.ALLS(CH.NoC{','}, t), hn)),
        Equal.trans(Bool, RT.all_noc(t, ','), CH.ALLS(CH.NoC{','}, t), True{}, an_eq(t, ','), AB.and_true_r(CH.ALLC(CH.NoC{','}, y), CH.ALLS(CH.NoC{','}, t), hn)))

def pc_ne(m: Maybe<&2, String>, r: Maybe<&2, Ss()>, +ys: Ss(), +h: {B.Vals.pick.cons(m, r) == Some{ys} : Maybe<&2, Ss()>}) -> {ST.is_cons(ys) == True{} : Bool}:
  match m r:
    case Some{+x} Some{+xs}:
      Equal.sym(Bool, True{}, ST.is_cons(ys), Equal.cong(Ss(), Bool, ST.is_cons, Con{x, xs}, ys, Equal.cong(Maybe<&2, Ss()>, Ss(), z => Maybe.default(&2, Ss(), z, Nil{}), Some{Con{x, xs}}, Some{ys}, h)))
    case Some{+x} None{}:
      Empty.absurd({ST.is_cons(ys) == True{} : Bool}, AB.false_ne_true(Equal.cong(Maybe<&2, Ss()>, Bool, z => Maybe.is_some(&2, Ss(), z), None{}, Some{ys}, h)))
    case None{} _:
      Empty.absurd({ST.is_cons(ys) == True{} : Bool}, AB.false_ne_true(Equal.cong(Maybe<&2, Ss()>, Bool, z => Maybe.is_some(&2, Ss(), z), None{}, Some{ys}, h)))

# The values kept, read back: the values picked.
def fv.join(M: Maybe<&2, Ss()>, +vs: Ss(), +ks: List<&2, Nat>, +k0: Nat, +kt: List<&2, Nat>,
  +ek: {ks == Con{k0, kt} : List<&2, Nat>},
  +eM: {B.Vals.pick(vs, ks) == M : Maybe<&2, Ss()>},
  +hvs: {CH.ALLS(CH.NoC{','}, vs) == True{} : Bool},
  +hg: {B.Got.of(B.Vals.join(M), B.BadCount{}) == B.Got{SI.gtext(B.Got.of(B.Vals.join(M), B.BadCount{}))} : B.Got}) ->
  {L.values_of(Some{SI.gtext(B.Got.of(B.Vals.join(M), B.BadCount{}))}) == M : Maybe<&2, Ss()>}:
  match M:
    case None{}:
      Empty.absurd({L.values_of(Some{""}) == None{} : Maybe<&2, Ss()>}, ref_ne(B.BadCount{}, "", hg))
    case Some{+ys}:
      +hok = {%eM : {CH.MLOK(CH.NoC{','}, _) == True{} : Bool}; CH.pick_ok(CH.NoC{','}, vs, ks, hvs) : {CH.ALLS(CH.NoC{','}, ys) == True{} : Bool}}
      +hc = pc_ne(List.get(&2, String, vs, k0), B.Vals.pick(vs, kt), ys,
        {%ek : {B.Vals.pick(vs, _) == Some{ys} : Maybe<&2, Ss()>}; eM : {B.Vals.pick.cons(List.get(&2, String, vs, k0), B.Vals.pick(vs, kt)) == Some{ys} : Maybe<&2, Ss()>}})
      Equal.cong(Ss(), Maybe<&2, Ss()>, z => Some{z}, String.split(String.join(ys, ","), ','), ys, sj(ys, hc, hok))

def KEEP(+num: B.Num, +n: Nat, +q: Nat, +i: Nat, +vs: Ss()) -> B.Got:
  B.Got.of(B.Vals.keep(num, n, q, i, vs), B.BadCount{})

def fv.keep(+b: Bool, +num: B.Num, +n: Nat, +q: Nat, +i: Nat, +vs: Ss(), +k0: Nat, +kt: List<&2, Nat>,
  +ek: {B.Vals.idx(num, q, i) == Con{k0, kt} : List<&2, Nat>},
  +eb: {B.Vals.fits(B.Vals.expected_count(num, n, q), List.length(&2, String, vs)) == b : Bool},
  +hvs: {CH.ALLS(CH.NoC{','}, vs) == True{} : Bool},
  +hg: {KEEP(num, n, q, i, vs) == B.Got{SI.gtext(KEEP(num, n, q, i, vs))} : B.Got}) ->
  {L.values_of(Some{SI.gtext(KEEP(num, n, q, i, vs))}) == B.Vals.pick(vs, B.Vals.idx(num, q, i)) : Maybe<&2, Ss()>}:
  match b:
    case False{}:
      +P = B.Vals.pick(vs, B.Vals.idx(num, q, i))
      +hg2 = {%eb : {B.Got.of(Bool.pick(Maybe<&2, String>, _, B.Vals.join(P), None{}), B.BadCount{}) == B.Got{SI.gtext(B.Got.of(Bool.pick(Maybe<&2, String>, _, B.Vals.join(P), None{}), B.BadCount{}))} : B.Got};
        hg : {B.Refuse{B.BadCount{}} == B.Got{""} : B.Got}}
      Empty.absurd({L.values_of(Some{SI.gtext(KEEP(num, n, q, i, vs))}) == P : Maybe<&2, Ss()>}, ref_ne(B.BadCount{}, "", hg2))
    case True{}:
      +P = B.Vals.pick(vs, B.Vals.idx(num, q, i))
      {%Equal.sym(Bool, B.Vals.fits(B.Vals.expected_count(num, n, q), List.length(&2, String, vs)), True{}, eb) : {L.values_of(Some{SI.gtext(B.Got.of(Bool.pick(Maybe<&2, String>, _, B.Vals.join(P), None{}), B.BadCount{}))}) == P : Maybe<&2, Ss()>};
       fv.join(P, vs, B.Vals.idx(num, q, i), k0, kt, ek, {==}, hvs,
         {%eb : {B.Got.of(Bool.pick(Maybe<&2, String>, _, B.Vals.join(P), None{}), B.BadCount{}) == B.Got{SI.gtext(B.Got.of(Bool.pick(Maybe<&2, String>, _, B.Vals.join(P), None{}), B.BadCount{}))} : B.Got};
          hg : {B.Got.of(B.Vals.join(P), B.BadCount{}) == B.Got{SI.gtext(B.Got.of(B.Vals.join(P), B.BadCount{}))} : B.Got}}) :
       {L.values_of(Some{SI.gtext(KEEP(num, n, q, i, vs))}) == P : Maybe<&2, Ss()>}}

def fv.g(+c: Bool, +n: Nat, +q: Nat, +i: Nat, +vs: Ss(),
  +ec: {Nat.is_eq(q, 1n) == c : Bool},
  +hvs: {CH.ALLS(CH.NoC{','}, vs) == True{} : Bool},
  +hg: {KEEP(B.NumG{}, n, q, 1n+i, vs) == B.Got{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))} : B.Got}) ->
  {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == L.lifted(B.NumG{}, q, 1n+i, vs) : Maybe<&2, Ss()>}:
  match c:
    case True{}:
      {%Equal.sym(Bool, Nat.is_eq(q, 1n), True{}, ec) : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == Bool.pick(Maybe<&2, Ss()>, _, L.somes([L.allele_value(B.NumG{}, vs, 0n), L.allele_value(B.NumG{}, vs, 1n+i)]), L.somes([L.genotype_value(vs, 0n, 0n), L.genotype_value(vs, 0n, 1n+i), L.genotype_value(vs, 1n+i, 1n+i)])) : Maybe<&2, Ss()>};
       %ec : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == B.Vals.pick(vs, Bool.pick(List<&2, Nat>, _, [0n, 1n+i], [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)])) : Maybe<&2, Ss()>};
       fv.keep(B.Vals.fits(B.Vals.expected_count(B.NumG{}, n, q), List.length(&2, String, vs)), B.NumG{}, n, q, 1n+i, vs, 0n, [1n+i],
         {%Equal.sym(Bool, Nat.is_eq(q, 1n), True{}, ec) : {Bool.pick(List<&2, Nat>, _, [0n, 1n+i], [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)]) == [0n, 1n+i] : List<&2, Nat>}; {==} : {B.Vals.idx(B.NumG{}, q, 1n+i) == [0n, 1n+i] : List<&2, Nat>}},
         {==}, hvs, hg) : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == L.lifted(B.NumG{}, q, 1n+i, vs) : Maybe<&2, Ss()>}}
    case False{}:
      {%Equal.sym(Bool, Nat.is_eq(q, 1n), False{}, ec) : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == Bool.pick(Maybe<&2, Ss()>, _, L.somes([L.allele_value(B.NumG{}, vs, 0n), L.allele_value(B.NumG{}, vs, 1n+i)]), L.somes([L.genotype_value(vs, 0n, 0n), L.genotype_value(vs, 0n, 1n+i), L.genotype_value(vs, 1n+i, 1n+i)])) : Maybe<&2, Ss()>};
       %ec : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == B.Vals.pick(vs, Bool.pick(List<&2, Nat>, _, [0n, 1n+i], [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)])) : Maybe<&2, Ss()>};
       fv.keep(B.Vals.fits(B.Vals.expected_count(B.NumG{}, n, q), List.length(&2, String, vs)), B.NumG{}, n, q, 1n+i, vs, 0n, [B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)],
         {%Equal.sym(Bool, Nat.is_eq(q, 1n), False{}, ec) : {Bool.pick(List<&2, Nat>, _, [0n, 1n+i], [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)]) == [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)] : List<&2, Nat>}; {==} : {B.Vals.idx(B.NumG{}, q, 1n+i) == [0n, B.Gt.index(0n, 1n+i), B.Gt.index(1n+i, 1n+i)] : List<&2, Nat>}},
         {==}, hvs, hg) : {L.values_of(Some{SI.gtext(KEEP(B.NumG{}, n, q, 1n+i, vs))}) == L.lifted(B.NumG{}, q, 1n+i, vs) : Maybe<&2, Ss()>}}

# The values kept, for a per-allele tag: lifted.
def fv.lift(+num: B.Num, +n: Nat, +q: Nat, +i: Nat, +vs: Ss(),
  +ha: {L.per_allele_num(num) == True{} : Bool},
  +hvs: {CH.ALLS(CH.NoC{','}, vs) == True{} : Bool},
  +hg: {KEEP(num, n, q, 1n+i, vs) == B.Got{SI.gtext(KEEP(num, n, q, 1n+i, vs))} : B.Got}) ->
  {L.values_of(Some{SI.gtext(KEEP(num, n, q, 1n+i, vs))}) == L.lifted(num, q, 1n+i, vs) : Maybe<&2, Ss()>}:
  match num:
    case B.NumA{}:
      fv.keep(B.Vals.fits(B.Vals.expected_count(B.NumA{}, n, q), List.length(&2, String, vs)), B.NumA{}, n, q, 1n+i, vs, Nat.sub(1n+i, 1n), Nil{}, {==}, {==}, hvs, hg)
    case B.NumR{}:
      fv.keep(B.Vals.fits(B.Vals.expected_count(B.NumR{}, n, q), List.length(&2, String, vs)), B.NumR{}, n, q, 1n+i, vs, 0n, [1n+i], {==}, {==}, hvs, hg)
    case B.NumG{}:
      fv.g(Nat.is_eq(q, 1n), n, q, i, vs, {==}, hvs, hg)
    case B.NumOther{}:
      Empty.absurd({L.values_of(Some{SI.gtext(KEEP(B.NumOther{}, n, q, 1n+i, vs))}) == L.lifted(B.NumOther{}, q, 1n+i, vs) : Maybe<&2, Ss()>}, AB.false_ne_true(ha))
    case B.NumUnknown{}:
      Empty.absurd({L.values_of(Some{SI.gtext(KEEP(B.NumUnknown{}, n, q, 1n+i, vs))}) == L.lifted(B.NumUnknown{}, q, 1n+i, vs) : Maybe<&2, Ss()>}, AB.false_ne_true(ha))

def comma_all(+x: String) -> {CH.ALLS(CH.NoC{','}, String.split(x, ',')) == True{} : Bool}:
  Equal.trans(Bool, CH.ALLS(CH.NoC{','}, String.split(x, ',')), ST.allnoc(String.split(x, ','), ','), True{},
    Equal.sym(Bool, ST.allnoc(String.split(x, ','), ','), CH.ALLS(CH.NoC{','}, String.split(x, ',')), SM.alls_noc(String.split(x, ','), ',')), ST.split_all(x, ','))

def VS(+v: String) -> Ss():
  String.split(v, ',')

def QV(+cp: Maybe<&2, Nat>, +n: Nat, +v: String) -> Nat:
  B.Vals.copies(cp, n, List.length(&2, String, VS(v)))

# A per-allele value (not '.'): the values kept.
def fv.n(+num: B.Num, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +ha: {L.per_allele_num(num) == True{} : Bool},
  +hm: {String.eq(v, ".") == False{} : Bool}) ->
  {B.Fmt.split.num(Some{num}, k, v, n, cp, 1n+i) == KEEP(num, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}:
  match num:
    case B.NumA{}:
      %Equal.sym(Bool, String.eq(v, "."), False{}, hm) : {B.Got.of(B.Vals.split.if(_, B.NumA{}, n, cp, 1n+i, v), B.BadCount{}) == KEEP(B.NumA{}, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}
      {==}
    case B.NumR{}:
      %Equal.sym(Bool, String.eq(v, "."), False{}, hm) : {B.Got.of(B.Vals.split.if(_, B.NumR{}, n, cp, 1n+i, v), B.BadCount{}) == KEEP(B.NumR{}, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}
      {==}
    case B.NumG{}:
      %Equal.sym(Bool, String.eq(v, "."), False{}, hm) : {B.Got.of(B.Vals.split.if(_, B.NumG{}, n, cp, 1n+i, v), B.BadCount{}) == KEEP(B.NumG{}, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}
      {==}
    case B.NumOther{}:
      Empty.absurd({B.Fmt.split.num(Some{B.NumOther{}}, k, v, n, cp, 1n+i) == KEEP(B.NumOther{}, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}, AB.false_ne_true(ha))
    case B.NumUnknown{}:
      Empty.absurd({B.Fmt.split.num(Some{B.NumUnknown{}}, k, v, n, cp, 1n+i) == KEEP(B.NumUnknown{}, n, QV(cp, n, v), 1n+i, VS(v)) : B.Got}, AB.false_ne_true(ha))

def RHS(+num: B.Num, +body: String, +s: Nat, +i: Nat, +v: String) -> Maybe<&2, Ss()>:
  L.lifted(num, B.Vals.copies(L.sample_copies(body, s), L.n_alts(body), List.length(&2, String, L.values(v))), 1n+i, L.values(v))

def fv_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +k: String, +v: String, +num: B.Num,
  +hgt: {String.eq(k, "GT") == False{} : Bool},
  +hn: {B.Tags.find(B.Defs.fmt(defs), k) == Some{num} : Maybe<&2, B.Num>},
  +ha: {L.per_allele_num(num) == True{} : Bool},
  +hm: {String.eq(v, ".") == False{} : Bool},
  r: CO.VA(defs, o0, body, i, p, s, j, k, v)) -> {L.values_of(L.sample_at(p, s, j)) == RHS(num, body, s, i, v) : Maybe<&2, Ss()>}:
  match r:
    case (+col, q):
      match q:
        case (em, q2):
          match q2:
            case (eO, ea):
              +n = L.n_alts(body)
              +cp = CO.CP(body, col)
              +fmt = B.Defs.fmt(defs)
              +O = CO.ONE(defs, o0, body, i, col, k, v)
              +N1 = B.Fmt.split.num(B.Tags.find(fmt, k), k, v, n, cp, 1n+i)
              +K = KEEP(num, n, QV(cp, n, v), 1n+i, VS(v))
              +e1 = Equal.cong(Bool, B.Got, z => Bool.pick(B.Got, z, B.Gt.split(o0, n, 1n+i, v), N1), String.eq(k, "GT"), False{}, hgt)
              +e2 = Equal.cong(Maybe<&2, B.Num>, B.Got, z => B.Fmt.split.num(z, k, v, n, cp, 1n+i), B.Tags.find(fmt, k), Some{num}, hn)
              +eK = Equal.trans(B.Got, O, N1, K, e1, Equal.trans(B.Got, N1, B.Fmt.split.num(Some{num}, k, v, n, cp, 1n+i), K, e2, fv.n(num, k, v, n, cp, i, ha, hm)))
              +hgK = Equal.trans(B.Got, K, O, B.Got{SI.gtext(K)}, Equal.sym(B.Got, O, K, eK),
                Equal.trans(B.Got, O, B.Got{SI.gtext(O)}, B.Got{SI.gtext(K)}, eO, Equal.cong(B.Got, B.Got, z => B.Got{SI.gtext(z)}, O, K, eK)))
              +ecp = Equal.cong(Maybe<&2, String>, Maybe<&2, Nat>, z => L.copies_of(L.column_values(z), L.format_keys(body)), List.get(&2, String, AT.FS(body), Nat.add(9n, s)), Some{col}, em)
              Equal.trans(Maybe<&2, Ss()>, L.values_of(L.sample_at(p, s, j)), L.values_of(Some{SI.gtext(O)}), RHS(num, body, s, i, v),
                Equal.cong(Maybe<&2, String>, Maybe<&2, Ss()>, z => L.values_of(z), L.sample_at(p, s, j), Some{SI.gtext(O)}, ea),
                Equal.trans(Maybe<&2, Ss()>, L.values_of(Some{SI.gtext(O)}), L.values_of(Some{SI.gtext(K)}), RHS(num, body, s, i, v),
                  Equal.cong(B.Got, Maybe<&2, Ss()>, z => L.values_of(Some{SI.gtext(z)}), O, K, eK),
                  Equal.trans(Maybe<&2, Ss()>, L.values_of(Some{SI.gtext(K)}), L.lifted(num, QV(cp, n, v), 1n+i, VS(v)), RHS(num, body, s, i, v),
                    fv.lift(num, n, QV(cp, n, v), i, VS(v), ha, comma_all(v), hgK),
                    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Ss()>, z => L.lifted(num, B.Vals.copies(z, n, List.length(&2, String, VS(v))), 1n+i, VS(v)), cp, L.sample_copies(body, s), Equal.sym(Maybe<&2, Nat>, L.sample_copies(body, s), cp, ecp)))))

# Law split_format_values: every per-allele FORMAT value (not GT, not '.')
# gives, in the record for ALT i+1, exactly the values of that record's
# alleles (lifted), for the copies its sample's GT names.
law split_format_values:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +j: Nat
  for +k: String
  for +hk: {List.get(&2, String, L.format_keys(body), j) == Some{k} : Maybe<&2, String>}
  for +hgt: {String.eq(k, "GT") == False{} : Bool}
  for +num: B.Num
  for +hn: {B.Tags.find(B.Defs.fmt(defs), k) == Some{num} : Maybe<&2, B.Num>}
  for +ha: {L.per_allele_num(num) == True{} : Bool}
  for +v: String
  for +hv: {L.sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
  for +hm: {String.eq(v, ".") == False{} : Bool}
  {L.values_of(L.sample_at(p, s, j)) == RHS(num, body, s, i, v) : Maybe<&2, Ss()>}

def split_format_values(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, num, hn, ha, v, hv, hm):
  fv_at(defs, R.Opts.over0(o), body, i, p, s, j, k, v, num, hgt, hn, ha, hm, CO.val_at(defs, o, body, ps, h, i, p, hp, s, j, k, hk, v, hv))
