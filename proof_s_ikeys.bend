import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_chars.bend as CH
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_valw.bend as VW
import ./proof_run_text.bend as RT
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_info_keys: each record of a split line has the line's INFO keys,
# in order. Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def nc(+s: String, +c: Char, +h: {CH.ALLC(CH.NoC{c}, s) == True{} : Bool}) -> {RT.no_c(s, c) == True{} : Bool}:
  Equal.trans(Bool, RT.no_c(s, c), ST.noc(s, c), True{}, AT.nc_eq(s, c), Equal.trans(Bool, ST.noc(s, c), CH.ALLC(CH.NoC{c}, s), True{}, SM.noc_allc(s, c), h))

# An entry's key holds no '='.
def key_nc(+e: String) -> {RT.no_c(B.Info.key(e), '=') == True{} : Bool}:
  nc(B.Info.key(e), '=', CH.field_all(CH.NoC{'='}, String.split(e, '='), 0n,
    Equal.trans(Bool, CH.ALLS(CH.NoC{'='}, String.split(e, '=')), ST.allnoc(String.split(e, '='), '='), True{},
      Equal.sym(Bool, ST.allnoc(String.split(e, '='), '='), CH.ALLS(CH.NoC{'='}, String.split(e, '=')), SM.alls_noc(String.split(e, '='), '=')), ST.split_all(e, '='))))

# "k=v" has key k, when k holds no '='.
def key_eq(+k: String, +v: String, +h: {RT.no_c(k, '=') == True{} : Bool}) -> {B.Info.key(String.append(k, String.append("=", v))) == k : String}:
  %Equal.sym(Ss(), String.split(String.append(k, SCon{'=', v}), '='), k <> String.split(v, '='), RT.split_app(k, v, '=', h)) : {B.Rec.field(_, 0n) == k : String}
  {==}

def is_got(g: B.Got) -> Bool:
  SM.is_got(g)

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  AB.false_ne_true(Equal.cong(B.Got, Bool, is_got, B.Refuse{c}, B.Got{y}, h))

# A per-allele entry's result: its key, '=', the values kept.
def kv(+k: String, +m: Maybe<&2, String>, +y: String, +hk: {RT.no_c(k, '=') == True{} : Bool},
  +h: {B.Got.cat(B.Got{k}, "=", B.Got.of(m, B.BadCount{})) == B.Got{y} : B.Got}) -> {B.Info.key(y) == k : String}:
  match m:
    case None{}:
      Empty.absurd({B.Info.key(y) == k : String}, ref_ne(B.BadCount{}, y, h))
    case Some{+v}:
      +ey = Equal.cong(B.Got, String, SI.gtext, B.Got{String.append(k, String.append("=", v))}, B.Got{y}, h)
      {%ey : {B.Info.key(_) == k : String}; key_eq(k, v, hk) : {B.Info.key(y) == k : String}}

def keq(+m: Maybe<&2, B.Num>, +k: String, +e: String, +n: Nat, +i: Nat, +y: String, +hk: {RT.no_c(k, '=') == True{} : Bool},
  +h: {B.Info.split.eq(m, k, e, n, i) == B.Got{y} : B.Got}, +he: {B.Info.key(e) == k : String}) -> {B.Info.key(y) == k : String}:
  match m:
    case None{}:
      Empty.absurd({B.Info.key(y) == k : String}, ref_ne(B.UndefinedTag{"INFO/" ++ k}, y, h))
    case Some{+num}:
      match num:
        case B.NumUnknown{}:
          Empty.absurd({B.Info.key(y) == k : String}, ref_ne(B.UndefinedTag{"INFO/" ++ k}, y, h))
        case B.NumOther{}:
          {%Equal.cong(B.Got, String, SI.gtext, B.Got{e}, B.Got{y}, h) : {B.Info.key(_) == k : String}; he : {B.Info.key(y) == k : String}}
        case B.NumA{}:
          kv(k, B.Vals.split(B.NumA{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), y, hk, h)
        case B.NumR{}:
          kv(k, B.Vals.split(B.NumR{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), y, hk, h)
        case B.NumG{}:
          kv(k, B.Vals.split(B.NumG{}, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), y, hk, h)

def kflag(+pa: Bool, +e: String, +y: String, +h: {Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{e}) == B.Got{y} : B.Got}) -> {B.Info.key(y) == B.Info.key(e) : String}:
  match pa:
    case True{}:
      Empty.absurd({B.Info.key(y) == B.Info.key(e) : String}, ref_ne(B.BadCount{}, y, h))
    case False{}:
      {%Equal.cong(B.Got, String, SI.gtext, B.Got{e}, B.Got{y}, h) : {B.Info.key(_) == B.Info.key(e) : String}; {==} : {B.Info.key(y) == B.Info.key(e) : String}}

def kn.c(+c: Bool, +m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String,
  +h: {Bool.pick(B.Got, c, Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{e}), B.Info.split.eq(m, B.Info.key(e), e, n, i)) == B.Got{y} : B.Got}) ->
  {B.Info.key(y) == B.Info.key(e) : String}:
  match c:
    case True{}:
      kflag(B.Num.per_allele(m), e, y, h)
    case False{}:
      keq(m, B.Info.key(e), e, n, i, y, key_nc(e), h, {==})

# One entry of a record: the line's entry's key.
def kn(+m: Maybe<&2, B.Num>, +e: String, +n: Nat, +i: Nat, +y: String,
  +h: {B.Info.split.num(m, e, n, i) == B.Got{y} : B.Got}) -> {B.Info.key(y) == B.Info.key(e) : String}:
  kn.c(String.eq(B.Info.key(e), e), m, e, n, i, y, h)

def gkey(+g: B.Got, +x: String, +eg: {g == B.Got{SI.gtext(g)} : B.Got}) -> {g == B.Got{SI.gtext(g)} : B.Got}:
  eg

# The rest of the entries, from the joined text's rest.
def kgo.t(+et: Ss(), +e: String, +tags: List<&2, B.Tag>, +n: Nat, +i: Nat, +w: String,
  +h: {B.Got.join(B.Info.split.go(Con{e, et}, tags, n, i), ";") == B.Got{w} : B.Got},
  rec: @y: String -> {B.Got.join(B.Info.split.go(et, tags, n, i), ";") == B.Got{y} : B.Got} -> {L.info_keys.go(SM.TX(B.Info.split.go(et, tags, n, i))) == L.info_keys.go(et) : Ss()}) ->
  {B.Info.key(e) <> L.info_keys.go(SM.TX(B.Info.split.go(et, tags, n, i))) == B.Info.key(e) <> L.info_keys.go(et) : Ss()}:
  match et:
    case Nil{}:
      {==}
    case Con{+e2, +et2}:
      +g = B.Info.split.num(B.Tags.find(tags, B.Info.key(e)), e, n, i)
      +J = B.Got.join(B.Info.split.go(Con{e2, et2}, tags, n, i), ";")
      +eg = AT.cat_l(g, ";", J, w, h)
      +h2 = AB.subst(B.Got, z => {B.Got.cat(z, ";", J) == B.Got{w} : B.Got}, g, B.Got{SI.gtext(g)}, eg, h)
      Equal.cong(Ss(), Ss(), z => B.Info.key(e) <> z, L.info_keys.go(SM.TX(B.Info.split.go(Con{e2, et2}, tags, n, i))), L.info_keys.go(Con{e2, et2}),
        rec(SI.gtext(J), AT.cat_r(SI.gtext(g), ";", J, w, h2)))

# The entries of a record, joined: their keys are the line's entries' keys.
law kgo:
  for +es: Ss()
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +w: String
  for +h: {B.Got.join(B.Info.split.go(es, tags, n, i), ";") == B.Got{w} : B.Got}
  {L.info_keys.go(SM.TX(B.Info.split.go(es, tags, n, i))) == L.info_keys.go(es) : Ss()}

def kgo(es, tags, n, i, w, h):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +et}:
      +g = B.Info.split.num(B.Tags.find(tags, B.Info.key(e)), e, n, i)
      +eg = AT.join_nth(Con{g, B.Info.split.go(et, tags, n, i)}, ";", w, h, 0n, g, {==})
      +ek = kn(B.Tags.find(tags, B.Info.key(e)), e, n, i, SI.gtext(g), eg)
      %Equal.sym(String, B.Info.key(SI.gtext(g)), B.Info.key(e), ek) : {_ <> L.info_keys.go(SM.TX(B.Info.split.go(et, tags, n, i))) == B.Info.key(e) <> L.info_keys.go(et) : Ss()}
      kgo.t(et, e, tags, n, i, w, h, y => hy => kgo(et, tags, n, i, y, hy))

# The entries of the line's INFO, split from a record's INFO.
def ik_es(es: Ss(), +tags: List<&2, B.Tag>, +n: Nat, +i: Nat, +w: String,
  +h: {B.Got.join(B.Info.split.go(es, tags, n, i), ";") == B.Got{w} : B.Got},
  +hes: {CH.ALLS(CH.NoC{';'}, es) == True{} : Bool},
  +hc: {ST.is_cons(es) == True{} : Bool}) ->
  {L.info_keys.go(String.split(w, ';')) == L.info_keys.go(es) : Ss()}:
  match es:
    case Nil{}:
      Empty.absurd({L.info_keys.go(String.split(w, ';')) == L.info_keys.go(Nil{}) : Ss()}, AB.false_ne_true(hc))
    case Con{+e, +et}:
      +g = B.Info.split.num(B.Tags.find(tags, B.Info.key(e)), e, n, i)
      %Equal.sym(Ss(), String.split(w, ';'), SM.TX(Con{g, B.Info.split.go(et, tags, n, i)}),
          AT.join_sep(';', B.Info.split.go(et, tags, n, i), g, w, h, VW.igoW(CH.NoC{';'}, Con{e, et}, tags, n, i, hes, {==}, {==}, {==}))) :
        {L.info_keys.go(_) == L.info_keys.go(Con{e, et}) : Ss()}
      kgo(Con{e, et}, tags, n, i, w, h)

def semi_all(+x: String) -> {CH.ALLS(CH.NoC{';'}, String.split(x, ';')) == True{} : Bool}:
  Equal.trans(Bool, CH.ALLS(CH.NoC{';'}, String.split(x, ';')), ST.allnoc(String.split(x, ';'), ';'), True{},
    Equal.sym(Bool, ST.allnoc(String.split(x, ';'), ';'), CH.ALLS(CH.NoC{';'}, String.split(x, ';')), SM.alls_noc(String.split(x, ';'), ';')), ST.split_all(x, ';'))

# A record of a line whose fields are fs: the line's INFO keys.
def ik_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +k: Nat, +a: String, +p: String,
  +hg: {B.Rec.piece(fs, a, defs, o0, n, k) == B.Got{p} : B.Got},
  +hf: {CH.ALLS(SM.TAB(), fs) == True{} : Bool},
  +ha: {CH.ALLC(SM.TAB(), a) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) ->
  {L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(fs, 7n), ';')) : Ss()}:
  match fs:
    case Nil{}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Nil{}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Nil{}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Nil{}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Nil{}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Nil{}}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({L.info_keys.go(String.split(B.Rec.field(B.Rec.fields(p), 7n), ';')) == L.info_keys.go(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, 7n), ';')) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +r}}}}}}}}:
      +FS8 = SM.F8(f0, f1, f2, f3, f4, f5, f6, f7, r)
      +ks = String.split(B.Rec.field(FS8, 8n), ':')
      +GS = B.Rec.piece.go(FS8, 0n, a, defs, ks, o0, n, k)
      +ef = AT.fields_at(f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}}, a, defs, o0, n, k, p, hg, hf, ha)
      +I = B.Info.split(f7, B.Defs.info(defs), n, k)
      +eI = AT.join_nth(GS, "\t", p, hg, 7n, I, {==})
      %Equal.sym(Ss(), B.Rec.fields(p), SM.TX(GS), ef) : {L.info_keys.go(String.split(B.Rec.field(_, 7n), ';')) == L.info_keys.go(String.split(f7, ';')) : Ss()}
      ik_es(String.split(f7, ';'), B.Defs.info(defs), n, k, SI.gtext(I), eI, semi_all(f7), ST.split_cons(f7, ';'))

def ik_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String,
  r: AT.AT(defs, o0, body, i, p), +hl: AT.L8T(body)) -> {L.info_keys(p) == L.info_keys(body) : Ss()}:
  match r:
    case (+a, q):
      match q:
        case (ha, hg):
          ik_fs(AT.FS(body), defs, o0, L.n_alts(body), 1n+i, a, p, hg, AT.fs_tab(body), AT.alt_tab(body, i, a, ha), hl)

# Law split_info_keys: each record has the input's INFO keys, in order.
law split_info_keys:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  {L.info_keys(p) == L.info_keys(body) : Ss()}

def split_info_keys(defs, o, body, ps, h, i, p, hp):
  ik_at(defs, R.Opts.over0(o), body, i, p, AT.piece_at(defs, o, body, ps, h, i, p, hp), AT.parts_l8(defs, o, body, ps, h))
