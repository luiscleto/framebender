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
import ./proof_s_ikeys.bend as IK
import ./proof_s_col.bend as CO
import ./proof_run_base.bend as RB
import ./proof_run_rec.bend as RR
import ./proof_run_text.bend as RT
import ./proof_machine_nat.bend as MN
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# INFO entries: an entry with a value is its key, '=' and its value text; and
# entry e of the record for ALT i+1 is B.Info.split.num of the line's entry e.
# Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def drop0(+v: String) -> {String.drop(v, 0n) == v : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      {==}

law drop_app:
  for +us: String
  for +c: Char
  for +v: String
  {String.drop(String.append(us, SCon{c, v}), Nat.add(String.length(us), 1n)) == v : String}

def drop_app(us, c, v):
  match us:
    case SNil{}:
      drop0(v)
    case SCon{+h, +r}:
      drop_app(r, c, v)

law ltp:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, Nat.add(a, 1n+b)) == True{} : Bool}

def ltp(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      ltp(p, b)

def KV(+x: String) -> String:
  String.append(B.Info.key(x), String.append("=", L.value_text(x)))

# k=y, k without '=': its value text is y.
def vtx(+k: String, +y: String, +hk: {RT.no_c(k, '=') == True{} : Bool}) -> {L.value_text(String.append(k, String.append("=", y))) == y : String}:
  %Equal.sym(String, B.Info.key(String.append(k, String.append("=", y))), k, IK.key_eq(k, y, hk)) : {String.drop(String.append(k, String.append("=", y)), Nat.add(String.length(_), 1n)) == y : String}
  drop_app(k, '=', y)

def kvx.r(rest: Ss(), +k0: String, +x: String,
  +ej: {String.join(Con{k0, rest}, "=") == x : String},
  +ek: {B.Info.key(x) == k0 : String},
  +hne: {String.eq(B.Info.key(x), x) == False{} : Bool}) -> {x == KV(x) : String}:
  match rest:
    case Nil{}:
      +exk = Equal.trans(String, x, k0, B.Info.key(x), Equal.sym(String, k0, x, ej), Equal.sym(String, B.Info.key(x), k0, ek))
      +ht = {%Equal.sym(String, x, B.Info.key(x), exk) : {String.eq(B.Info.key(x), _) == True{} : Bool}; RB.str_eq_refl(B.Info.key(x)) : {String.eq(B.Info.key(x), x) == True{} : Bool}}
      Empty.absurd({x == KV(x) : String}, AB.false_ne_true(Equal.trans(Bool, False{}, String.eq(B.Info.key(x), x), True{}, Equal.sym(Bool, String.eq(B.Info.key(x), x), False{}, hne), ht)))
    case Con{+r0, +rt}:
      +Rr = String.join.go(rt, r0, "=")
      +ex = Equal.sym(String, String.append(k0, String.append("=", Rr)), x, ej)
      +vt = Equal.trans(String, L.value_text(x), String.drop(x, Nat.add(String.length(k0), 1n)), Rr,
        Equal.cong(String, String, z => String.drop(x, Nat.add(String.length(z), 1n)), B.Info.key(x), k0, ek),
        Equal.trans(String, String.drop(x, Nat.add(String.length(k0), 1n)), String.drop(String.append(k0, String.append("=", Rr)), Nat.add(String.length(k0), 1n)), Rr,
          Equal.cong(String, String, z => String.drop(z, Nat.add(String.length(k0), 1n)), x, String.append(k0, String.append("=", Rr)), ex),
          drop_app(k0, '=', Rr)))
      Equal.trans(String, x, String.append(k0, String.append("=", Rr)), KV(x), ex,
        Equal.trans(String, String.append(k0, String.append("=", Rr)), String.append(B.Info.key(x), String.append("=", Rr)), KV(x),
          Equal.cong(String, String, z => String.append(z, String.append("=", Rr)), k0, B.Info.key(x), Equal.sym(String, B.Info.key(x), k0, ek)),
          Equal.cong(String, String, z => String.append(B.Info.key(x), String.append("=", z)), Rr, L.value_text(x), Equal.sym(String, L.value_text(x), Rr, vt))))

def kvx.k(ss: Ss(), +x: String,
  +es: {String.split(x, '=') == ss : Ss()},
  +hne: {String.eq(B.Info.key(x), x) == False{} : Bool}) -> {x == KV(x) : String}:
  match ss:
    case Nil{}:
      +hc = {%es : {ST.is_cons(_) == True{} : Bool}; ST.split_cons(x, '=') : {ST.is_cons(Nil{}) == True{} : Bool}}
      Empty.absurd({x == KV(x) : String}, AB.false_ne_true(hc))
    case Con{+k0, +rest}:
      +ej = {%es : {String.join(_, "=") == x : String}; RR.join_split(x, '=') : {String.join(Con{k0, rest}, "=") == x : String}}
      +ek = {%Equal.sym(Ss(), String.split(x, '='), Con{k0, rest}, es) : {B.Rec.field(_, 0n) == k0 : String}; {==} : {B.Info.key(x) == k0 : String}}
      kvx.r(rest, k0, x, ej, ek, hne)

# An entry whose key is not the whole entry: its key, '=', its value text.
law kvx:
  for +x: String
  for +hne: {String.eq(B.Info.key(x), x) == False{} : Bool}
  {x == KV(x) : String}

def kvx(x, hne):
  kvx.k(String.split(x, '='), x, {==}, hne)

def hv_ne.k(+b: Bool, +x: String, +eb: {String.eq(B.Info.key(x), x) == b : Bool}, +hv: {L.has_value(x) == True{} : Bool}) -> {String.eq(B.Info.key(x), x) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = RB.str_eq_sound(B.Info.key(x), x, eb)
      +h2 = {%e : {Nat.is_lt(String.length(_), String.length(x)) == True{} : Bool}; hv : {Nat.is_lt(String.length(x), String.length(x)) == True{} : Bool}}
      Empty.absurd({String.eq(B.Info.key(x), x) == False{} : Bool}, AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(String.length(x), String.length(x)), True{}, Equal.sym(Bool, Nat.is_lt(String.length(x), String.length(x)), False{}, N.lt_irrefl(String.length(x))), h2)))

# An entry with a value is not its key alone.
def hv_ne(+x: String, +hv: {L.has_value(x) == True{} : Bool}) -> {String.eq(B.Info.key(x), x) == False{} : Bool}:
  hv_ne.k(String.eq(B.Info.key(x), x), x, {==}, hv)

# An entry that is not its key alone has a value.
def ne_hv(+x: String, +hne: {String.eq(B.Info.key(x), x) == False{} : Bool}) -> {L.has_value(x) == True{} : Bool}:
  +K = B.Info.key(x)
  +V = L.value_text(x)
  +el = Equal.trans(Nat, String.length(x), String.length(KV(x)), Nat.add(String.length(K), 1n+String.length(V)),
    Equal.cong(String, Nat, z => String.length(z), x, KV(x), kvx(x, hne)),
    MN.str_len_append(K, String.append("=", V)))
  {%Equal.sym(Nat, String.length(x), Nat.add(String.length(K), 1n+String.length(V)), el) : {Nat.is_lt(String.length(K), _) == True{} : Bool};
   ltp(String.length(K), String.length(V)) : {L.has_value(x) == True{} : Bool}}

def IGO(+es: Ss(), +tags: List<&2, B.Tag>, +n: Nat, +i: Nat) -> Gs():
  B.Info.split.go(es, tags, n, i)

law igo_get:
  for +es: Ss()
  for +tags: List<&2, B.Tag>
  for +n: Nat
  for +i: Nat
  for +e: Nat
  for +x: String
  for +hx: {List.get(&2, String, es, e) == Some{x} : Maybe<&2, String>}
  {List.get(&2, B.Got, IGO(es, tags, n, i), e) == Some{B.Info.split.num(B.Tags.find(tags, B.Info.key(x)), x, n, i)} : Maybe<&2, B.Got>}

def igo_get(es, tags, n, i, e, x, hx):
  match es:
    case Nil{}:
      Empty.absurd({List.get(&2, B.Got, Nil{}, e) == Some{B.Info.split.num(B.Tags.find(tags, B.Info.key(x)), x, n, i)} : Maybe<&2, B.Got>}, AT.pa_nil(e, x, hx))
    case Con{+x0, +t}:
      match e:
        case 0n:
          Equal.cong(String, Maybe<&2, B.Got>, z => Some{B.Info.split.num(B.Tags.find(tags, B.Info.key(z)), z, n, i)}, x0, x, AT.some_inj(x0, x, hx))
        case 1n+m:
          igo_get(t, tags, n, i, m, x, hx)

# A record's INFO, split at ';': its entries' results.
def ies(es: Ss(), +tags: List<&2, B.Tag>, +n: Nat, +i: Nat, +w: String,
  +h: {B.Got.join(IGO(es, tags, n, i), ";") == B.Got{w} : B.Got},
  +hes: {CH.ALLS(CH.NoC{';'}, es) == True{} : Bool},
  +hc: {ST.is_cons(es) == True{} : Bool}) ->
  {String.split(w, ';') == SM.TX(IGO(es, tags, n, i)) : Ss()}:
  match es:
    case Nil{}:
      Empty.absurd({String.split(w, ';') == SM.TX(IGO(Nil{}, tags, n, i)) : Ss()}, AB.false_ne_true(hc))
    case Con{+e, +et}:
      AT.join_sep(';', IGO(et, tags, n, i), B.Info.split.num(B.Tags.find(tags, B.Info.key(e)), e, n, i), w, h, VW.igoW(CH.NoC{';'}, Con{e, et}, tags, n, i, hes, {==}, {==}, {==}))

def ie_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +k: Nat, +a: String, +p: String,
  +hg: {B.Rec.piece(fs, a, defs, o0, n, k) == B.Got{p} : B.Got},
  +hf: {CH.ALLS(SM.TAB(), fs) == True{} : Bool},
  +ha: {CH.ALLC(SM.TAB(), a) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) ->
  {B.Info.split(B.Rec.field(fs, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(fs, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(fs, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}:
  match fs:
    case Nil{}:
      Empty.absurd({B.Info.split(B.Rec.field(Nil{}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Nil{}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Nil{}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Nil{}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Nil{}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Nil{}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Nil{}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Nil{}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Nil{}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Nil{}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Nil{}}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Nil{}}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Nil{}}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, 7n), B.Defs.info(defs), n, k) == B.Got{SI.gtext(B.Info.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, 7n), B.Defs.info(defs), n, k))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, 7n), ';'), B.Defs.info(defs), n, k)) : Ss()}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +r}}}}}}}}:
      +FS8 = SM.F8(f0, f1, f2, f3, f4, f5, f6, f7, r)
      +ks = String.split(B.Rec.field(FS8, 8n), ':')
      +GS = B.Rec.piece.go(FS8, 0n, a, defs, ks, o0, n, k)
      +ef = AT.fields_at(f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}}, a, defs, o0, n, k, p, hg, hf, ha)
      +I = B.Info.split(f7, B.Defs.info(defs), n, k)
      +eI = AT.join_nth(GS, "\t", p, hg, 7n, I, {==})
      (eI,
       {%Equal.sym(Ss(), B.Rec.fields(p), SM.TX(GS), ef) : {String.split(B.Rec.field(_, 7n), ';') == SM.TX(IGO(String.split(f7, ';'), B.Defs.info(defs), n, k)) : Ss()};
        ies(String.split(f7, ';'), B.Defs.info(defs), n, k, SI.gtext(I), eI, IK.semi_all(f7), ST.split_cons(f7, ';')) : {L.info_entries(p) == SM.TX(IGO(String.split(f7, ';'), B.Defs.info(defs), n, k)) : Ss()}})

def NUMI(+defs: B.Defs, +body: String, +i: Nat, +x: String) -> B.Got:
  B.Info.split.num(B.Tags.find(B.Defs.info(defs), B.Info.key(x)), x, L.n_alts(body), 1n+i)

def EA(+defs: B.Defs, +body: String, +i: Nat, +p: String, +e: Nat, +x: String) -> Type:
  {NUMI(defs, body, i, x) == B.Got{SI.gtext(NUMI(defs, body, i, x))} : B.Got}
  & {List.get(&2, String, L.info_entries(p), e) == Some{SI.gtext(NUMI(defs, body, i, x))} : Maybe<&2, String>}

def ea_k(+defs: B.Defs, +body: String, +i: Nat, +p: String, +e: Nat, +x: String,
  +hx: {List.get(&2, String, L.info_entries(body), e) == Some{x} : Maybe<&2, String>},
  r: {B.Info.split(B.Rec.field(AT.FS(body), 7n), B.Defs.info(defs), L.n_alts(body), 1n+i) == B.Got{SI.gtext(B.Info.split(B.Rec.field(AT.FS(body), 7n), B.Defs.info(defs), L.n_alts(body), 1n+i))} : B.Got} & {L.info_entries(p) == SM.TX(IGO(String.split(B.Rec.field(AT.FS(body), 7n), ';'), B.Defs.info(defs), L.n_alts(body), 1n+i)) : Ss()}) -> EA(defs, body, i, p, e, x):
  match r:
    case (eI, eie):
      +es = L.info_entries(body)
      +G = IGO(es, B.Defs.info(defs), L.n_alts(body), 1n+i)
      +N1 = NUMI(defs, body, i, x)
      +eg = igo_get(es, B.Defs.info(defs), L.n_alts(body), 1n+i, e, x, hx)
      (AT.join_nth(G, ";", SI.gtext(B.Info.split(B.Rec.field(AT.FS(body), 7n), B.Defs.info(defs), L.n_alts(body), 1n+i)), eI, e, N1, eg),
       {%Equal.sym(Ss(), L.info_entries(p), SM.TX(G), eie) : {List.get(&2, String, _, e) == Some{SI.gtext(N1)} : Maybe<&2, String>};
        CO.tx_get(G, e, N1, eg) : {List.get(&2, String, L.info_entries(p), e) == Some{SI.gtext(N1)} : Maybe<&2, String>}})

def ea_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +e: Nat, +x: String,
  r: AT.AT(defs, o0, body, i, p), +hl: AT.L8T(body),
  +hx: {List.get(&2, String, L.info_entries(body), e) == Some{x} : Maybe<&2, String>}) -> EA(defs, body, i, p, e, x):
  match r:
    case (+a, q):
      match q:
        case (ha, hg):
          ea_k(defs, body, i, p, e, x, hx, ie_fs(AT.FS(body), defs, o0, L.n_alts(body), 1n+i, a, p, hg, AT.fs_tab(body), AT.alt_tab(body, i, a, ha), hl))

# Entry e of the record for ALT i+1: the line's entry e, as Info.split.num
# gives it (a text).
law ent_at:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +e: Nat
  for +x: String
  for +hx: {List.get(&2, String, L.info_entries(body), e) == Some{x} : Maybe<&2, String>}
  EA(defs, body, i, p, e, x)

def ent_at(defs, o, body, ps, h, i, p, hp, e, x, hx):
  ea_at(defs, R.Opts.over0(o), body, i, p, e, x, AT.piece_at(defs, o, body, ps, h, i, p, hp), AT.parts_l8(defs, o, body, ps, h), hx)
