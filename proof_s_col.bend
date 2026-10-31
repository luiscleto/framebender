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
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# A record's fields by place, and its sample columns: sample s's column in
# the record for ALT i is B.Fmt.split of the line's. Every variable is
# reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def none_s(+x: String, +h: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  AT.none_some(x, h)

# Field k of fields fs: piece.go gives its result there.
law pg_get:
  for +fs: Ss()
  for +j: Nat
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +k: Nat
  for +f: String
  for +hf: {List.get(&2, String, fs, k) == Some{f} : Maybe<&2, String>}
  {List.get(&2, B.Got, B.Rec.piece.go(fs, j, a, defs, ks, o0, n, i), k) == Some{B.Rec.piece.field(Nat.add(k, j), f, a, defs, ks, o0, n, i)} : Maybe<&2, B.Got>}

def pg_get(fs, j, a, defs, ks, o0, n, i, k, f, hf):
  match fs:
    case Nil{}:
      Empty.absurd({List.get(&2, B.Got, Nil{}, k) == Some{B.Rec.piece.field(Nat.add(k, j), f, a, defs, ks, o0, n, i)} : Maybe<&2, B.Got>}, AT.pa_nil(k, f, hf))
    case Con{+g, +t}:
      match k:
        case 0n:
          Equal.cong(String, Maybe<&2, B.Got>, z => Some{B.Rec.piece.field(j, z, a, defs, ks, o0, n, i)}, g, f, AT.some_inj(g, f, hf))
        case 1n+m:
          %N.add_succ(m, j) : {List.get(&2, B.Got, B.Rec.piece.go(t, 1n+j, a, defs, ks, o0, n, i), m) == Some{B.Rec.piece.field(_, f, a, defs, ks, o0, n, i)} : Maybe<&2, B.Got>}
          pg_get(t, 1n+j, a, defs, ks, o0, n, i, m, f, hf)

law pg_none:
  for +fs: Ss()
  for +j: Nat
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +k: Nat
  for +hf: {List.get(&2, String, fs, k) == None{} : Maybe<&2, String>}
  {List.get(&2, B.Got, B.Rec.piece.go(fs, j, a, defs, ks, o0, n, i), k) == None{} : Maybe<&2, B.Got>}

def pg_none(fs, j, a, defs, ks, o0, n, i, k, hf):
  match fs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case Con{+g, +t}:
      match k:
        case 0n:
          Empty.absurd({List.get(&2, B.Got, B.Rec.piece.go(Con{g, t}, j, a, defs, ks, o0, n, i), 0n) == None{} : Maybe<&2, B.Got>}, none_s(g, Equal.sym(Maybe<&2, String>, Some{g}, None{}, hf)))
        case 1n+m:
          pg_none(t, 1n+j, a, defs, ks, o0, n, i, m, hf)

law tx_get:
  for +gs: Gs()
  for +k: Nat
  for +g: B.Got
  for +h: {List.get(&2, B.Got, gs, k) == Some{g} : Maybe<&2, B.Got>}
  {List.get(&2, String, SM.TX(gs), k) == Some{SI.gtext(g)} : Maybe<&2, String>}

def tx_get(gs, k, g, h):
  match gs:
    case Nil{}:
      Empty.absurd({List.get(&2, String, Nil{}, k) == Some{SI.gtext(g)} : Maybe<&2, String>}, AT.jn_nil(k, g, h))
    case Con{+g0, +t}:
      match k:
        case 0n:
          Equal.cong(B.Got, Maybe<&2, String>, z => Some{SI.gtext(z)}, g0, g, AT.some_g(g0, g, h))
        case 1n+m:
          tx_get(t, m, g, h)

law tx_none:
  for +gs: Gs()
  for +k: Nat
  for +h: {List.get(&2, B.Got, gs, k) == None{} : Maybe<&2, B.Got>}
  {List.get(&2, String, SM.TX(gs), k) == None{} : Maybe<&2, String>}

def tx_none(gs, k, h):
  match gs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case Con{+g0, +t}:
      match k:
        case 0n:
          Empty.absurd({List.get(&2, String, SM.TX(Con{g0, t}), 0n) == None{} : Maybe<&2, String>}, AT.none_g(g0, Equal.sym(Maybe<&2, B.Got>, Some{g0}, None{}, h)))
        case 1n+m:
          tx_none(t, m, h)

# A sample's field (place 9 + s): its column split as B.Fmt.split says.
def pf9(+s: Nat, +col: String, +a: String, +defs: B.Defs, +ks: Ss(), +o0: Bool, +n: Nat, +i: Nat) ->
  {B.Rec.piece.field(Nat.add(Nat.add(9n, s), 0n), col, a, defs, ks, o0, n, i) == B.Fmt.split(ks, col, B.Defs.fmt(defs), o0, n, i) : B.Got}:
  %Equal.sym(Nat, Nat.add(Nat.add(9n, s), 0n), Nat.add(9n, s), N.add_zero(Nat.add(9n, s))) : {B.Rec.piece.field(_, col, a, defs, ks, o0, n, i) == B.Fmt.split(ks, col, B.Defs.fmt(defs), o0, n, i) : B.Got}
  %Equal.sym(Bool, Nat.is_le(0n, s), True{}, N.le_zero_l(s)) :
    {Bool.pick(B.Got, _, B.Fmt.split(ks, col, B.Defs.fmt(defs), o0, n, i), B.Got{col}) == B.Fmt.split(ks, col, B.Defs.fmt(defs), o0, n, i) : B.Got}
  {==}

# Sample s's column in a record: the line's, split.
def FT(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +col: String) -> B.Got:
  B.Fmt.split(AT.KS(body), col, B.Defs.fmt(defs), o0, L.n_alts(body), 1n+i)

def CS(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +col: String) -> Type:
  {FT(defs, o0, body, i, col) == B.Got{SI.gtext(FT(defs, o0, body, i, col))} : B.Got}
  & {L.sample_column(p, s) == Some{String.split(SI.gtext(FT(defs, o0, body, i, col)), ':')} : Maybe<&2, Ss()>}

def ca_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +k: Nat, +a: String, +p: String, +s: Nat, +col: String,
  +hg: {B.Rec.piece(fs, a, defs, o0, n, k) == B.Got{p} : B.Got},
  +hf: {CH.ALLS(SM.TAB(), fs) == True{} : Bool},
  +ha: {CH.ALLC(SM.TAB(), a) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool},
  +hc: {List.get(&2, String, fs, Nat.add(9n, s)) == Some{col} : Maybe<&2, String>}) ->
  {B.Fmt.split(String.split(B.Rec.field(fs, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k) == B.Got{SI.gtext(B.Fmt.split(String.split(B.Rec.field(fs, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k))} : B.Got}
  & {L.sample_column(p, s) == Some{String.split(SI.gtext(B.Fmt.split(String.split(B.Rec.field(fs, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k)), ':')} : Maybe<&2, Ss()>}:
  match fs:
    case Nil{}:
      Empty.absurd({B.Fmt.split(String.split(B.Rec.field(Nil{}, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k) == B.Got{SI.gtext(B.Fmt.split(String.split(B.Rec.field(Nil{}, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k))} : B.Got}
        & {L.sample_column(p, s) == Some{String.split(SI.gtext(B.Fmt.split(String.split(B.Rec.field(Nil{}, 8n), ':'), col, B.Defs.fmt(defs), o0, n, k)), ':')} : Maybe<&2, Ss()>}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, +r}:
      +ks = String.split(B.Rec.field(Con{f0, r}, 8n), ':')
      +F = B.Fmt.split(ks, col, B.Defs.fmt(defs), o0, n, k)
      +GS = B.Rec.piece.go(Con{f0, r}, 0n, a, defs, ks, o0, n, k)
      +ef = AT.fields_at(f0, r, a, defs, o0, n, k, p, hg, hf, ha)
      +eg0 = pg_get(Con{f0, r}, 0n, a, defs, ks, o0, n, k, Nat.add(9n, s), col, hc)
      +eg = Equal.trans(Maybe<&2, B.Got>, List.get(&2, B.Got, GS, Nat.add(9n, s)), Some{B.Rec.piece.field(Nat.add(Nat.add(9n, s), 0n), col, a, defs, ks, o0, n, k)}, Some{F}, eg0,
        Equal.cong(B.Got, Maybe<&2, B.Got>, z => Some{z}, B.Rec.piece.field(Nat.add(Nat.add(9n, s), 0n), col, a, defs, ks, o0, n, k), F, pf9(s, col, a, defs, ks, o0, n, k)))
      +et = tx_get(GS, Nat.add(9n, s), F, eg)
      (AT.join_nth(GS, "\t", p, hg, Nat.add(9n, s), F, eg),
       {%Equal.sym(Ss(), B.Rec.fields(p), SM.TX(GS), ef) : {L.column_values(List.get(&2, String, _, Nat.add(9n, s))) == Some{String.split(SI.gtext(F), ':')} : Maybe<&2, Ss()>};
        %Equal.sym(Maybe<&2, String>, List.get(&2, String, SM.TX(GS), Nat.add(9n, s)), Some{SI.gtext(F)}, et) : {L.column_values(_) == Some{String.split(SI.gtext(F), ':')} : Maybe<&2, Ss()>};
        {==} : {L.sample_column(p, s) == Some{String.split(SI.gtext(F), ':')} : Maybe<&2, Ss()>}})

def ca_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +col: String,
  r: AT.AT(defs, o0, body, i, p), +hl: AT.L8T(body),
  +hc: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == Some{col} : Maybe<&2, String>}) -> CS(defs, o0, body, i, p, s, col):
  match r:
    case (+a, q):
      match q:
        case (ha, hg):
          ca_fs(AT.FS(body), defs, o0, L.n_alts(body), 1n+i, a, p, s, col, hg, AT.fs_tab(body), AT.alt_tab(body, i, a, ha), hl, hc)

# Sample s's column in the record for ALT i+1 (the line has one).
law col_at:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +col: String
  for +hc: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == Some{col} : Maybe<&2, String>}
  CS(defs, R.Opts.over0(o), body, i, p, s, col)

def col_at(defs, o, body, ps, h, i, p, hp, s, col, hc):
  ca_at(defs, R.Opts.over0(o), body, i, p, s, col, AT.piece_at(defs, o, body, ps, h, i, p, hp), AT.parts_l8(defs, o, body, ps, h), hc)

def cn_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +k: Nat, +a: String, +p: String, +s: Nat,
  +hg: {B.Rec.piece(fs, a, defs, o0, n, k) == B.Got{p} : B.Got},
  +hf: {CH.ALLS(SM.TAB(), fs) == True{} : Bool},
  +ha: {CH.ALLC(SM.TAB(), a) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool},
  +hc: {List.get(&2, String, fs, Nat.add(9n, s)) == None{} : Maybe<&2, String>}) ->
  {L.sample_column(p, s) == None{} : Maybe<&2, Ss()>}:
  match fs:
    case Nil{}:
      Empty.absurd({L.sample_column(p, s) == None{} : Maybe<&2, Ss()>}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, +r}:
      +ks = String.split(B.Rec.field(Con{f0, r}, 8n), ':')
      +GS = B.Rec.piece.go(Con{f0, r}, 0n, a, defs, ks, o0, n, k)
      +ef = AT.fields_at(f0, r, a, defs, o0, n, k, p, hg, hf, ha)
      +et = tx_none(GS, Nat.add(9n, s), pg_none(Con{f0, r}, 0n, a, defs, ks, o0, n, k, Nat.add(9n, s), hc))
      {%Equal.sym(Ss(), B.Rec.fields(p), SM.TX(GS), ef) : {L.column_values(List.get(&2, String, _, Nat.add(9n, s))) == None{} : Maybe<&2, Ss()>};
       %Equal.sym(Maybe<&2, String>, List.get(&2, String, SM.TX(GS), Nat.add(9n, s)), None{}, et) : {L.column_values(_) == None{} : Maybe<&2, Ss()>};
       {==} : {L.sample_column(p, s) == None{} : Maybe<&2, Ss()>}}

def cn_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat,
  r: AT.AT(defs, o0, body, i, p), +hl: AT.L8T(body),
  +hc: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == None{} : Maybe<&2, String>}) -> {L.sample_column(p, s) == None{} : Maybe<&2, Ss()>}:
  match r:
    case (+a, q):
      match q:
        case (ha, hg):
          cn_fs(AT.FS(body), defs, o0, L.n_alts(body), 1n+i, a, p, s, hg, AT.fs_tab(body), AT.alt_tab(body, i, a, ha), hl, hc)

# No such column in the line: none in the record.
law col_none:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +hc: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == None{} : Maybe<&2, String>}
  {L.sample_column(p, s) == None{} : Maybe<&2, Ss()>}

def col_none(defs, o, body, ps, h, i, p, hp, s, hc):
  cn_at(defs, R.Opts.over0(o), body, i, p, s, AT.piece_at(defs, o, body, ps, h, i, p, hp), AT.parts_l8(defs, o, body, ps, h), hc)

def GO(+ks: Ss(), +vs: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat) -> Gs():
  B.Fmt.split.go(ks, vs, fmt, o0, n, cp, i)

# Key j and value j of a column: Fmt.split.go's result j is theirs.
law go_get:
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +o0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +j: Nat
  for +k: String
  for +v: String
  for +hk: {List.get(&2, String, ks, j) == Some{k} : Maybe<&2, String>}
  for +hv: {List.get(&2, String, vs, j) == Some{v} : Maybe<&2, String>}
  {List.get(&2, B.Got, GO(ks, vs, fmt, o0, n, cp, i), j) == Some{B.Fmt.split.one(k, v, fmt, o0, n, cp, i)} : Maybe<&2, B.Got>}

def go_get(ks, vs, fmt, o0, n, cp, i, j, k, v, hk, hv):
  match ks vs:
    case _ Nil{}:
      Empty.absurd({List.get(&2, B.Got, GO(ks, Nil{}, fmt, o0, n, cp, i), j) == Some{B.Fmt.split.one(k, v, fmt, o0, n, cp, i)} : Maybe<&2, B.Got>}, AT.pa_nil(j, v, hv))
    case Nil{} Con{+v0, +vt}:
      Empty.absurd({List.get(&2, B.Got, GO(Nil{}, Con{v0, vt}, fmt, o0, n, cp, i), j) == Some{B.Fmt.split.one(k, v, fmt, o0, n, cp, i)} : Maybe<&2, B.Got>}, AT.pa_nil(j, k, hk))
    case Con{+k0, +kt} Con{+v0, +vt}:
      match j:
        case 0n:
          +ek = AT.some_inj(k0, k, hk)
          +ev = AT.some_inj(v0, v, hv)
          %Equal.sym(String, k0, k, ek) : {Some{B.Fmt.split.one(_, v0, fmt, o0, n, cp, i)} == Some{B.Fmt.split.one(k, v, fmt, o0, n, cp, i)} : Maybe<&2, B.Got>}
          %Equal.sym(String, v0, v, ev) : {Some{B.Fmt.split.one(k, _, fmt, o0, n, cp, i)} == Some{B.Fmt.split.one(k, v, fmt, o0, n, cp, i)} : Maybe<&2, B.Got>}
          {==}
        case 1n+m:
          go_get(kt, vt, fmt, o0, n, cp, i, m, k, v, hk, hv)

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  AB.false_ne_true(Equal.cong(B.Got, Bool, SM.is_got, B.Refuse{c}, B.Got{y}, h))

def colon_all(+x: String) -> {CH.ALLS(CH.NoC{':'}, String.split(x, ':')) == True{} : Bool}:
  Equal.trans(Bool, CH.ALLS(CH.NoC{':'}, String.split(x, ':')), ST.allnoc(String.split(x, ':'), ':'), True{},
    Equal.sym(Bool, ST.allnoc(String.split(x, ':'), ':'), CH.ALLS(CH.NoC{':'}, String.split(x, ':')), SM.alls_noc(String.split(x, ':'), ':')), ST.split_all(x, ':'))

def sp_go.k(+ks: Ss(), +v: String, +vt: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +w: String,
  +h: {B.Got.join(GO(ks, Con{v, vt}, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got},
  +hv: {CH.ALLS(CH.NoC{':'}, Con{v, vt}) == True{} : Bool}) ->
  {String.split(w, ':') == SM.TX(GO(ks, Con{v, vt}, fmt, o0, n, cp, i)) : Ss()}:
  match ks:
    case Nil{}:
      Empty.absurd({String.split(w, ':') == SM.TX(GO(Nil{}, Con{v, vt}, fmt, o0, n, cp, i)) : Ss()}, ref_ne(B.BadCount{}, w, h))
    case Con{+k, +kt}:
      AT.join_sep(':', GO(kt, vt, fmt, o0, n, cp, i), B.Fmt.split.one(k, v, fmt, o0, n, cp, i), w, h, VW.fgoW(CH.NoC{':'}, Con{k, kt}, Con{v, vt}, fmt, o0, n, cp, i, hv, {==}))

# A record's column, split at ':': its value results' texts.
def sp_go(+ks: Ss(), vs: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +w: String,
  +h: {B.Got.join(GO(ks, vs, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got},
  +hv: {CH.ALLS(CH.NoC{':'}, vs) == True{} : Bool},
  +hc: {ST.is_cons(vs) == True{} : Bool}) ->
  {String.split(w, ':') == SM.TX(GO(ks, vs, fmt, o0, n, cp, i)) : Ss()}:
  match vs:
    case Nil{}:
      Empty.absurd({String.split(w, ':') == SM.TX(GO(ks, Nil{}, fmt, o0, n, cp, i)) : Ss()}, AB.false_ne_true(hc))
    case Con{+v, +vt}:
      sp_go.k(ks, v, vt, fmt, o0, n, cp, i, w, h, hv)

# Sample s's value for key j in the record for ALT i+1: Fmt.split.one of the
# line's key and value, a text.
def CP(+body: String, +col: String) -> Maybe<&2, Nat>:
  B.Gt.copies(B.Fmt.gt(AT.KS(body), String.split(col, ':')))

def ONE(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +col: String, +k: String, +v: String) -> B.Got:
  B.Fmt.split.one(k, v, B.Defs.fmt(defs), o0, L.n_alts(body), CP(body, col), 1n+i)

def VA(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +k: String, +v: String) -> Type:
  &col: String -> ({List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == Some{col} : Maybe<&2, String>}
    & ({ONE(defs, o0, body, i, col, k, v) == B.Got{SI.gtext(ONE(defs, o0, body, i, col, k, v))} : B.Got}
    & {L.sample_at(p, s, j) == Some{SI.gtext(ONE(defs, o0, body, i, col, k, v))} : Maybe<&2, String>}))

def va_some(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +k: String, +v: String, +col: String,
  +em: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == Some{col} : Maybe<&2, String>},
  +hk: {List.get(&2, String, L.format_keys(body), j) == Some{k} : Maybe<&2, String>},
  +hv: {List.get(&2, String, String.split(col, ':'), j) == Some{v} : Maybe<&2, String>},
  c: CS(defs, o0, body, i, p, s, col)) -> VA(defs, o0, body, i, p, s, j, k, v):
  match c:
    case (+eF, +ec):
      +F = FT(defs, o0, body, i, col)
      +ks = AT.KS(body)
      +vs = String.split(col, ':')
      +G = GO(ks, vs, B.Defs.fmt(defs), o0, L.n_alts(body), CP(body, col), 1n+i)
      +O = ONE(defs, o0, body, i, col, k, v)
      +eg = go_get(ks, vs, B.Defs.fmt(defs), o0, L.n_alts(body), CP(body, col), 1n+i, j, k, v, hk, hv)
      +es = sp_go(ks, vs, B.Defs.fmt(defs), o0, L.n_alts(body), CP(body, col), 1n+i, SI.gtext(F), eF, colon_all(col), ST.split_cons(col, ':'))
      (col, (em, (AT.join_nth(G, ":", SI.gtext(F), eF, j, O, eg),
        {%Equal.sym(Maybe<&2, Ss()>, L.sample_column(p, s), Some{String.split(SI.gtext(F), ':')}, ec) : {L.sample_at.of(_, j) == Some{SI.gtext(O)} : Maybe<&2, String>};
         %Equal.sym(Ss(), String.split(SI.gtext(F), ':'), SM.TX(G), es) : {List.get(&2, String, _, j) == Some{SI.gtext(O)} : Maybe<&2, String>};
         tx_get(G, j, O, eg) : {L.sample_at(p, s, j) == Some{SI.gtext(O)} : Maybe<&2, String>}})))

def va_m(m: Maybe<&2, String>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts},
  +i: Nat, +p: String, +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}, +s: Nat, +j: Nat, +k: String, +v: String,
  +hk: {List.get(&2, String, L.format_keys(body), j) == Some{k} : Maybe<&2, String>},
  +hv: {L.sample_at(body, s, j) == Some{v} : Maybe<&2, String>},
  +em: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == m : Maybe<&2, String>}) -> VA(defs, R.Opts.over0(o), body, i, p, s, j, k, v):
  match m:
    case None{}:
      +hv2 = {%em : {L.sample_at.of(L.column_values(_), j) == Some{v} : Maybe<&2, String>}; hv : {L.sample_at.of(L.column_values(None{}), j) == Some{v} : Maybe<&2, String>}}
      Empty.absurd(VA(defs, R.Opts.over0(o), body, i, p, s, j, k, v), AT.none_some(v, hv2))
    case Some{+col}:
      +hv2 = {%em : {L.sample_at.of(L.column_values(_), j) == Some{v} : Maybe<&2, String>}; hv : {List.get(&2, String, String.split(col, ':'), j) == Some{v} : Maybe<&2, String>}}
      va_some(defs, R.Opts.over0(o), body, i, p, s, j, k, v, col, em, hk, hv2, col_at(defs, o, body, ps, h, i, p, hp, s, col, em))

law val_at:
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
  for +v: String
  for +hv: {L.sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
  VA(defs, R.Opts.over0(o), body, i, p, s, j, k, v)

def val_at(defs, o, body, ps, h, i, p, hp, s, j, k, hk, v, hv):
  va_m(List.get(&2, String, AT.FS(body), Nat.add(9n, s)), defs, o, body, ps, h, i, p, hp, s, j, k, v, hk, hv, {==})
