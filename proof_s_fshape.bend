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
import ./proof_s_col.bend as CO
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_format_shape: each sample of a record has as many values as in
# the line (none when the line has no such column). Every variable is
# reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  AB.false_ne_true(Equal.cong(B.Got, Bool, SM.is_got, B.Refuse{c}, B.Got{y}, h))

def GO(+ks: Ss(), +vs: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat) -> Gs():
  B.Fmt.split.go(ks, vs, fmt, o0, n, cp, i)

# A value results after the first: as many as the values (none refused).
def lgo.c(+k: String, +kt: Ss(), +v: String, +vt: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +w: String,
  +h: {B.Got.join(GO(Con{k, kt}, Con{v, vt}, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got},
  rec: @y: String -> {B.Got.join(GO(kt, vt, fmt, o0, n, cp, i), ":") == B.Got{y} : B.Got} -> {List.length(&2, B.Got, GO(kt, vt, fmt, o0, n, cp, i)) == List.length(&2, String, vt) : Nat}) ->
  {List.length(&2, B.Got, GO(Con{k, kt}, Con{v, vt}, fmt, o0, n, cp, i)) == List.length(&2, String, Con{v, vt}) : Nat}:
  match kt:
    case Nil{}:
      match vt:
        case Nil{}:
          {==}
        case Con{+v2, +vt2}:
          +g = B.Fmt.split.one(k, v, fmt, o0, n, cp, i)
          +J = B.Got.join(GO(Nil{}, Con{v2, vt2}, fmt, o0, n, cp, i), ":")
          +eg = AT.cat_l(g, ":", J, w, h)
          +h2 = AB.subst(B.Got, z => {B.Got.cat(z, ":", J) == B.Got{w} : B.Got}, g, B.Got{SI.gtext(g)}, eg, h)
          Empty.absurd({List.length(&2, B.Got, GO(Con{k, Nil{}}, Con{v, Con{v2, vt2}}, fmt, o0, n, cp, i)) == List.length(&2, String, Con{v, Con{v2, vt2}}) : Nat},
            ref_ne(B.BadCount{}, "", AT.cat_r(SI.gtext(g), ":", J, w, h2)))
    case Con{+k2, +kt2}:
      match vt:
        case Nil{}:
          {==}
        case Con{+v2, +vt2}:
          +g = B.Fmt.split.one(k, v, fmt, o0, n, cp, i)
          +J = B.Got.join(GO(Con{k2, kt2}, Con{v2, vt2}, fmt, o0, n, cp, i), ":")
          +eg = AT.cat_l(g, ":", J, w, h)
          +h2 = AB.subst(B.Got, z => {B.Got.cat(z, ":", J) == B.Got{w} : B.Got}, g, B.Got{SI.gtext(g)}, eg, h)
          Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Got, GO(Con{k2, kt2}, Con{v2, vt2}, fmt, o0, n, cp, i)), List.length(&2, String, Con{v2, vt2}),
            rec(SI.gtext(J), AT.cat_r(SI.gtext(g), ":", J, w, h2)))

law lgo:
  for +ks: Ss()
  for +vs: Ss()
  for +fmt: List<&2, B.Tag>
  for +o0: Bool
  for +n: Nat
  for +cp: Maybe<&2, Nat>
  for +i: Nat
  for +w: String
  for +h: {B.Got.join(GO(ks, vs, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got}
  {List.length(&2, B.Got, GO(ks, vs, fmt, o0, n, cp, i)) == List.length(&2, String, vs) : Nat}

def lgo(ks, vs, fmt, o0, n, cp, i, w, h):
  match ks vs:
    case _ Nil{}:
      {==}
    case Nil{} Con{+v, +vt}:
      Empty.absurd({List.length(&2, B.Got, GO(Nil{}, Con{v, vt}, fmt, o0, n, cp, i)) == List.length(&2, String, Con{v, vt}) : Nat}, ref_ne(B.BadCount{}, w, h))
    case Con{+k, +kt} Con{+v, +vt}:
      lgo.c(k, kt, v, vt, fmt, o0, n, cp, i, w, h, y => hy => lgo(kt, vt, fmt, o0, n, cp, i, y, hy))

def colon_all(+x: String) -> {CH.ALLS(CH.NoC{':'}, String.split(x, ':')) == True{} : Bool}:
  Equal.trans(Bool, CH.ALLS(CH.NoC{':'}, String.split(x, ':')), ST.allnoc(String.split(x, ':'), ':'), True{},
    Equal.sym(Bool, ST.allnoc(String.split(x, ':'), ':'), CH.ALLS(CH.NoC{':'}, String.split(x, ':')), SM.alls_noc(String.split(x, ':'), ':')), ST.split_all(x, ':'))

def lsplit.k(+ks: Ss(), +v: String, +vt: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +w: String,
  +h: {B.Got.join(GO(ks, Con{v, vt}, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got},
  +hv: {CH.ALLS(CH.NoC{':'}, Con{v, vt}) == True{} : Bool}) ->
  {List.length(&2, String, String.split(w, ':')) == List.length(&2, String, Con{v, vt}) : Nat}:
  match ks:
    case Nil{}:
      Empty.absurd({List.length(&2, String, String.split(w, ':')) == List.length(&2, String, Con{v, vt}) : Nat}, ref_ne(B.BadCount{}, w, h))
    case Con{+k, +kt}:
      +g = B.Fmt.split.one(k, v, fmt, o0, n, cp, i)
      +T = GO(kt, vt, fmt, o0, n, cp, i)
      %Equal.sym(Ss(), String.split(w, ':'), SM.TX(Con{g, T}), AT.join_sep(':', T, g, w, h, VW.fgoW(CH.NoC{':'}, Con{k, kt}, Con{v, vt}, fmt, o0, n, cp, i, hv, {==}))) :
        {List.length(&2, String, _) == List.length(&2, String, Con{v, vt}) : Nat}
      Equal.trans(Nat, List.length(&2, String, SM.TX(Con{g, T})), List.length(&2, B.Got, Con{g, T}), List.length(&2, String, Con{v, vt}),
        SM.len_tx(Con{g, T}), lgo(Con{k, kt}, Con{v, vt}, fmt, o0, n, cp, i, w, h))

# A sample column split by a record: as many values.
def lsplit.v(+ks: Ss(), vs: Ss(), +fmt: List<&2, B.Tag>, +o0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +w: String,
  +h: {B.Got.join(GO(ks, vs, fmt, o0, n, cp, i), ":") == B.Got{w} : B.Got},
  +hv: {CH.ALLS(CH.NoC{':'}, vs) == True{} : Bool},
  +hc: {ST.is_cons(vs) == True{} : Bool}) ->
  {List.length(&2, String, String.split(w, ':')) == List.length(&2, String, vs) : Nat}:
  match vs:
    case Nil{}:
      Empty.absurd({List.length(&2, String, String.split(w, ':')) == List.length(&2, String, Nil{}) : Nat}, AB.false_ne_true(hc))
    case Con{+v, +vt}:
      lsplit.k(ks, v, vt, fmt, o0, n, cp, i, w, h, hv)

def LEN(+p: String, +body: String, +s: Nat) -> Type:
  {L.len_of(L.sample_column(p, s)) == L.len_of(L.sample_column(body, s)) : Maybe<&2, Nat>}

def fs_some(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +col: String,
  +em: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == Some{col} : Maybe<&2, String>},
  c: CO.CS(defs, o0, body, i, p, s, col)) -> LEN(p, body, s):
  match c:
    case (eF, ec):
      +F = CO.FT(defs, o0, body, i, col)
      +ks = AT.KS(body)
      +vs = String.split(col, ':')
      {%Equal.sym(Maybe<&2, Ss()>, L.sample_column(p, s), Some{String.split(SI.gtext(F), ':')}, ec) : {L.len_of(_) == L.len_of(L.sample_column(body, s)) : Maybe<&2, Nat>};
       %Equal.sym(Maybe<&2, String>, List.get(&2, String, AT.FS(body), Nat.add(9n, s)), Some{col}, em) : {L.len_of(Some{String.split(SI.gtext(F), ':')}) == L.len_of(L.column_values(_)) : Maybe<&2, Nat>};
       Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, List.length(&2, String, String.split(SI.gtext(F), ':')), List.length(&2, String, vs),
         lsplit.v(ks, vs, B.Defs.fmt(defs), o0, L.n_alts(body), B.Gt.copies(B.Fmt.gt(ks, vs)), 1n+i, SI.gtext(F), eF, colon_all(col), ST.split_cons(col, ':'))) :
       LEN(p, body, s)}

def fs_m(m: Maybe<&2, String>, +defs: B.Defs, +o: B.Opts, +body: String, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts},
  +i: Nat, +p: String, +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}, +s: Nat,
  +em: {List.get(&2, String, AT.FS(body), Nat.add(9n, s)) == m : Maybe<&2, String>}) -> LEN(p, body, s):
  match m:
    case None{}:
      {%Equal.sym(Maybe<&2, Ss()>, L.sample_column(p, s), None{}, CO.col_none(defs, o, body, ps, h, i, p, hp, s, em)) : {L.len_of(_) == L.len_of(L.sample_column(body, s)) : Maybe<&2, Nat>};
       %Equal.sym(Maybe<&2, String>, List.get(&2, String, AT.FS(body), Nat.add(9n, s)), None{}, em) : {L.len_of(None{}) == L.len_of(L.column_values(_)) : Maybe<&2, Nat>};
       {==} : LEN(p, body, s)}
    case Some{+col}:
      fs_some(defs, R.Opts.over0(o), body, i, p, s, col, em, CO.col_at(defs, o, body, ps, h, i, p, hp, s, col, em))

# Law split_format_shape: each sample has as many values as in the input
# (none when the line has no such column).
law split_format_shape:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  LEN(p, body, s)

def split_format_shape(defs, o, body, ps, h, i, p, hp, s):
  fs_m(List.get(&2, String, AT.FS(body), Nat.add(9n, s)), defs, o, body, ps, h, i, p, hp, s, {==})
