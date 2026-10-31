import Base
import ./types.bend as B
import ./proof_s_cr.bend as CR
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_chars.bend as CH
import ./proof_s_same.bend as SM
import ./proof_run_text.bend as RT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# The record for ALT i+1 of a split line (B.Rec.parts' Pieces, i from 0):
# B.Rec.piece of the line's fields and that ALT, and its fields are the texts
# B.Rec.piece.go gives field by field. The laws on what a record holds
# (split_info_*, split_format_*, split_gt, split_phase) start here. Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def FS(+body: String) -> Ss():
  B.Rec.fields(body)

def ALTS(+body: String) -> Ss():
  B.Rec.alts(B.Rec.fields(body))

def KS(+body: String) -> Ss():
  String.split(B.Rec.field(B.Rec.fields(body), 8n), ':')

# The record's text, and its ALT.
def AT(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String) -> Type:
  &a: String -> ({List.get(&2, String, ALTS(body), i) == Some{a} : Maybe<&2, String>}
    & {B.Rec.piece(FS(body), a, defs, o0, L.n_alts(body), 1n+i) == B.Got{p} : B.Got})

# ---------------------------------------------------------------------------
# From Pieces to the records of the ALTs
# ---------------------------------------------------------------------------

def PG(+defs: B.Defs, +o0: Bool, +body: String, +ps: Ss()) -> Type:
  {B.Parts.of(B.Rec.pieces.go(ALTS(body), FS(body), defs, o0, L.n_alts(body), 1n)) == B.Pieces{ps} : B.Parts}

def pg_split(+d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(ALTS(body)) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(ALTS(body)), ALTS(body), FS(body), defs, o0) == B.Pieces{ps} : B.Parts}) ->
  PG(defs, o0, body, ps):
  match d:
    case False{}:
      +h2 = {%ed : {B.Rec.parts.split(_, ALTS(body), FS(body), defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, ALTS(body), FS(body), defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(PG(defs, o0, body, ps), AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      {%ed : {B.Rec.parts.split(_, ALTS(body), FS(body), defs, o0) == B.Pieces{ps} : B.Parts}; h : PG(defs, o0, body, ps)}

def pg_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {SI.COND(sp, FS(body)) == c : Bool},
  +h: {B.Rec.parts.if(SI.COND(sp, FS(body)), False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}) ->
  PG(defs, o0, body, ps):
  match c:
    case False{}:
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(PG(defs, o0, body, ps), AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}}
      pg_split(B.Alts.distinct(ALTS(body)), defs, o0, body, ps, {==}, h2)

# Pieces come from the records of the ALTs, in order, from ALT 1.
law parts_pg:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  PG(defs, R.Opts.over0(o), body, ps)

def parts_pg(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      pg_if(SI.COND(sp, FS(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(SI.COND(sp, FS(body)), B.Text.has_cr(body), defs, o0, FS(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))

# ---------------------------------------------------------------------------
# The record at place i
# ---------------------------------------------------------------------------

def none_some(+p: String, +h: {None{} == Some{p} : Maybe<&2, String>}) -> Empty:
  AB.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{p}, h))

def some_inj(+x: String, +y: String, +h: {Some{x} == Some{y} : Maybe<&2, String>}) -> {x == y : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, x), Some{x}, Some{y}, h)

def pa_nil(+i: Nat, +p: String, +h: {List.get(&2, String, Nil{}, i) == Some{p} : Maybe<&2, String>}) -> Empty:
  match i:
    case 0n:
      none_some(p, h)
    case 1n+k:
      none_some(p, h)

def ATJ(+alts: Ss(), +fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +j: Nat, +i: Nat, +p: String) -> Type:
  &a: String -> ({List.get(&2, String, alts, i) == Some{a} : Maybe<&2, String>}
    & {B.Rec.piece(fs, a, defs, o0, n, Nat.add(i, j)) == B.Got{p} : B.Got})

# One place further: the next ALT's record is ALT j + 1 + k.
def pa_succ(+a: String, +t: Ss(), +fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +j: Nat, +k: Nat, +p: String,
  r: ATJ(t, fs, defs, o0, n, 1n+j, k, p)) -> ATJ(Con{a, t}, fs, defs, o0, n, j, 1n+k, p):
  match r:
    case (+b, q):
      match q:
        case (hb, hg):
          (b, (hb, {%N.add_succ(k, j) : {B.Rec.piece(fs, b, defs, o0, n, _) == B.Got{p} : B.Got};
            hg : {B.Rec.piece(fs, b, defs, o0, n, 1n+Nat.add(k, j)) == B.Got{p} : B.Got}}))

def pa_cons(+i: Nat, +a: String, +t: Ss(), +fs: Ss(), +defs: B.Defs, +o0: Bool, +n: Nat, +j: Nat, +g: B.Got, +r: B.Parts, +p: String,
  +eg: {g == B.Got{SI.gtext(g)} : B.Got},
  +hr: {r == B.Pieces{SI.pieces_of(r)} : B.Parts},
  +hp: {List.get(&2, String, SI.gtext(g) <> SI.pieces_of(r), i) == Some{p} : Maybe<&2, String>},
  rec: @k: Nat -> {List.get(&2, String, SI.pieces_of(r), k) == Some{p} : Maybe<&2, String>} -> ATJ(t, fs, defs, o0, n, 1n+j, k, p)) ->
  {g == B.Rec.piece(fs, a, defs, o0, n, j) : B.Got} -> ATJ(Con{a, t}, fs, defs, o0, n, j, i, p):
  match i:
    case 0n:
      eb => (a, ({==}, Equal.trans(B.Got, B.Rec.piece(fs, a, defs, o0, n, j), g, B.Got{p}, Equal.sym(B.Got, g, B.Rec.piece(fs, a, defs, o0, n, j), eb),
        Equal.trans(B.Got, g, B.Got{SI.gtext(g)}, B.Got{p}, eg, Equal.cong(String, B.Got, x => B.Got{x}, SI.gtext(g), p, some_inj(SI.gtext(g), p, hp))))))
    case 1n+k:
      eb => pa_succ(a, t, fs, defs, o0, n, j, k, p, rec(k, hp))

# The record at place i of the records of alts from ALT j: the record of
# alts' i-th ALT, as ALT j + i.
law pieces_at:
  for +alts: Ss()
  for +fs: Ss()
  for +defs: B.Defs
  for +o0: Bool
  for +n: Nat
  for +j: Nat
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, fs, defs, o0, n, j)) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  ATJ(alts, fs, defs, o0, n, j, i, p)

def pieces_at(alts, fs, defs, o0, n, j, ps, h, i, p, hp):
  match alts:
    case Nil{}:
      +e0 = Equal.cong(B.Parts, Ss(), SI.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h)
      +hp0 = {%Equal.sym(Ss(), Nil{}, ps, e0) : {List.get(&2, String, _, i) == Some{p} : Maybe<&2, String>}; hp : {List.get(&2, String, Nil{}, i) == Some{p} : Maybe<&2, String>}}
      Empty.absurd(ATJ(Nil{}, fs, defs, o0, n, j, i, p), pa_nil(i, p, hp0))
    case Con{+a, +t}:
      +g = B.Rec.piece(fs, a, defs, o0, n, j)
      +r = B.Parts.of(B.Rec.pieces.go(t, fs, defs, o0, n, 1n+j))
      +eg = SI.pc_g(g, r, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{SI.gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
      +eps = SI.pc_ps(SI.gtext(g), r, ps, h2g)
      +hp2 = {%eps : {List.get(&2, String, _, i) == Some{p} : Maybe<&2, String>}; hp : {List.get(&2, String, SI.gtext(g) <> SI.pieces_of(r), i) == Some{p} : Maybe<&2, String>}}
      pa_cons(i, a, t, fs, defs, o0, n, j, g, r, p, eg, SI.pc_r(SI.gtext(g), r, ps, h2g), hp2,
        k => hk => pieces_at(t, fs, defs, o0, n, 1n+j, SI.pieces_of(r), SI.pc_r(SI.gtext(g), r, ps, h2g), k, p, hk), {==})

# The record at place i of a split line: the record of ALT i+1.
law piece_at:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  AT(defs, R.Opts.over0(o), body, i, p)

def at_k(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String,
  r: ATJ(ALTS(body), FS(body), defs, o0, L.n_alts(body), 1n, i, p)) -> AT(defs, o0, body, i, p):
  match r:
    case (+a, q):
      match q:
        case (ha, hg):
          (a, (ha, {%N.add_one(i) : {B.Rec.piece(FS(body), a, defs, o0, L.n_alts(body), _) == B.Got{p} : B.Got};
            hg : {B.Rec.piece(FS(body), a, defs, o0, L.n_alts(body), 1n+i) == B.Got{p} : B.Got}}))

def piece_at(defs, o, body, ps, h, i, p, hp):
  at_k(defs, R.Opts.over0(o), body, i, p,
    pieces_at(ALTS(body), FS(body), defs, R.Opts.over0(o), L.n_alts(body), 1n, ps, parts_pg(defs, o, body, ps, h), i, p, hp))

# ---------------------------------------------------------------------------
# Joined results
# ---------------------------------------------------------------------------

def cat_l(+a: B.Got, +sep: String, +b: B.Got, +x: String, +h: {B.Got.cat(a, sep, b) == B.Got{x} : B.Got}) -> {a == B.Got{SI.gtext(a)} : B.Got}:
  match a:
    case B.Got{+y}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Got, Bool, SM.is_got, B.Refuse{c}, B.Got{x}, h)))

def cat_r(+y: String, +sep: String, +b: B.Got, +x: String, +h: {B.Got.cat(B.Got{y}, sep, b) == B.Got{x} : B.Got}) -> {b == B.Got{SI.gtext(b)} : B.Got}:
  match b:
    case B.Got{+w}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Got, Bool, SM.is_got, B.Refuse{c}, B.Got{x}, h)))

def cat_y(+y: String, +sep: String, +b: B.Got, +x: String, +h: {B.Got.cat(B.Got{y}, sep, b) == B.Got{x} : B.Got}) -> {x == String.append(y, String.append(sep, SI.gtext(b))) : String}:
  match b:
    case B.Got{+w}:
      Equal.sym(String, String.append(y, String.append(sep, w)), x, Equal.cong(B.Got, String, SI.gtext, B.Got{String.append(y, String.append(sep, w))}, B.Got{x}, h))
    case B.Refuse{+c}:
      Empty.absurd({x == String.append(y, String.append(sep, "")) : String}, AB.false_ne_true(Equal.cong(B.Got, Bool, SM.is_got, B.Refuse{c}, B.Got{x}, h)))

def some_g(+g: B.Got, +h: B.Got, +e: {Some{g} == Some{h} : Maybe<&2, B.Got>}) -> {g == h : B.Got}:
  Equal.cong(Maybe<&2, B.Got>, B.Got, m => Maybe.default(&2, B.Got, m, g), Some{g}, Some{h}, e)

def none_g(+g: B.Got, +e: {None{} == Some{g} : Maybe<&2, B.Got>}) -> Empty:
  AB.false_ne_true(Equal.cong(Maybe<&2, B.Got>, Bool, m => Maybe.is_some(&2, B.Got, m), None{}, Some{g}, e))

def jn_nil(+j: Nat, +g: B.Got, +h: {List.get(&2, B.Got, Nil{}, j) == Some{g} : Maybe<&2, B.Got>}) -> Empty:
  match j:
    case 0n:
      none_g(g, h)
    case 1n+k:
      none_g(g, h)

def jn_cons(+t: Gs(), +g0: B.Got, +sep: String, +x: String,
  +h: {B.Got.join(Con{g0, t}, sep) == B.Got{x} : B.Got},
  +j: Nat, +g: B.Got,
  +hj: {List.get(&2, B.Got, Con{g0, t}, j) == Some{g} : Maybe<&2, B.Got>},
  rec: @k: Nat -> @y: String -> {B.Got.join(t, sep) == B.Got{y} : B.Got} -> @g2: B.Got -> {List.get(&2, B.Got, t, k) == Some{g2} : Maybe<&2, B.Got>} -> {g2 == B.Got{SI.gtext(g2)} : B.Got}) ->
  {g == B.Got{SI.gtext(g)} : B.Got}:
  match t:
    case Nil{}:
      match j:
        case 0n:
          +e = some_g(g0, g, hj)
          {%e : {_ == B.Got{SI.gtext(_)} : B.Got}; SM.got_self(g0, x, h) : {g == B.Got{SI.gtext(g)} : B.Got}}
        case 1n+k:
          Empty.absurd({g == B.Got{SI.gtext(g)} : B.Got}, jn_nil(k, g, hj))
    case Con{+g1, +t1}:
      match j:
        case 0n:
          +J = B.Got.join(Con{g1, t1}, sep)
          +e = some_g(g0, g, hj)
          {%e : {_ == B.Got{SI.gtext(_)} : B.Got}; cat_l(g0, sep, J, x, h) : {g == B.Got{SI.gtext(g)} : B.Got}}
        case 1n+k:
          +J = B.Got.join(Con{g1, t1}, sep)
          +eg0 = cat_l(g0, sep, J, x, h)
          +h2 = AB.subst(B.Got, z => {B.Got.cat(z, sep, J) == B.Got{x} : B.Got}, g0, B.Got{SI.gtext(g0)}, eg0, h)
          rec(k, SI.gtext(J), cat_r(SI.gtext(g0), sep, J, x, h2), g, hj)

# A joined text: every result in it is a text.
law join_nth:
  for +gs: Gs()
  for +sep: String
  for +x: String
  for +h: {B.Got.join(gs, sep) == B.Got{x} : B.Got}
  for +j: Nat
  for +g: B.Got
  for +hj: {List.get(&2, B.Got, gs, j) == Some{g} : Maybe<&2, B.Got>}
  {g == B.Got{SI.gtext(g)} : B.Got}

def join_nth(gs, sep, x, h, j, g, hj):
  match gs:
    case Nil{}:
      Empty.absurd({g == B.Got{SI.gtext(g)} : B.Got}, jn_nil(j, g, hj))
    case Con{+g0, +t}:
      jn_cons(t, g0, sep, x, h, j, g, hj, k => y => hy => g2 => hk => join_nth(t, sep, y, hy, k, g2, hk))

# The two "no c" tests agree.
law nc_eq:
  for +s: String
  for +c: Char
  {RT.no_c(s, c) == ST.noc(s, c) : Bool}

def nc_eq(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(Char.is_eq(h, c)), z), RT.no_c(t, c), ST.noc(t, c), nc_eq(t, c))

def gok_nc(+c: Char, +g: B.Got, +eg: {g == B.Got{SI.gtext(g)} : B.Got}, +hg: {CH.GOK(CH.NoC{c}, g) == True{} : Bool}) -> {ST.noc(SI.gtext(g), c) == True{} : Bool}:
  +h2 = AB.subst(B.Got, z => {CH.GOK(CH.NoC{c}, z) == True{} : Bool}, g, B.Got{SI.gtext(g)}, eg, hg)
  Equal.trans(Bool, ST.noc(SI.gtext(g), c), CH.ALLC(CH.NoC{c}, SI.gtext(g)), True{}, SM.noc_allc(SI.gtext(g), c), h2)

# Results joined with c, none holding a c: splitting at c gives their texts.
law join_sep:
  for +c: Char
  for +t: Gs()
  for +g: B.Got
  for +x: String
  for +h: {B.Got.join(Con{g, t}, SCon{c, SNil{}}) == B.Got{x} : B.Got}
  for +hg: {CH.GOKS(CH.NoC{c}, Con{g, t}) == True{} : Bool}
  {String.split(x, c) == SM.TX(Con{g, t}) : Ss()}

def join_sep(c, t, g, x, h, hg):
  match t:
    case Nil{}:
      +eg = SM.got_self(g, x, h)
      +ex = Equal.cong(B.Got, String, SI.gtext, g, B.Got{x}, h)
      %ex : {String.split(_, c) == SM.TX(Con{g, Nil{}}) : Ss()}
      ST.split_noc(SI.gtext(g), c, gok_nc(c, g, eg, AB.and_true_l(CH.GOK(CH.NoC{c}, g), True{}, hg)))
    case Con{+g2, +t2}:
      +sep = {SCon{c, SNil{}} : String}
      +J = B.Got.join(Con{g2, t2}, sep)
      +eg = cat_l(g, sep, J, x, h)
      +h2 = AB.subst(B.Got, z => {B.Got.cat(z, sep, J) == B.Got{x} : B.Got}, g, B.Got{SI.gtext(g)}, eg, h)
      +ex = cat_y(SI.gtext(g), sep, J, x, h2)
      +eJ = cat_r(SI.gtext(g), sep, J, x, h2)
      +nc = gok_nc(c, g, eg, AB.and_true_l(CH.GOK(CH.NoC{c}, g), CH.GOKS(CH.NoC{c}, Con{g2, t2}), hg))
      %Equal.sym(String, x, String.append(SI.gtext(g), String.append(sep, SI.gtext(J))), ex) : {String.split(_, c) == SM.TX(Con{g, Con{g2, t2}}) : Ss()}
      %Equal.sym(Ss(), String.split(String.append(SI.gtext(g), SCon{c, SI.gtext(J)}), c), SI.gtext(g) <> String.split(SI.gtext(J), c),
          RT.split_app(SI.gtext(g), SI.gtext(J), c, Equal.trans(Bool, RT.no_c(SI.gtext(g), c), ST.noc(SI.gtext(g), c), True{}, nc_eq(SI.gtext(g), c), nc))) :
        {_ == SM.TX(Con{g, Con{g2, t2}}) : Ss()}
      %Equal.sym(Ss(), String.split(SI.gtext(J), c), SM.TX(Con{g2, t2}), join_sep(c, t2, g2, SI.gtext(J), eJ, AB.and_true_r(CH.GOK(CH.NoC{c}, g), CH.GOKS(CH.NoC{c}, Con{g2, t2}), hg))) :
        {SI.gtext(g) <> _ == SM.TX(Con{g, Con{g2, t2}}) : Ss()}
      {==}

# A split line has at least 8 fields (it is not MALFORMED).
def L8T(+body: String) -> Data:
  {Nat.is_lt(List.length(&2, String, FS(body)), 8n) == False{} : Bool}

def l8_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {SI.COND(sp, FS(body)) == c : Bool},
  +h: {B.Rec.parts.if(SI.COND(sp, FS(body)), False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}) -> L8T(body):
  match c:
    case False{}:
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, FS(body)) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(L8T(body), AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = FS(body)
      +al = B.Rec.alts(fs)
      +M = B.Rec.malformed(fs)
      +hnm = SM.not_true(M, AB.and_true_r(sp, Bool.not(M), AB.and_true_l(Bool.and(sp, Bool.not(M)), Nat.is_le(2n, List.length(&2, String, al)), e)))
      +L8 = Nat.is_lt(List.length(&2, String, fs), 8n)
      +B0 = String.is_empty(B.Rec.field(fs, 0n))
      +B1 = Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))
      +B3 = Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n)))
      +B4 = B.Text.any_empty(B.Rec.alts(fs))
      SM.or_false_l(L8, B0, SM.or_false_l(Bool.or(L8, B0), B1, SM.or_false_l(Bool.or(Bool.or(L8, B0), B1), B3, SM.or_false_l(Bool.or(Bool.or(Bool.or(L8, B0), B1), B3), B4, hnm))))

law parts_l8:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  L8T(body)

def parts_l8(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      l8_if(SI.COND(sp, FS(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(SI.COND(sp, FS(body)), B.Text.has_cr(body), defs, o0, FS(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))

# The line's fields hold no tab; nor does any of its ALTs.
def fs_tab(+body: String) -> {CH.ALLS(SM.TAB(), FS(body)) == True{} : Bool}:
  Equal.trans(Bool, CH.ALLS(SM.TAB(), FS(body)), ST.allnoc(FS(body), '\t'), True{}, Equal.sym(Bool, ST.allnoc(FS(body), '\t'), CH.ALLS(SM.TAB(), FS(body)), SM.alls_noc(FS(body), '\t')), ST.split_all(body, '\t'))

def alt_tab(+body: String, +i: Nat, +a: String, +ha: {List.get(&2, String, ALTS(body), i) == Some{a} : Maybe<&2, String>}) -> {CH.ALLC(SM.TAB(), a) == True{} : Bool}:
  CH.get_all(SM.TAB(), ALTS(body), i, a, CH.split_all(SM.TAB(), B.Rec.field(FS(body), 4n), ',', CH.field_all(SM.TAB(), FS(body), 4n, fs_tab(body))), ha)

# A record's fields: the texts of its field results.
law fields_at:
  for +f0: String
  for +r: Ss()
  for +a: String
  for +defs: B.Defs
  for +o0: Bool
  for +n: Nat
  for +k: Nat
  for +p: String
  for +hg: {B.Rec.piece(Con{f0, r}, a, defs, o0, n, k) == B.Got{p} : B.Got}
  for +hf: {CH.ALLS(SM.TAB(), Con{f0, r}) == True{} : Bool}
  for +ha: {CH.ALLC(SM.TAB(), a) == True{} : Bool}
  {B.Rec.fields(p) == SM.TX(B.Rec.piece.go(Con{f0, r}, 0n, a, defs, String.split(B.Rec.field(Con{f0, r}, 8n), ':'), o0, n, k)) : Ss()}

def fields_at(f0, r, a, defs, o0, n, k, p, hg, hf, ha):
  +ks = String.split(B.Rec.field(Con{f0, r}, 8n), ':')
  join_sep('\t', B.Rec.piece.go(r, 1n, a, defs, ks, o0, n, k), B.Rec.piece.field(0n, f0, a, defs, ks, o0, n, k), p, hg,
    CH.pgo(SM.TAB(), Con{f0, r}, 0n, a, defs, ks, o0, n, k, hf, ha, {==}))
