import Base
import ./types.bend as B
import ./proof_s_cr.bend as CR
import ./LAWS.bend as L
import ./proof_s_str.bend as ST
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The records of a split line (B.Rec.parts' Pieces): each has the line's
# CHROM and POS (fields 0 and 1) and one ALT. Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def gtext(g: B.Got) -> String:
  match g:
    case B.Got{s}:
      s
    case B.Refuse{c}:
      ""

def is_got(g: B.Got) -> Bool:
  match g:
    case B.Got{s}:
      True{}
    case B.Refuse{c}:
      False{}

def is_pieces(pt: B.Parts) -> Bool:
  match pt:
    case B.Pieces{ps}:
      True{}
    case _:
      False{}

def pieces_of(pt: B.Parts) -> Ss():
  match pt:
    case B.Pieces{ps}:
      ps
    case _:
      Nil{}

# The record's site.
def SITE(+f0: String, +f1: String, +p: String) -> Type:
  {B.Rec.field(B.Rec.fields(p), 0n) == f0 : String} & ({B.Rec.field(B.Rec.fields(p), 1n) == f1 : String} & {L.n_alts(p) == 1n : Nat})

def ALLSITE(+f0: String, +f1: String, ps: Ss()) -> Type:
  match ps:
    case Nil{}:
      Unit
    case +p <> t:
      SITE(f0, f1, p) & ALLSITE(f0, f1, t)

# ---------------------------------------------------------------------------
# Joining with tabs
# ---------------------------------------------------------------------------

# A text joined in front of r: r is a text, and the whole is x, a tab, r's.
def cat_r(+x: String, +r: B.Got, +y: String, +h: {B.Got.cat(B.Got{x}, "\t", r) == B.Got{y} : B.Got}) -> {r == B.Got{gtext(r)} : B.Got}:
  match r:
    case B.Got{+w}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Got, Bool, is_got, B.Refuse{c}, B.Got{y}, h)))

def cat_y(+x: String, +r: B.Got, +y: String, +h: {B.Got.cat(B.Got{x}, "\t", r) == B.Got{y} : B.Got}) -> {y == String.append(x, String.append("\t", gtext(r))) : String}:
  match r:
    case B.Got{+w}:
      Equal.sym(String, String.append(x, String.append("\t", w)), y, Equal.cong(B.Got, String, gtext, B.Got{String.append(x, String.append("\t", w))}, B.Got{y}, h))
    case B.Refuse{+c}:
      Empty.absurd({y == String.append(x, "\t") : String}, AB.false_ne_true(Equal.cong(B.Got, Bool, is_got, B.Refuse{c}, B.Got{y}, h)))

# The fields after the ALT (none when the ALT is last).
def XL(r: Gs()) -> Ss():
  match r:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      String.split(gtext(B.Got.join(Con{g, t}, "\t")), '\t')

law last:
  for +a: String
  for +r: Gs()
  for +y: String
  for +h: {B.Got.join(Con{B.Got{a}, r}, "\t") == B.Got{y} : B.Got}
  for +hn: {ST.noc(a, '\t') == True{} : Bool}
  {String.split(y, '\t') == a <> XL(r) : Ss()}

def last(a, r, y, h, hn):
  match r:
    case Nil{}:
      %Equal.sym(String, y, a, Equal.sym(String, a, y, Equal.cong(B.Got, String, gtext, B.Got{a}, B.Got{y}, h))) : {String.split(_, '\t') == [a] : Ss()}
      ST.split_noc(a, '\t', hn)
    case Con{+g, +t}:
      +J = B.Got.join(Con{g, t}, "\t")
      %Equal.sym(String, y, String.append(a, String.append("\t", gtext(J))), cat_y(a, J, y, h)) : {String.split(_, '\t') == a <> XL(Con{g, t}) : Ss()}
      ST.split_tab(a, gtext(J), hn)

# ---------------------------------------------------------------------------
# A record's first five fields
# ---------------------------------------------------------------------------

def F5(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss()) -> Ss():
  Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}}

# The record for ALT a of a line whose fields are f0 .. f4 then rest: its
# fields are f0 .. f3, a, then the rest.
law piece_fields:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +rest: Ss()
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +x: String
  for +hj: {B.Got.join(B.Rec.piece.go(F5(f0, f1, f2, f3, f4, rest), 0n, a, defs, ks, over0, n, i), "\t") == B.Got{x} : B.Got}
  for +h0: {ST.noc(f0, '\t') == True{} : Bool}
  for +h1: {ST.noc(f1, '\t') == True{} : Bool}
  for +h2: {ST.noc(f2, '\t') == True{} : Bool}
  for +h3: {ST.noc(f3, '\t') == True{} : Bool}
  for +ha: {ST.noc(a, '\t') == True{} : Bool}
  {B.Rec.fields(x) == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i))}}}}} : Ss()}

def piece_fields(f0, f1, f2, f3, f4, rest, a, defs, ks, over0, n, i, x, hj, h0, h1, h2, h3, ha):
  +R5 = B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i)
  +J4 = B.Got.join(Con{B.Got{a}, R5}, "\t")
  +J3 = B.Got.join(Con{B.Got{f3}, Con{B.Got{a}, R5}}, "\t")
  +J2 = B.Got.join(Con{B.Got{f2}, Con{B.Got{f3}, Con{B.Got{a}, R5}}}, "\t")
  +J1 = B.Got.join(Con{B.Got{f1}, Con{B.Got{f2}, Con{B.Got{f3}, Con{B.Got{a}, R5}}}}, "\t")
  +w1 = gtext(J1)
  +w2 = gtext(J2)
  +w3 = gtext(J3)
  +w4 = gtext(J4)
  +e1 = cat_r(f0, J1, x, hj)
  +e2 = cat_r(f1, J2, w1, e1)
  +e3 = cat_r(f2, J3, w2, e2)
  +e4 = cat_r(f3, J4, w3, e3)
  %Equal.sym(String, x, String.append(f0, String.append("\t", w1)), cat_y(f0, J1, x, hj)) : {String.split(_, '\t') == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(Ss(), String.split(String.append(f0, SCon{'\t', w1}), '\t'), f0 <> String.split(w1, '\t'), ST.split_tab(f0, w1, h0)) : {_ == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(String, w1, String.append(f1, String.append("\t", w2)), cat_y(f1, J2, w1, e1)) : {f0 <> String.split(_, '\t') == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(Ss(), String.split(String.append(f1, SCon{'\t', w2}), '\t'), f1 <> String.split(w2, '\t'), ST.split_tab(f1, w2, h1)) : {f0 <> _ == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(String, w2, String.append(f2, String.append("\t", w3)), cat_y(f2, J3, w2, e2)) : {f0 <> f1 <> String.split(_, '\t') == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(Ss(), String.split(String.append(f2, SCon{'\t', w3}), '\t'), f2 <> String.split(w3, '\t'), ST.split_tab(f2, w3, h2)) : {f0 <> f1 <> _ == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(String, w3, String.append(f3, String.append("\t", w4)), cat_y(f3, J4, w3, e3)) : {f0 <> f1 <> f2 <> String.split(_, '\t') == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(Ss(), String.split(String.append(f3, SCon{'\t', w4}), '\t'), f3 <> String.split(w4, '\t'), ST.split_tab(f3, w4, h3)) : {f0 <> f1 <> f2 <> _ == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  %Equal.sym(Ss(), String.split(w4, '\t'), a <> XL(R5), last(a, R5, w4, e4, ha)) : {f0 <> f1 <> f2 <> f3 <> _ == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, XL(R5)}}}}} : Ss()}
  {==}

# Its CHROM, POS and its one ALT.
def piece_site(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +a: String, +defs: B.Defs, +ks: Ss(), +over0: Bool, +n: Nat, +i: Nat, +x: String,
  +hj: {B.Got.join(B.Rec.piece.go(F5(f0, f1, f2, f3, f4, rest), 0n, a, defs, ks, over0, n, i), "\t") == B.Got{x} : B.Got},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +ha: {ST.noc(a, '\t') == True{} : Bool}, +hc: {ST.noc(a, ',') == True{} : Bool}) -> SITE(f0, f1, x):
  +R = XL(B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i))
  +E = piece_fields(f0, f1, f2, f3, f4, rest, a, defs, ks, over0, n, i, x, hj, h0, h1, h2, h3, ha)
  +G = {Con{f0, Con{f1, Con{f2, Con{f3, Con{a, R}}}}} : Ss()}
  ({%Equal.sym(Ss(), B.Rec.fields(x), G, E) : {B.Rec.field(_, 0n) == f0 : String}; {==} : {B.Rec.field(B.Rec.fields(x), 0n) == f0 : String}},
   ({%Equal.sym(Ss(), B.Rec.fields(x), G, E) : {B.Rec.field(_, 1n) == f1 : String}; {==} : {B.Rec.field(B.Rec.fields(x), 1n) == f1 : String}},
    {%Equal.sym(Ss(), B.Rec.fields(x), G, E) : {List.length(&2, String, B.Rec.alts(_)) == 1n : Nat};
     %Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hc)) : {List.length(&2, String, _) == 1n : Nat};
     {==} : {L.n_alts(x) == 1n : Nat}}))

# Parts.cons giving Pieces: a text in front of Pieces.
def pc_g(+g: B.Got, +r: B.Parts, +ps: Ss(), +h: {B.Parts.cons(g, r) == B.Pieces{ps} : B.Parts}) -> {g == B.Got{gtext(g)} : B.Got}:
  match g:
    case B.Got{+x}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

def pc_r(+x: String, +r: B.Parts, +ps: Ss(), +h: {B.Parts.cons(B.Got{x}, r) == B.Pieces{ps} : B.Parts}) -> {r == B.Pieces{pieces_of(r)} : B.Parts}:
  match r:
    case B.Pieces{+qs}:
      {==}
    case B.Whole{}:
      Empty.absurd({B.Whole{} == B.Pieces{Nil{}} : B.Parts}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h)))
    case B.Unsplit{+c}:
      Empty.absurd({B.Unsplit{c} == B.Pieces{Nil{}} : B.Parts}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

def pc_ps(+x: String, +r: B.Parts, +ps: Ss(), +h: {B.Parts.cons(B.Got{x}, r) == B.Pieces{ps} : B.Parts}) -> {ps == x <> pieces_of(r) : Ss()}:
  match r:
    case B.Pieces{+qs}:
      Equal.sym(Ss(), x <> qs, ps, Equal.cong(B.Parts, Ss(), pieces_of, B.Pieces{x <> qs}, B.Pieces{ps}, h))
    case B.Whole{}:
      Empty.absurd({ps == [x] : Ss()}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h)))
    case B.Unsplit{+c}:
      Empty.absurd({ps == [x] : Ss()}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{c}, B.Pieces{ps}, h)))

# The records for the ALTs from i on.
law pieces_site:
  for +alts: Ss()
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +rest: Ss()
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts}
  for +h0: {ST.noc(f0, '\t') == True{} : Bool}
  for +h1: {ST.noc(f1, '\t') == True{} : Bool}
  for +h2: {ST.noc(f2, '\t') == True{} : Bool}
  for +h3: {ST.noc(f3, '\t') == True{} : Bool}
  for +hat: {ST.allnoc(alts, '\t') == True{} : Bool}
  for +hac: {ST.allnoc(alts, ',') == True{} : Bool}
  ALLSITE(f0, f1, ps)

def pieces_site(alts, f0, f1, f2, f3, f4, rest, defs, over0, n, i, ps, h, h0, h1, h2, h3, hat, hac):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : ALLSITE(f0, f1, _)
      Unit{}
    case Con{+a, +t}:
      +FS = F5(f0, f1, f2, f3, f4, rest)
      +g = B.Rec.piece(FS, a, defs, over0, n, i)
      +r = B.Parts.of(B.Rec.pieces.go(t, FS, defs, over0, n, 1n+i))
      +eg = pc_g(g, r, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
      %Equal.sym(Ss(), ps, gtext(g) <> pieces_of(r), pc_ps(gtext(g), r, ps, h2g)) : ALLSITE(f0, f1, _)
      (piece_site(f0, f1, f2, f3, f4, rest, a, defs, String.split(B.Rec.field(FS, 8n), ':'), over0, n, i, gtext(g), eg, h0, h1, h2, h3,
         AB.and_true_l(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat), AB.and_true_l(ST.noc(a, ','), ST.allnoc(t, ','), hac)),
       pieces_site(t, f0, f1, f2, f3, f4, rest, defs, over0, n, 1n+i, pieces_of(r), pc_r(gtext(g), r, ps, h2g), h0, h1, h2, h3,
         AB.and_true_r(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat), AB.and_true_r(ST.noc(a, ','), ST.allnoc(t, ','), hac)))

def F(+fs: Ss(), +k: Nat) -> String:
  B.Rec.field(fs, k)

def site_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts},
  +hall: {ST.allnoc(fs, '\t') == True{} : Bool},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))) == True{} : Bool}) -> ALLSITE(F(fs, 0n), F(fs, 1n), ps):
  match fs:
    case Nil{}:
      Empty.absurd(ALLSITE("", "", ps), AB.false_ne_true(hn2))
    case Con{+f0, Nil{}}:
      Empty.absurd(ALLSITE(f0, "", ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd(ALLSITE(f0, f1, ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd(ALLSITE(f0, f1, ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd(ALLSITE(f0, f1, ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, +rest}}}}}:
      +a1 = AB.and_true_r(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall)
      +a2 = AB.and_true_r(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1)
      +a3 = AB.and_true_r(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2)
      +a4 = AB.and_true_r(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3)
      pieces_site(String.split(f4, ','), f0, f1, f2, f3, f4, rest, defs, o0, List.length(&2, String, String.split(f4, ',')), 1n, ps, h,
        AB.and_true_l(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall),
        AB.and_true_l(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1),
        AB.and_true_l(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2),
        AB.and_true_l(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3),
        ST.split_nod(f4, ',', '\t', AB.and_true_l(ST.noc(f4, '\t'), ST.allnoc(rest, '\t'), a4)),
        ST.split_all(f4, ','))

def ps_split(+d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool}) ->
  ALLSITE(F(B.Rec.fields(body), 0n), F(B.Rec.fields(body), 1n), ps):
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(ALLSITE(F(fs, 0n), F(fs, 1n), ps), AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      site_fs(fs, defs, o0, ps, h2, ST.split_all(body, '\t'), hn2)

def COND(+sp: Bool, +fs: Ss()) -> Bool:
  Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))))

def ps_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  ALLSITE(F(B.Rec.fields(body), 0n), F(B.Rec.fields(body), 1n), ps):
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(ALLSITE(F(fs, 0n), F(fs, 1n), ps), AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      ps_split(B.Alts.distinct(al), defs, o0, body, ps, {==}, h2,
        AB.and_true_r(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, al)), e))

# The records of a split line (B.Rec.parts' Pieces): each has the line's
# CHROM and POS and one ALT.
law parts_site:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  ALLSITE(F(B.Rec.fields(body), 0n), F(B.Rec.fields(body), 1n), ps)

def parts_site(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      ps_if(COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))

# ---------------------------------------------------------------------------
# The records' ALT fields (law split_alts)
# ---------------------------------------------------------------------------

def a4(+x: String, +f0: String, +f1: String, +f2: String, +f3: String, +a: String, +xl: Ss(),
  +e: {B.Rec.fields(x) == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, xl}}}}} : Ss()}) -> {B.Rec.field(B.Rec.fields(x), 4n) == a : String}:
  %Equal.sym(Ss(), B.Rec.fields(x), Con{f0, Con{f1, Con{f2, Con{f3, Con{a, xl}}}}}, e) : {B.Rec.field(_, 4n) == a : String}
  {==}

law pieces_alts:
  for +alts: Ss()
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +rest: Ss()
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts}
  for +h0: {ST.noc(f0, '\t') == True{} : Bool}
  for +h1: {ST.noc(f1, '\t') == True{} : Bool}
  for +h2: {ST.noc(f2, '\t') == True{} : Bool}
  for +h3: {ST.noc(f3, '\t') == True{} : Bool}
  for +hat: {ST.allnoc(alts, '\t') == True{} : Bool}
  {L.alt_fields(ps) == alts : Ss()}

def pieces_alts(alts, f0, f1, f2, f3, f4, rest, defs, over0, n, i, ps, h, h0, h1, h2, h3, hat):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {L.alt_fields(_) == Nil{} : Ss()}
      {==}
    case Con{+a, +t}:
      +FS = F5(f0, f1, f2, f3, f4, rest)
      +g = B.Rec.piece(FS, a, defs, over0, n, i)
      +r = B.Parts.of(B.Rec.pieces.go(t, FS, defs, over0, n, 1n+i))
      +eg = pc_g(g, r, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
      +ks = String.split(B.Rec.field(FS, 8n), ':')
      %Equal.sym(Ss(), ps, gtext(g) <> pieces_of(r), pc_ps(gtext(g), r, ps, h2g)) : {L.alt_fields(_) == Con{a, t} : Ss()}
      %Equal.sym(String, B.Rec.field(B.Rec.fields(gtext(g)), 4n), a,
          a4(gtext(g), f0, f1, f2, f3, a, XL(B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i)),
            piece_fields(f0, f1, f2, f3, f4, rest, a, defs, ks, over0, n, i, gtext(g), eg, h0, h1, h2, h3, AB.and_true_l(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat)))) :
        {Con{_, L.alt_fields(pieces_of(r))} == Con{a, t} : Ss()}
      %Equal.sym(Ss(), L.alt_fields(pieces_of(r)), t, pieces_alts(t, f0, f1, f2, f3, f4, rest, defs, over0, n, 1n+i, pieces_of(r), pc_r(gtext(g), r, ps, h2g), h0, h1, h2, h3, AB.and_true_r(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat))) :
        {Con{a, _} == Con{a, t} : Ss()}
      {==}

def alts_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts},
  +hall: {ST.allnoc(fs, '\t') == True{} : Bool},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))) == True{} : Bool}) -> {L.alt_fields(ps) == B.Rec.alts(fs) : Ss()}:
  match fs:
    case Nil{}:
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(Nil{}) : Ss()}, AB.false_ne_true(hn2))
    case Con{+f0, Nil{}}:
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(Con{f0, Nil{}}) : Ss()}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(Con{f0, Con{f1, Nil{}}}) : Ss()}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(Con{f0, Con{f1, Con{f2, Nil{}}}}) : Ss()}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}) : Ss()}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, +rest}}}}}:
      +a1 = AB.and_true_r(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall)
      +a2 = AB.and_true_r(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1)
      +a3 = AB.and_true_r(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2)
      +a4 = AB.and_true_r(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3)
      pieces_alts(String.split(f4, ','), f0, f1, f2, f3, f4, rest, defs, o0, List.length(&2, String, String.split(f4, ',')), 1n, ps, h,
        AB.and_true_l(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall),
        AB.and_true_l(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1),
        AB.and_true_l(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2),
        AB.and_true_l(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3),
        ST.split_nod(f4, ',', '\t', AB.and_true_l(ST.noc(f4, '\t'), ST.allnoc(rest, '\t'), a4)))

def pa_split(+d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool}) ->
  {L.alt_fields(ps) == B.Rec.alts(B.Rec.fields(body)) : Ss()}:
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(fs) : Ss()}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      alts_fs(fs, defs, o0, ps, h2, ST.split_all(body, '\t'), hn2)

def pa_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  {L.alt_fields(ps) == B.Rec.alts(B.Rec.fields(body)) : Ss()}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.alt_fields(ps) == B.Rec.alts(fs) : Ss()}, AB.false_ne_true(Equal.cong(B.Parts, Bool, is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      pa_split(B.Alts.distinct(al), defs, o0, body, ps, {==}, h2,
        AB.and_true_r(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, al)), e))

# One record per ALT, in the input's order (law split_alts).
law split_alts:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {L.alt_fields(ps) == B.Rec.alts(B.Rec.fields(body)) : Ss()}

def split_alts(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      pa_if(COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))
