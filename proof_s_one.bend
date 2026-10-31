import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_recs.bend as RS
import ./proof_b_simdefs.bend as S
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The records of a split line have one ALT each (each ALT field is one of the
# line's ALTs, which hold no comma): so a record is not split again. Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def tl(xs: Ss()) -> Ss():
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      t

def hd(+d: String, xs: Ss()) -> String:
  match xs:
    case Nil{}:
      d
    case x <> t:
      x

def is_con(xs: Ss()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      True{}

def and_tt(a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

law ao:
  for +ps: Ss()
  for +xs: Ss()
  for +term: String
  for +h: {L.alt_fields(ps) == xs : Ss()}
  for +hc: {ST.allnoc(xs, ',') == True{} : Bool}
  {S.all_one(RS.LS(ps, term)) == True{} : Bool}

def ao(ps, xs, term, h, hc):
  match ps xs:
    case Nil{} _:
      {==}
    case Con{+p, +t} Nil{}:
      Empty.absurd({S.all_one(RS.LS(Con{p, t}, term)) == True{} : Bool}, AB.false_ne_true(Equal.cong(Ss(), Bool, z => is_con(z), Nil{}, L.alt_fields(Con{p, t}), Equal.sym(Ss(), L.alt_fields(Con{p, t}), Nil{}, h))))
    case Con{+p, +t} Con{+a, +xt}:
      +f4 = B.Rec.field(B.Rec.fields(p), 4n)
      +ea = Equal.cong(Ss(), String, z => hd(f4, z), L.alt_fields(Con{p, t}), Con{a, xt}, h)
      +et = Equal.cong(Ss(), Ss(), z => tl(z), L.alt_fields(Con{p, t}), Con{a, xt}, h)
      +hna = P.and_true_l(ST.noc(a, ','), ST.allnoc(xt, ','), hc)
      +one = {(%Equal.sym(String, f4, a, ea) : {Nat.is_lt(List.length(&2, String, String.split(_, ',')), 2n) == True{} : Bool};
          %Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hna)) : {Nat.is_lt(List.length(&2, String, _), 2n) == True{} : Bool};
          {==}) : {S.one_alt(B.Line{p, term}) == True{} : Bool}}
      and_tt(S.one_alt(B.Line{p, term}), S.all_one(RS.LS(t, term)), one, ao(t, xt, term, et, P.and_true_r(ST.noc(a, ','), ST.allnoc(xt, ','), hc)))

law pieces_one:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +term: String
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {S.all_one(RS.LS(ps, term)) == True{} : Bool}

def pieces_one(defs, o, body, ps, term, h):
  ao(ps, B.Rec.alts(B.Rec.fields(body)), term, SI.split_alts(defs, o, body, ps, h), ST.split_all(B.Rec.field(B.Rec.fields(body), 4n), ','))

# A record with one ALT is left whole: -m does not split it again.
def lt2(n: Nat, +h: {Nat.is_lt(n, 2n) == True{} : Bool}) -> {Nat.is_le(2n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.is_le(2n, 2n+q) == False{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, P.lt_zero(q)), h)))

law one_parts:
  for +defs: B.Defs
  for +o: B.Opts
  for +b: String
  for +h1: {Nat.is_lt(L.n_alts(b), 2n) == True{} : Bool}
  {B.Rec.parts(defs, o, b) == B.Whole{} : B.Parts}

def one_parts(defs, o, b, h1):
  match o:
    case B.Opts{+s, +w, +sp, +o0, +a}:
      +g = Bool.and(sp, Bool.not(B.Rec.malformed(B.Rec.fields(b))))
      %Equal.sym(Bool, Nat.is_le(2n, L.n_alts(b)), False{}, lt2(L.n_alts(b), h1)) : {B.Rec.parts.if(Bool.and(g, _), B.Text.has_cr(b), defs, o0, B.Rec.fields(b)) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Bool.and(g, False{}), False{}, P.and_false_r(g)) : {B.Rec.parts.if(_, B.Text.has_cr(b), defs, o0, B.Rec.fields(b)) == B.Whole{} : B.Parts}
      {==}

def is_pieces(p: B.Parts) -> Bool:
  match p:
    case B.Pieces{ps}:
      True{}
    case B.Whole{}:
      False{}
    case B.Unsplit{c}:
      False{}

# So a record with one ALT is never split into pieces.
law one_not_pieces:
  for +defs: B.Defs
  for +o: B.Opts
  for +b: String
  for +ps: Ss()
  for +h1: {Nat.is_lt(L.n_alts(b), 2n) == True{} : Bool}
  for +hp: {B.Rec.parts(defs, o, b) == B.Pieces{ps} : B.Parts}
  Empty

def one_not_pieces(defs, o, b, ps, h1, hp):
  P.false_ne_true(Equal.trans(Bool, False{}, is_pieces(B.Rec.parts(defs, o, b)), True{},
    Equal.cong(B.Parts, Bool, z => is_pieces(z), B.Whole{}, B.Rec.parts(defs, o, b), Equal.sym(B.Parts, B.Rec.parts(defs, o, b), B.Whole{}, one_parts(defs, o, b, h1))),
    Equal.cong(B.Parts, Bool, z => is_pieces(z), B.Rec.parts(defs, o, b), B.Pieces{ps}, hp)))
