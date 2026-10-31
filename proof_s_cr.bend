import Base
import ./types.bend as B
import ./run.bend as R
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# A line -m splits holds no carriage return (B.Rec.parts.cr): so the laws
# about split lines see Rec.parts.if with no CR, as before the CR rule. Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def is_pieces(pt: B.Parts) -> Bool:
  match pt:
    case B.Pieces{ps}:
      True{}
    case _:
      False{}

def cr.k(go: Bool, cr: Bool, +defs: B.Defs, +o0: Bool, +fs: Ss(), +ps: Ss(),
  +h: {B.Rec.parts.if(go, cr, defs, o0, fs) == B.Pieces{ps} : B.Parts}) -> {cr == False{} : Bool}:
  match go cr:
    case False{} _:
      Empty.absurd({cr == False{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, z => is_pieces(z), B.Whole{}, B.Pieces{ps}, h)))
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, z => is_pieces(z), B.Unsplit{B.BadCr{}}, B.Pieces{ps}, h)))
    case True{} False{}:
      {==}

law cr_none:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {B.Text.has_cr(body) == False{} : Bool}

def cr_none(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(body)
      cr.k(sp && Bool.not(B.Rec.malformed(fs)) && Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))), B.Text.has_cr(body), defs, o0, fs, ps, h)

# The Pieces hypothesis, the CR test answered.
def cr_h(+go: Bool, +cr: Bool, +defs: B.Defs, +o0: Bool, +fs: Ss(), +ps: Ss(),
  +hc: {cr == False{} : Bool},
  +h: {B.Rec.parts.if(go, cr, defs, o0, fs) == B.Pieces{ps} : B.Parts}) -> {B.Rec.parts.if(go, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}:
  {(%hc : {B.Rec.parts.if(go, _, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h) : {B.Rec.parts.if(go, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
