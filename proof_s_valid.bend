import Base
import ./types.bend as B
import ./proof_s_cr.bend as CR
import ./LAWS.bend as L
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI

# Law split_valid's core: when a variant is valid with all its ALTs, it is
# valid with any one of them. Every variable is reusable.

def Bs() -> Data:
  List<&2, B.Base>

def Vs() -> Data:
  List<&2, List<&2, B.Base>>

def VAL(+seq: Bs(), +pos: Nat, +ref: Bs(), +alts: Vs()) -> Bool:
  L.valid(seq, B.Var{pos, ref, alts})

# Every ALT alone: valid.
def ALLV(+seq: Bs(), +pos: Nat, +ref: Bs(), ys: Vs()) -> Type:
  match ys:
    case Nil{}:
      Unit
    case +y <> t:
      {VAL(seq, pos, ref, [y]) == True{} : Bool} & ALLV(seq, pos, ref, t)

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(h))
    case False{}:
      {==}

def or_false_l(+a: Bool, +b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, e)))

def or_false_r(+a: Bool, +b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, e)))

def SL(+seq: Bs(), +pos: Nat, +ref: Bs()) -> Bool:
  B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(ref)), ref)

law vall:
  for +seq: Bs()
  for +pos: Nat
  for +ref: Bs()
  for +ys: Vs()
  for +hP: {Nat.is_le(1n, pos) == True{} : Bool}
  for +hR: {Nat.is_le(1n, L.len(ref)) == True{} : Bool}
  for +hS: {SL(seq, pos, ref) == True{} : Bool}
  for +hNE: {L.all_nonempty(ys) == True{} : Bool}
  for +hM: {B.Alleles.member(ref, ys) == False{} : Bool}
  ALLV(seq, pos, ref, ys)

def vall(seq, pos, ref, ys, hP, hR, hS, hNE, hM):
  match ys:
    case Nil{}:
      Unit{}
    case Con{+y, +t}:
      +hy = AB.and_true_l(Nat.is_le(1n, L.len(y)), L.all_nonempty(t), hNE)
      +ht = AB.and_true_r(Nat.is_le(1n, L.len(y)), L.all_nonempty(t), hNE)
      +he = or_false_l(B.Bases.eq(ref, y), B.Alleles.member(ref, t), hM)
      +hm = or_false_r(B.Bases.eq(ref, y), B.Alleles.member(ref, t), hM)
      +v1 = {%Equal.sym(Bool, Nat.is_le(1n, pos), True{}, hP) :
          {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(_, Nat.is_le(1n, L.len(ref))), Nat.is_le(1n, 1n)), Bool.and(Nat.is_le(1n, L.len(y)), True{})), Bool.and(Bool.not(Bool.or(B.Bases.eq(ref, y), False{})), Bool.and(Bool.not(False{}), True{}))), SL(seq, pos, ref)) == True{} : Bool};
        %Equal.sym(Bool, Nat.is_le(1n, L.len(ref)), True{}, hR) :
          {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, _), Nat.is_le(1n, 1n)), Bool.and(Nat.is_le(1n, L.len(y)), True{})), Bool.and(Bool.not(Bool.or(B.Bases.eq(ref, y), False{})), Bool.and(Bool.not(False{}), True{}))), SL(seq, pos, ref)) == True{} : Bool};
        %Equal.sym(Bool, Nat.is_le(1n, L.len(y)), True{}, hy) :
          {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), Nat.is_le(1n, 1n)), Bool.and(_, True{})), Bool.and(Bool.not(Bool.or(B.Bases.eq(ref, y), False{})), Bool.and(Bool.not(False{}), True{}))), SL(seq, pos, ref)) == True{} : Bool};
        %Equal.sym(Bool, B.Bases.eq(ref, y), False{}, he) :
          {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), Nat.is_le(1n, 1n)), Bool.and(True{}, True{})), Bool.and(Bool.not(Bool.or(_, False{})), Bool.and(Bool.not(False{}), True{}))), SL(seq, pos, ref)) == True{} : Bool};
        %Equal.sym(Bool, SL(seq, pos, ref), True{}, hS) :
          {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), Nat.is_le(1n, 1n)), Bool.and(True{}, True{})), Bool.and(Bool.not(Bool.or(False{}, False{})), Bool.and(Bool.not(False{}), True{}))), _) == True{} : Bool};
        {==} : {VAL(seq, pos, ref, [y]) == True{} : Bool}}
      (v1, vall(seq, pos, ref, t, hP, hR, hS, ht, hm))

# From a valid variant: every ALT alone.
def VF(+seq: Bs(), +pos: Nat, +ref: Bs(), +alts: Vs()) -> Bool:
  Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_le(1n, pos), Nat.is_le(1n, L.len(ref))), Nat.is_le(1n, List.length(&2, Bs(), alts))), L.all_nonempty(alts)), B.Alleles.distinct(ref <> alts)), SL(seq, pos, ref))

law valid_each:
  for +seq: Bs()
  for +pos: Nat
  for +ref: Bs()
  for +alts: Vs()
  for +hv: {VAL(seq, pos, ref, alts) == True{} : Bool}
  ALLV(seq, pos, ref, alts)

def valid_each(seq, pos, ref, alts, hv):
  +A1 = Nat.is_le(1n, pos)
  +A2 = Nat.is_le(1n, L.len(ref))
  +A3 = Nat.is_le(1n, List.length(&2, Bs(), alts))
  +A4 = L.all_nonempty(alts)
  +A5 = B.Alleles.distinct(ref <> alts)
  +A6 = SL(seq, pos, ref)
  +h5 = AB.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(A1, A2), A3), A4), A5), A6, hv)
  +hS = AB.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(A1, A2), A3), A4), A5), A6, hv)
  +h4 = AB.and_true_l(Bool.and(Bool.and(Bool.and(A1, A2), A3), A4), A5, h5)
  +hD = AB.and_true_r(Bool.and(Bool.and(Bool.and(A1, A2), A3), A4), A5, h5)
  +h3 = AB.and_true_l(Bool.and(Bool.and(A1, A2), A3), A4, h4)
  +hNE = AB.and_true_r(Bool.and(Bool.and(A1, A2), A3), A4, h4)
  +h2 = AB.and_true_l(Bool.and(A1, A2), A3, h3)
  +hP = AB.and_true_l(A1, A2, h2)
  +hR = AB.and_true_r(A1, A2, h2)
  +hM = not_true(B.Alleles.member(ref, alts), AB.and_true_l(Bool.not(B.Alleles.member(ref, alts)), B.Alleles.distinct(alts), hD))
  vall(seq, pos, ref, alts, hP, hR, hS, hNE, hM)

# ---------------------------------------------------------------------------
# The records of a split line
# ---------------------------------------------------------------------------

def Ss() -> Data:
  List<&2, String>

def MV() -> Data:
  Maybe<&2, Vs()>

def hdx(xs: Vs()) -> Bs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x

def tlx(xs: Vs()) -> Vs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def unv(m: MV()) -> Vs():
  Maybe.default(&2, Vs(), m, Nil{})

def is_somev(m: MV()) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# Reading ALTs that all read: the first, and the rest.
def rd_k(+ma: Maybe<&2, Bs()>, +mt: MV(), +xs: Vs(), +h: {B.Alleles.read.cons(ma, mt) == Some{xs} : MV()}) ->
  {ma == Some{hdx(xs)} : Maybe<&2, Bs()>} & ({mt == Some{tlx(xs)} : MV()} & {xs == Con{hdx(xs), tlx(xs)} : Vs()}):
  match ma mt:
    case Some{+x} Some{+ys}:
      +e = Equal.cong(MV(), Vs(), unv, Some{Con{x, ys}}, Some{xs}, h)
      %e : {Some{x} == Some{hdx(_)} : Maybe<&2, Bs()>} & ({Some{ys} == Some{tlx(_)} : MV()} & {_ == Con{hdx(_), tlx(_)} : Vs()})
      ({==}, ({==}, {==}))
    case None{} _:
      Empty.absurd({None{} == Some{hdx(xs)} : Maybe<&2, Bs()>} & ({mt == Some{tlx(xs)} : MV()} & {xs == Con{hdx(xs), tlx(xs)} : Vs()}),
        AB.false_ne_true(Equal.cong(MV(), Bool, is_somev, None{}, Some{xs}, h)))
    case Some{+x} None{}:
      Empty.absurd({Some{x} == Some{hdx(xs)} : Maybe<&2, Bs()>} & ({None{} == Some{tlx(xs)} : MV()} & {xs == Con{hdx(xs), tlx(xs)} : Vs()}),
        AB.false_ne_true(Equal.cong(MV(), Bool, is_somev, None{}, Some{xs}, h)))

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def SEQ(+raw: String) -> Bs():
  B.Bases.of_fasta(raw)

def F5(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss()) -> Ss():
  Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}}

# One record: valid with its ALT.
def lv_one(+fa: List<&2, B.Contig>, +raw: String, +ref: Bs(), +x: Bs(), +P: String,
  +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +a: String, +xl: Ss(),
  +E: {B.Rec.fields(P) == Con{f0, Con{f1, Con{f2, Con{f3, Con{a, xl}}}}} : Ss()},
  +hfind: {B.Fasta.find(fa, f0) == Some{raw} : Maybe<&2, String>},
  +href: {B.Allele.read(f3) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Allele.read(a) == Some{x} : Maybe<&2, Bs()>},
  +hac: {ST.noc(a, ',') == True{} : Bool},
  +vh: {VAL(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, [x]) == True{} : Bool}) ->
  {L.line_valid(fa, P) == True{} : Bool}:
  +G = {Con{f0, Con{f1, Con{f2, Con{f3, Con{a, xl}}}}} : Ss()}
  %Equal.sym(Ss(), B.Rec.fields(P), G, E) : {L.line_valid.contig(B.Fasta.find(fa, B.Rec.field(_, 0n)), _) == True{} : Bool}
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, f0), Some{raw}, hfind) : {L.line_valid.contig(_, G) == True{} : Bool}
  %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(f3), Some{ref}, href) :
    {L.line_valid.vars(_, B.Alleles.read(String.split(a, ',')), SEQ(raw), B.Rec.pos(G)) == True{} : Bool}
  %Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hac)) :
    {L.line_valid.vars(Some{ref}, B.Alleles.read(_), SEQ(raw), B.Rec.pos(G)) == True{} : Bool}
  %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(a), Some{x}, ea) :
    {L.line_valid.vars(Some{ref}, B.Alleles.read.cons(_, Some{Nil{}}), SEQ(raw), B.Rec.pos(G)) == True{} : Bool}
  vh

def pv.d(+fa: List<&2, B.Contig>, +raw: String, +ref: Bs(), +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +defs: B.Defs, +over0: Bool, +n: Nat, +i: Nat, +a: String, +t: Ss(), +xs: Vs(), +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(Con{a, t}, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts},
  +ea: {B.Allele.read(a) == Some{hdx(xs)} : Maybe<&2, Bs()>},
  +et: {B.Alleles.read(t) == Some{tlx(xs)} : MV()},
  hv2: ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, Con{hdx(xs), tlx(xs)}),
  +hfind: {B.Fasta.find(fa, f0) == Some{raw} : Maybe<&2, String>},
  +href: {B.Allele.read(f3) == Some{ref} : Maybe<&2, Bs()>},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +hta: {ST.noc(a, '\t') == True{} : Bool}, +hca: {ST.noc(a, ',') == True{} : Bool},
  ih: @+ps2: Ss() -> {B.Parts.of(B.Rec.pieces.go(t, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, 1n+i)) == B.Pieces{ps2} : B.Parts} -> {B.Alleles.read(t) == Some{tlx(xs)} : MV()} -> ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, tlx(xs)) -> {L.all_line_valid(fa, ps2) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  (vh, vt) = hv2
  +g = B.Rec.piece(F5(f0, f1, f2, f3, f4, rest), a, defs, over0, n, i)
  +r = B.Parts.of(B.Rec.pieces.go(t, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, 1n+i))
  +eg = SI.pc_g(g, r, ps, h)
  +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{SI.gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
  +ks = String.split(B.Rec.field(F5(f0, f1, f2, f3, f4, rest), 8n), ':')
  +E = SI.piece_fields(f0, f1, f2, f3, f4, rest, a, defs, ks, over0, n, i, SI.gtext(g), eg, h0, h1, h2, h3, hta)
  %Equal.sym(Ss(), ps, SI.gtext(g) <> SI.pieces_of(r), SI.pc_ps(SI.gtext(g), r, ps, h2g)) : {L.all_line_valid(fa, _) == True{} : Bool}
  and_tt(L.line_valid(fa, SI.gtext(g)), L.all_line_valid(fa, SI.pieces_of(r)),
    lv_one(fa, raw, ref, hdx(xs), SI.gtext(g), f0, f1, f2, f3, f4, rest, a, SI.XL(B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i)), E, hfind, href, ea, hca, vh),
    ih(SI.pieces_of(r), SI.pc_r(SI.gtext(g), r, ps, h2g), et, vt))

def pv.c(+fa: List<&2, B.Contig>, +raw: String, +ref: Bs(), +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +defs: B.Defs, +over0: Bool, +n: Nat, +i: Nat, +a: String, +t: Ss(), +xs: Vs(), +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(Con{a, t}, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts},
  rd: {B.Allele.read(a) == Some{hdx(xs)} : Maybe<&2, Bs()>} & ({B.Alleles.read(t) == Some{tlx(xs)} : MV()} & {xs == Con{hdx(xs), tlx(xs)} : Vs()}),
  hall: ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, xs),
  +hfind: {B.Fasta.find(fa, f0) == Some{raw} : Maybe<&2, String>},
  +href: {B.Allele.read(f3) == Some{ref} : Maybe<&2, Bs()>},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +hta: {ST.noc(a, '\t') == True{} : Bool}, +hca: {ST.noc(a, ',') == True{} : Bool},
  ih: @+ps2: Ss() -> {B.Parts.of(B.Rec.pieces.go(t, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, 1n+i)) == B.Pieces{ps2} : B.Parts} -> {B.Alleles.read(t) == Some{tlx(xs)} : MV()} -> ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, tlx(xs)) -> {L.all_line_valid(fa, ps2) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  (ea, q) = rd
  (et, ex2) = q
  pv.d(fa, raw, ref, f0, f1, f2, f3, f4, rest, defs, over0, n, i, a, t, xs, ps, h, ea, et,
    AB.subst(Vs(), z => ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, z), xs, Con{hdx(xs), tlx(xs)}, ex2, hall),
    hfind, href, h0, h1, h2, h3, hta, hca, ih)

law pieces_valid:
  for +fa: List<&2, B.Contig>
  for +raw: String
  for +ref: Bs()
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +rest: Ss()
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +alts: Ss()
  for +i: Nat
  for +xs: Vs()
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts}
  for +hr: {B.Alleles.read(alts) == Some{xs} : MV()}
  for hall: ALLV(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, xs)
  for +hfind: {B.Fasta.find(fa, f0) == Some{raw} : Maybe<&2, String>}
  for +href: {B.Allele.read(f3) == Some{ref} : Maybe<&2, Bs()>}
  for +h0: {ST.noc(f0, '\t') == True{} : Bool}
  for +h1: {ST.noc(f1, '\t') == True{} : Bool}
  for +h2: {ST.noc(f2, '\t') == True{} : Bool}
  for +h3: {ST.noc(f3, '\t') == True{} : Bool}
  for +hat: {ST.allnoc(alts, '\t') == True{} : Bool}
  for +hac: {ST.allnoc(alts, ',') == True{} : Bool}
  {L.all_line_valid(fa, ps) == True{} : Bool}

def pieces_valid(fa, raw, ref, f0, f1, f2, f3, f4, rest, defs, over0, n, alts, i, xs, ps, h, hr, hall, hfind, href, h0, h1, h2, h3, hat, hac):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), SI.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {L.all_line_valid(fa, _) == True{} : Bool}
      {==}
    case Con{+a, +t}:
      pv.c(fa, raw, ref, f0, f1, f2, f3, f4, rest, defs, over0, n, i, a, t, xs, ps, h, rd_k(B.Allele.read(a), B.Alleles.read(t), xs, hr), hall,
        hfind, href, h0, h1, h2, h3, AB.and_true_l(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat), AB.and_true_l(ST.noc(a, ','), ST.allnoc(t, ','), hac),
        +ps2 => hp2 => et2 => vt2 => pieces_valid(fa, raw, ref, f0, f1, f2, f3, f4, rest, defs, over0, n, t, 1n+i, tlx(xs), ps2, hp2, et2, vt2, hfind, href, h0, h1, h2, h3,
          AB.and_true_r(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat), AB.and_true_r(ST.noc(a, ','), ST.allnoc(t, ','), hac)))

def CTG(+fa: List<&2, B.Contig>, +fs: Ss()) -> Bool:
  L.line_valid.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs)

def sv_ref(+fa: List<&2, B.Contig>, +raw: String, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(String.split(f4, ','), F5(f0, f1, f2, f3, f4, rest), defs, o0, List.length(&2, String, String.split(f4, ',')), 1n)) == B.Pieces{ps} : B.Parts},
  +hfind: {B.Fasta.find(fa, f0) == Some{raw} : Maybe<&2, String>},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +h4: {ST.noc(f4, '\t') == True{} : Bool},
  +mr: Maybe<&2, Bs()>, +emr: {B.Allele.read(f3) == mr : Maybe<&2, Bs()>},
  +ma: MV(), +ema: {B.Alleles.read(String.split(f4, ',')) == ma : MV()},
  +hv: {L.line_valid.vars(mr, ma, SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest))) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  match mr ma:
    case Some{+ref} Some{+xs}:
      pieces_valid(fa, raw, ref, f0, f1, f2, f3, f4, rest, defs, o0, List.length(&2, String, String.split(f4, ',')), String.split(f4, ','), 1n, xs, ps, h, ema,
        valid_each(SEQ(raw), B.Rec.pos(F5(f0, f1, f2, f3, f4, rest)), ref, xs, hv), hfind, emr, h0, h1, h2, h3, ST.split_nod(f4, ',', '\t', h4), ST.split_all(f4, ','))
    case None{} _:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hv))
    case Some{+ref} None{}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hv))

def sv_find(+fa: List<&2, B.Contig>, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(String.split(f4, ','), F5(f0, f1, f2, f3, f4, rest), defs, o0, List.length(&2, String, String.split(f4, ',')), 1n)) == B.Pieces{ps} : B.Parts},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +h4: {ST.noc(f4, '\t') == True{} : Bool},
  +mf: Maybe<&2, String>, +emf: {B.Fasta.find(fa, f0) == mf : Maybe<&2, String>},
  +hv: {L.line_valid.contig(mf, F5(f0, f1, f2, f3, f4, rest)) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  match mf:
    case None{}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hv))
    case Some{+raw}:
      sv_ref(fa, raw, f0, f1, f2, f3, f4, rest, defs, o0, ps, h, emf, h0, h1, h2, h3, h4, B.Allele.read(f3), {==}, B.Alleles.read(String.split(f4, ',')), {==}, hv)

def sv_fs(fs: Ss(), +fa: List<&2, B.Contig>, +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts},
  +hall: {ST.allnoc(fs, '\t') == True{} : Bool},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))) == True{} : Bool},
  +hv: {CTG(fa, fs) == True{} : Bool}) -> {L.all_line_valid(fa, ps) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hn2))
    case Con{+f0, Nil{}}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, +rest}}}}}:
      +a1 = AB.and_true_r(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall)
      +a2 = AB.and_true_r(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1)
      +a3 = AB.and_true_r(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2)
      +a4 = AB.and_true_r(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3)
      sv_find(fa, f0, f1, f2, f3, f4, rest, defs, o0, ps, h,
        AB.and_true_l(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall),
        AB.and_true_l(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1),
        AB.and_true_l(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2),
        AB.and_true_l(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3),
        AB.and_true_l(ST.noc(f4, '\t'), ST.allnoc(rest, '\t'), a4),
        B.Fasta.find(fa, f0), {==}, hv)

def sv_split(+d: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))) == True{} : Bool},
  +hv: {CTG(fa, B.Rec.fields(body)) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      sv_fs(fs, fa, defs, o0, ps, h2, ST.split_all(body, '\t'), hn2, hv)

def sv_if(+c: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {SI.COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(SI.COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts},
  +hv: {CTG(fa, B.Rec.fields(body)) == True{} : Bool}) ->
  {L.all_line_valid(fa, ps) == True{} : Bool}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.all_line_valid(fa, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      sv_split(B.Alts.distinct(al), fa, defs, o0, body, ps, {==}, h2,
        AB.and_true_r(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, al)), e), hv)

# Law split_valid: if the line describes a valid variant on its contig, so
# does each record.
law split_valid:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +hv: {L.line_valid(fa, body) == True{} : Bool}
  {L.all_line_valid(fa, ps) == True{} : Bool}

def split_valid(fa, defs, o, body, ps, h, hv):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      sv_if(SI.COND(sp, B.Rec.fields(body)), fa, defs, o0, sp, body, ps, {==}, CR.cr_h(SI.COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h), hv)
