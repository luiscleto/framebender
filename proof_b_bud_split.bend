import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./protocol.bend as Pr
import ./norm_line.bend as J
import ./proof_b_cachedefs.bend as PC
import ./proof_b_defs.bend as P
import ./norm_seq.bend as Norm
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_xa.bend as BX
import ./proof_b_budget_mb.bend as BM
import ./proof_s_cr.bend as CR
import ./proof_s_site.bend as SI
import ./proof_s_str.bend as ST
import ./proof_fast.bend as PF
import ./proof_s_recs.bend as SR
import ./proof_base.bend as PB
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# A split line and the budget (-m): what B.Rec.parts' Pieces says of the line
# and its records, and why the records' allowances fit in the line's extra
# allowance (BN.xa). Every variable is reusable.
#   - the line passes Rec.parts' test (BN.cand), so its extra allowance is
#     nalts times its allowance;
#   - there are nalts records, each keeps the line's REF (so its allowance is
#     at most the line's) and has one ALT (so it has no extra allowance).

def Ss() -> Data:
  List<&2, String>

# ---------------------------------------------------------------------------
# Pieces: the test passed, the records made from every ALT
# ---------------------------------------------------------------------------

def PG(+fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss()) -> Data:
  {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts}

def pg_split(+d: Bool, +defs: B.Defs, +o0: Bool, +fs: Ss(), +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(fs)) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(fs)), B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}) -> PG(fs, defs, o0, ps):
  match d:
    case False{}:
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(PG(fs, defs, o0, ps), AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : PG(fs, defs, o0, ps)}

def pg_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +fs: Ss(), +ps: Ss(),
  +e: {SI.COND(sp, fs) == c : Bool},
  +h: {B.Rec.parts.if(SI.COND(sp, fs), False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}) ->
  PG(fs, defs, o0, ps) & {SI.COND(sp, fs) == True{} : Bool}:
  match c:
    case False{}:
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd(PG(fs, defs, o0, ps) & {SI.COND(sp, fs) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      (pg_split(B.Alts.distinct(B.Rec.alts(fs)), defs, o0, fs, ps, {==}, h2), e)

# A split line passed the test, and its records are those of its ALTs.
law parts_go:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  PG(B.Rec.fields(body), defs, R.Opts.over0(o), ps) & {SI.COND(R.Opts.split(o), B.Rec.fields(body)) == True{} : Bool}

def parts_go(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(body)
      pg_if(SI.COND(sp, fs), defs, o0, sp, fs, ps, {==},
        CR.cr_h(SI.COND(sp, fs), B.Text.has_cr(body), defs, o0, fs, ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))

# One record per ALT.
law pieces_len:
  for alts: Ss()
  for +fs: Ss()
  for +defs: B.Defs
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, fs, defs, o0, n, i)) == B.Pieces{ps} : B.Parts}
  {List.length(&2, String, ps) == List.length(&2, String, alts) : Nat}

def pieces_len(alts, fs, defs, o0, n, i, ps, h):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), SI.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {List.length(&2, String, _) == 0n : Nat}
      {==}
    case Con{+a, +t}:
      +g = B.Rec.piece(fs, a, defs, o0, n, i)
      +r = B.Parts.of(B.Rec.pieces.go(t, fs, defs, o0, n, 1n+i))
      +eg = SI.pc_g(g, r, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{SI.gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
      %Equal.sym(Ss(), ps, SI.gtext(g) <> SI.pieces_of(r), SI.pc_ps(SI.gtext(g), r, ps, h2g)) : {List.length(&2, String, _) == 1n+List.length(&2, String, t) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, String, SI.pieces_of(r)), List.length(&2, String, t),
        pieces_len(t, fs, defs, o0, n, 1n+i, SI.pieces_of(r), SI.pc_r(SI.gtext(g), r, ps, h2g)))

# Every record keeps the line's REF (field 3).
def ALLREF(+f3: String, ps: Ss()) -> Type:
  match ps:
    case Nil{}:
      Unit
    case +p <> t:
      {B.Rec.field(B.Rec.fields(p), 3n) == f3 : String} & ALLREF(f3, t)

def piece_ref(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +rest: Ss(), +a: String, +defs: B.Defs, +ks: Ss(), +over0: Bool, +n: Nat, +i: Nat, +x: String,
  +hj: {B.Got.join(B.Rec.piece.go(SI.F5(f0, f1, f2, f3, f4, rest), 0n, a, defs, ks, over0, n, i), "\t") == B.Got{x} : B.Got},
  +h0: {ST.noc(f0, '\t') == True{} : Bool}, +h1: {ST.noc(f1, '\t') == True{} : Bool}, +h2: {ST.noc(f2, '\t') == True{} : Bool}, +h3: {ST.noc(f3, '\t') == True{} : Bool},
  +ha: {ST.noc(a, '\t') == True{} : Bool}) -> {B.Rec.field(B.Rec.fields(x), 3n) == f3 : String}:
  +R = SI.XL(B.Rec.piece.go(rest, 5n, a, defs, ks, over0, n, i))
  +E = SI.piece_fields(f0, f1, f2, f3, f4, rest, a, defs, ks, over0, n, i, x, hj, h0, h1, h2, h3, ha)
  +G = {Con{f0, Con{f1, Con{f2, Con{f3, Con{a, R}}}}} : Ss()}
  {%Equal.sym(Ss(), B.Rec.fields(x), G, E) : {B.Rec.field(_, 3n) == f3 : String}; {==} : {B.Rec.field(B.Rec.fields(x), 3n) == f3 : String}}

law pieces_ref:
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
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, SI.F5(f0, f1, f2, f3, f4, rest), defs, over0, n, i)) == B.Pieces{ps} : B.Parts}
  for +h0: {ST.noc(f0, '\t') == True{} : Bool}
  for +h1: {ST.noc(f1, '\t') == True{} : Bool}
  for +h2: {ST.noc(f2, '\t') == True{} : Bool}
  for +h3: {ST.noc(f3, '\t') == True{} : Bool}
  for +hat: {ST.allnoc(alts, '\t') == True{} : Bool}
  ALLREF(f3, ps)

def pieces_ref(alts, f0, f1, f2, f3, f4, rest, defs, over0, n, i, ps, h, h0, h1, h2, h3, hat):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), SI.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : ALLREF(f3, _)
      Unit{}
    case Con{+a, +t}:
      +FS = SI.F5(f0, f1, f2, f3, f4, rest)
      +g = B.Rec.piece(FS, a, defs, over0, n, i)
      +r = B.Parts.of(B.Rec.pieces.go(t, FS, defs, over0, n, 1n+i))
      +eg = SI.pc_g(g, r, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, r) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{SI.gtext(g)}, r) == B.Pieces{ps} : B.Parts}}
      %Equal.sym(Ss(), ps, SI.gtext(g) <> SI.pieces_of(r), SI.pc_ps(SI.gtext(g), r, ps, h2g)) : ALLREF(f3, _)
      (piece_ref(f0, f1, f2, f3, f4, rest, a, defs, String.split(B.Rec.field(FS, 8n), ':'), over0, n, i, SI.gtext(g), eg, h0, h1, h2, h3,
         AB.and_true_l(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat)),
       pieces_ref(t, f0, f1, f2, f3, f4, rest, defs, over0, n, 1n+i, SI.pieces_of(r), SI.pc_r(SI.gtext(g), r, ps, h2g), h0, h1, h2, h3,
         AB.and_true_r(ST.noc(a, '\t'), ST.allnoc(t, '\t'), hat)))

def site_ref(fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  h: PG(fs, defs, o0, ps),
  +hall: {ST.allnoc(fs, '\t') == True{} : Bool},
  +hn2: {Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))) == True{} : Bool}) -> ALLREF(SI.F(fs, 3n), ps):
  match fs:
    case Nil{}:
      Empty.absurd(ALLREF("", ps), AB.false_ne_true(hn2))
    case Con{+f0, Nil{}}:
      Empty.absurd(ALLREF("", ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd(ALLREF("", ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd(ALLREF("", ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd(ALLREF(f3, ps), AB.false_ne_true(hn2))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, +rest}}}}}:
      +a1 = AB.and_true_r(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall)
      +a2 = AB.and_true_r(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1)
      +a3 = AB.and_true_r(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2)
      +a4 = AB.and_true_r(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3)
      pieces_ref(String.split(f4, ','), f0, f1, f2, f3, f4, rest, defs, o0, List.length(&2, String, String.split(f4, ',')), 1n, ps, h,
        AB.and_true_l(ST.noc(f0, '\t'), ST.allnoc(Con{f1, Con{f2, Con{f3, Con{f4, rest}}}}, '\t'), hall),
        AB.and_true_l(ST.noc(f1, '\t'), ST.allnoc(Con{f2, Con{f3, Con{f4, rest}}}, '\t'), a1),
        AB.and_true_l(ST.noc(f2, '\t'), ST.allnoc(Con{f3, Con{f4, rest}}, '\t'), a2),
        AB.and_true_l(ST.noc(f3, '\t'), ST.allnoc(Con{f4, rest}, '\t'), a3),
        ST.split_nod(f4, ',', '\t', AB.and_true_l(ST.noc(f4, '\t'), ST.allnoc(rest, '\t'), a4)))

# The facts the budget needs of a split line l and its records ps.
def SPF(+o: B.Opts, +l: B.Line, +ps: Ss()) -> Type:
  {BN.cand(o, l) == True{} : Bool}
  & ({List.length(&2, String, ps) == BN.nalts(l) : Nat}
  & (ALLREF(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n), ps) & SI.ALLSITE(SI.F(B.Rec.fields(B.Line.body(l)), 0n), SI.F(B.Rec.fields(B.Line.body(l)), 1n), ps)))

law parts_spf:
  for +defs: B.Defs
  for +o: B.Opts
  for +l: B.Line
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, B.Line.body(l)) == B.Pieces{ps} : B.Parts}
  SPF(o, l, ps)

def spf.k(+defs: B.Defs, +o: B.Opts, +l: B.Line, +ps: Ss(),
  +h: {B.Rec.parts(defs, o, B.Line.body(l)) == B.Pieces{ps} : B.Parts},
  g: PG(B.Rec.fields(B.Line.body(l)), defs, R.Opts.over0(o), ps) & {SI.COND(R.Opts.split(o), B.Rec.fields(B.Line.body(l))) == True{} : Bool}) -> SPF(o, l, ps):
  match g:
    case (+hg, +hc):
      +body = B.Line.body(l)
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +hn2 = AB.and_true_r(Bool.and(R.Opts.split(o), Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, al)), hc)
      (hc, (pieces_len(al, fs, defs, R.Opts.over0(o), List.length(&2, String, al), 1n, ps, hg),
        (site_ref(fs, defs, R.Opts.over0(o), ps, hg, ST.split_all(body, '\t'), hn2), SI.parts_site(defs, o, body, ps, h))))

def parts_spf(defs, o, l, ps, h):
  spf.k(defs, o, l, ps, h, parts_go(defs, o, B.Line.body(l), ps, h))

# ---------------------------------------------------------------------------
# The machine's fields (J.pfs) agree on MALFORMED
# ---------------------------------------------------------------------------

def pm.k(+g: J.C7, +body: String, +hg: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : Ss()}) ->
  {B.Rec.malformed(J.pfs.g(g, body)) == B.Rec.malformed(B.Rec.fields(body)) : Bool}:
  match g:
    case J.Short{}:
      {==}
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      +x = J.info.if(J.noend(r), r)
      +y = J.Cut.f(J.cut(r))
      +T = PF.ctail(J.cut(r))
      +F = B.Rec.fields(body)
      +hF = Equal.trans(Ss(), F, f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), PF.FG(f0, f1, f2, f3, f4, f5, f6, y, T),
        Equal.sym(Ss(), f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), F, hg),
        Equal.cong(Ss(), Ss(), z => f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> z, String.split(r, '\t'), y <> T, PF.split_ft(r)))
      %Equal.sym(Ss(), F, PF.FG(f0, f1, f2, f3, f4, f5, f6, y, T), hF) : {B.Rec.malformed(PF.PG(f0, f1, f2, f3, f4, f5, f6, x)) == B.Rec.malformed(_) : Bool}
      PF.sh_mal(f0, f1, f2, f3, f4, f5, f6, x, y, T)

law pfs_mal:
  for +body: String
  {B.Rec.malformed(J.pfs(body)) == B.Rec.malformed(B.Rec.fields(body)) : Bool}

def pfs_mal(body):
  pm.k(J.c7(body), body, PF.c7_split(body))

# A split line's gate is open (it is not malformed).
def gate_spf(+o: B.Opts, +l: B.Line, +hc: {BN.cand(o, l) == True{} : Bool}) -> {BN.lgate(l) == True{} : Bool}:
  +fs = B.Rec.fields(B.Line.body(l))
  +hm = AB.and_true_r(R.Opts.split(o), Bool.not(B.Rec.malformed(fs)),
    AB.and_true_l(Bool.and(R.Opts.split(o), Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, BN.nalts(l)), hc))
  %Equal.sym(Bool, B.Rec.malformed(J.pfs(B.Line.body(l))), B.Rec.malformed(fs), pfs_mal(B.Line.body(l))) : {Bool.not(_) == True{} : Bool}
  hm

# ---------------------------------------------------------------------------
# The records' allowances
# ---------------------------------------------------------------------------

# The REF the machine reads (J.pfs' field 3) is Rec.fields'.
def lref_eq(+l: B.Line) -> {BN.lref(l) == String.length(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n)) : Nat}:
  Equal.cong(String, Nat, z => String.length(z), B.Rec.field(J.pfs(B.Line.body(l)), 3n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n), PF.pfs_field(B.Line.body(l), 3n, {==}))

# A line's allowance once its gate is open.
def XL(+fa: List<&2, B.Contig>, +R: Nat) -> Nat:
  Nat.add(Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(BN.ZW(fa), BN.ZW(fa)))

def la_x(+fa: List<&2, B.Contig>, +l: B.Line) -> {Nat.is_le(BN.LA(fa, l), XL(fa, String.length(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n)))) == True{} : Bool}:
  %lref_eq(l) : {Nat.is_le(BN.LA(fa, l), XL(fa, _)) == True{} : Bool}
  BM.pk_le(BN.lgate(l), XL(fa, BN.lref(l)), XL(fa, BN.lref(l)), N.le_refl(XL(fa, BN.lref(l))))

def la_g(+fa: List<&2, B.Contig>, +l: B.Line, +hg: {BN.lgate(l) == True{} : Bool}) -> {BN.LA(fa, l) == XL(fa, String.length(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n))) : Nat}:
  %Equal.sym(Bool, BN.lgate(l), True{}, hg) : {BN.pick(_, XL(fa, BN.lref(l))) == XL(fa, String.length(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n))) : Nat}
  Equal.cong(Nat, Nat, z => XL(fa, z), BN.lref(l), String.length(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n)), lref_eq(l))

# The records (one line each, the split line's terminator) have at most the
# line's allowance each.
law las_recs:
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  for ps: Ss()
  for +term: String
  for +hg: {BN.lgate(l) == True{} : Bool}
  for hr: ALLREF(B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n), ps)
  {Nat.is_le(BN.LAs(fa, SR.LS(ps, term)), Nat.mul(List.length(&2, String, ps), BN.LA(fa, l))) == True{} : Bool}

def las_recs(fa, l, ps, term, hg, hr):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      (e3, ht) = hr
      +F3 = B.Rec.field(B.Rec.fields(B.Line.body(l)), 3n)
      +h1 = {%Equal.sym(Nat, BN.LA(fa, l), XL(fa, String.length(F3)), la_g(fa, l, hg)) : {Nat.is_le(BN.LA(fa, B.Line{p, term}), _) == True{} : Bool};
        %e3 : {Nat.is_le(BN.LA(fa, B.Line{p, term}), XL(fa, String.length(_))) == True{} : Bool};
        la_x(fa, B.Line{p, term}) : {Nat.is_le(BN.LA(fa, B.Line{p, term}), BN.LA(fa, l)) == True{} : Bool}}
      PB.le_add(BN.LA(fa, B.Line{p, term}), BN.LA(fa, l), BN.LAs(fa, SR.LS(t, term)), Nat.mul(List.length(&2, String, t), BN.LA(fa, l)),
        h1, las_recs(fa, l, t, term, hg, ht))

# The records have one ALT each: no extra allowance.
law xa_recs:
  for +o: B.Opts
  for +fa: List<&2, B.Contig>
  for ps: Ss()
  for +term: String
  for +f0: String
  for +f1: String
  for hs: SI.ALLSITE(f0, f1, ps)
  {BN.XA(o, fa, SR.LS(ps, term)) == 0n : Nat}

def xa_recs(o, fa, ps, term, f0, f1, hs):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      (s1, st) = hs
      (e0, s2) = s1
      (e1, en) = s2
      +l = {B.Line{p, term} : B.Line}
      +M = Bool.and(R.Opts.split(o), Bool.not(B.Rec.malformed(B.Rec.fields(p))))
      +hc = {%Equal.sym(Nat, L.n_alts(p), 1n, en) : {Bool.and(M, Nat.is_le(2n, _)) == False{} : Bool}; N.and_false_r(M) : {BN.cand(o, l) == False{} : Bool}}
      %Equal.sym(Bool, BN.cand(o, l), False{}, hc) : {Nat.add(BN.pick(_, Nat.mul(BN.nalts(l), BN.LA(fa, l))), BN.XA(o, fa, SR.LS(t, term))) == 0n : Nat}
      xa_recs(o, fa, t, term, f0, f1, st)

# ---------------------------------------------------------------------------
# The split step: the line's share (its rem and its extra allowance) pays
# for its records' allowances
# ---------------------------------------------------------------------------

law las_app:
  for +fa: List<&2, B.Contig>
  for xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  {BN.LAs(fa, List.append(&2, B.Line, xs, ys)) == Nat.add(BN.LAs(fa, xs), BN.LAs(fa, ys)) : Nat}

def las_app(fa, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +l <> +t:
      +X = BN.LA(fa, l)
      Equal.trans(Nat, Nat.add(X, BN.LAs(fa, List.append(&2, B.Line, t, ys))), Nat.add(X, Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys))),
        Nat.add(Nat.add(X, BN.LAs(fa, t)), BN.LAs(fa, ys)),
        Equal.cong(Nat, Nat, z => Nat.add(X, z), BN.LAs(fa, List.append(&2, B.Line, t, ys)), Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys)), las_app(fa, t, ys)),
        Equal.sym(Nat, Nat.add(Nat.add(X, BN.LAs(fa, t)), BN.LAs(fa, ys)), Nat.add(X, Nat.add(BN.LAs(fa, t), BN.LAs(fa, ys))), N.add_assoc(X, BN.LAs(fa, t), BN.LAs(fa, ys))))

law wa_las:
  for +fa: List<&2, B.Contig>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +ls: List<&2, B.Line>
  {Nat.is_le(BN.WA.ls(fa, fl, back, PC.mkWin(fa, wp), m, ls), BN.LAs(fa, ls)) == True{} : Bool}

def wa_las(fa, fl, back, wp, m, ls):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      N.le_add_mono_r(BN.LAs(fa, t), BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l), BN.LA(fa, l), BM.rem_le(fa, fl, back, wp, m, l))

# The records of l (ps, with l's terminator) in front of the lines t, in any
# state, have WA and XA within l's rem, extra allowance and t's.
law split_le:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +l: B.Line
  for +ps: Ss()
  for +term: String
  for +t: List<&2, B.Line>
  for +fl: Bool
  for +back: Nat
  for +wp: PC.WP
  for +m: Maybe<&2, List<&2, Pr.Req>>
  for +fl2: Bool
  for +back2: Nat
  for +wp2: PC.WP
  for +m2: Maybe<&2, List<&2, Pr.Req>>
  for hs: SPF(o, l, ps)
  {Nat.is_le(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, List.append(&2, B.Line, SR.LS(ps, term), t)), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, l <> t)) == True{} : Bool}

def split_le(fa, o, l, ps, term, t, fl, back, wp, m, fl2, back2, wp2, m2, hs):
  match hs:
    case (+hc, q1):
      match q1:
        case (+hn, q2):
          match q2:
            case (hr, hsi):
              +LSp = SR.LS(ps, term)
              +A = List.append(&2, B.Line, LSp, t)
              +K = Nat.mul(List.length(&2, String, ps), BN.LA(fa, l))
              +XA1 = BN.xa(o, fa, l)
              +R1 = BN.rem(fa, fl, back, PC.mkWin(fa, wp), m, l)
              +LTt = BN.LAs(fa, t)
              +XT = BN.XA(o, fa, t)
              +hg = gate_spf(o, l, hc)
              # WA: at most the records' allowances and t's.
              +hw = N.le_trans(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, A), BN.LAs(fa, A), Nat.add(K, LTt),
                wa_las(fa, fl2, back2, wp2, m2, A),
                {%Equal.sym(Nat, BN.LAs(fa, A), Nat.add(BN.LAs(fa, LSp), LTt), las_app(fa, LSp, t)) : {Nat.is_le(_, Nat.add(K, LTt)) == True{} : Bool};
                  N.le_add_mono_r(LTt, BN.LAs(fa, LSp), K, las_recs(fa, l, ps, term, hg, hr)) : {Nat.is_le(BN.LAs(fa, A), Nat.add(K, LTt)) == True{} : Bool}})
              # XA: the records' is 0.
              +ex = Equal.trans(Nat, BN.XA(o, fa, A), Nat.add(BN.XA(o, fa, LSp), XT), XT, BX.xa_app(o, fa, LSp, t),
                Equal.cong(Nat, Nat, z => Nat.add(z, XT), BN.XA(o, fa, LSp), 0n, xa_recs(o, fa, ps, term, SI.F(B.Rec.fields(B.Line.body(l)), 0n), SI.F(B.Rec.fields(B.Line.body(l)), 1n), hsi)))
              # K is the line's extra allowance.
              +ek = {%Equal.sym(Bool, BN.cand(o, l), True{}, hc) : {BN.pick(_, Nat.mul(BN.nalts(l), BN.LA(fa, l))) == K : Nat};
                Equal.cong(Nat, Nat, z => Nat.mul(z, BN.LA(fa, l)), BN.nalts(l), List.length(&2, String, ps), Equal.sym(Nat, List.length(&2, String, ps), BN.nalts(l), hn)) : {XA1 == K : Nat}}
              +e1 = Equal.trans(Nat, Nat.add(Nat.add(K, LTt), XT), Nat.add(K, Nat.add(LTt, XT)), Nat.add(LTt, Nat.add(K, XT)), N.add_assoc(K, LTt, XT), N.add_left_comm(K, LTt, XT))
              +hx = {%Equal.sym(Nat, BN.XA(o, fa, A), XT, ex) : {Nat.is_le(_, XT) == True{} : Bool}; N.le_refl(XT) : {Nat.is_le(BN.XA(o, fa, A), XT) == True{} : Bool}}
              +h2 = {%Equal.sym(Nat, XA1, K, ek) : {Nat.is_le(Nat.add(Nat.add(K, LTt), XT), Nat.add(Nat.add(R1, LTt), Nat.add(_, XT))) == True{} : Bool};
                %Equal.sym(Nat, Nat.add(Nat.add(K, LTt), XT), Nat.add(LTt, Nat.add(K, XT)), e1) : {Nat.is_le(_, Nat.add(Nat.add(R1, LTt), Nat.add(K, XT))) == True{} : Bool};
                N.le_add_mono_r(Nat.add(K, XT), LTt, Nat.add(R1, LTt), N.le_add_l(LTt, R1)) :
                {Nat.is_le(Nat.add(Nat.add(K, LTt), XT), Nat.add(Nat.add(R1, LTt), Nat.add(XA1, XT))) == True{} : Bool}}
              N.le_trans(BN.WAX(fa, o, fl2, back2, PC.mkWin(fa, wp2), m2, A), Nat.add(Nat.add(K, LTt), XT), BN.WAX(fa, o, fl, back, PC.mkWin(fa, wp), m, l <> t),
                PB.le_add(BN.WA.ls(fa, fl2, back2, PC.mkWin(fa, wp2), m2, A), Nat.add(K, LTt), BN.XA(o, fa, A), XT, hw, hx), h2)

# The records of a split line on its text (SR, inject.r) in front of the
# sources xs: their lines, then those of xs.
law all_rs:
  for ps: Ss()
  for +tm: String
  for +xs: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +cs: List<&2, String>
  {BN.ALL(Norm.recs_src(ps, tm, P.mkSrcs(xs)), P.mkPd(pd), eof, cs) == List.append(&2, B.Line, SR.LS(ps, tm), BN.ALL(P.mkSrcs(xs), P.mkPd(pd), eof, cs)) : List<&2, B.Line>}

def all_rs(ps, tm, xs, pd, eof, cs):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => B.Line{p, tm} <> z,
        BN.ALL(Norm.recs_src(t, tm, P.mkSrcs(xs)), P.mkPd(pd), eof, cs), List.append(&2, B.Line, SR.LS(t, tm), BN.ALL(P.mkSrcs(xs), P.mkPd(pd), eof, cs)),
        all_rs(t, tm, xs, pd, eof, cs))
