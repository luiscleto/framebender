import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./run.bend as R
import ./proof_run_text.bend as X
import ./proof_run_dec.bend as D
import ./proof_run_rec.bend as C
import ./proof_run_rejudge.bend as J
import ./proof_run_line.bend as N
import ./tan.bend as Tan
import ./proof_var.bend as PV
import ./proof_s_str.bend as ST
import ./proof_s_valid.bend as V
import ./proof_s_same.bend as SM
import ./proof_s_site.bend as SI

# Law split_change. First, for any line: the text judge gives it makes the
# change the line makes (only a normalized line's text changes, and its
# normal form makes the same change). Then a record of a split line makes the
# change of its ALT. Every variable is reusable.

def Bs() -> Data:
  List<&2, B.Base>

def Vs() -> Data:
  List<&2, List<&2, B.Base>>

def LC(+fa: List<&2, B.Contig>, +b: String) -> Vs():
  L.line_change(fa, b)

# The written text
# ================

# A line read as a variant on the contig raw: its change.
def lc_b(+fa: List<&2, B.Contig>, +b: String, +raw: String, +ref: Bs(), +alts: Vs(),
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == Some{alts} : Maybe<&2, Vs()>}) ->
  {LC(fa, b) == L.haps(B.Bases.of_fasta(raw), N.VV(b, ref, alts)) : Vs()}:
  +fs = N.FS(b)
  +seq = B.Bases.of_fasta(raw)
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(fs, 0n)), Some{raw}, ef) :
    {L.line_change.contig(_, fs) == L.haps(seq, N.VV(b, ref, alts)) : Vs()}
  %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(B.Rec.field(fs, 3n)), Some{ref}, er) :
    {L.line_change.vars(_, B.Alleles.read(B.Rec.alts(fs)), seq, B.Rec.pos(fs)) == L.haps(seq, N.VV(b, ref, alts)) : Vs()}
  %Equal.sym(Maybe<&2, Vs()>, B.Alleles.read(B.Rec.alts(fs)), Some{alts}, ea) :
    {L.line_change.vars(Some{ref}, _, seq, B.Rec.pos(fs)) == L.haps(seq, N.VV(b, ref, alts)) : Vs()}
  {==}

# A normalized line: its rebuilt text makes the line's change.
def nz_case(+fa: List<&2, B.Contig>, +b: String, +raw: String, +ref: Bs(), +alts: Vs(), w: B.Var,
  +ew: {Tan.normal(B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == w : B.Var},
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == Some{alts} : Maybe<&2, Vs()>},
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == None{} : Maybe<&2, B.Code>}) ->
  {LC(fa, B.Rec.rebuild(N.FS(b), N.VV(b, ref, alts), w)) == L.haps(B.Bases.of_fasta(raw), N.VV(b, ref, alts)) : Vs()}:
  match w:
    case B.Var{+q, +s, +y}:
      +fs = N.FS(b)
      +seq = B.Bases.of_fasta(raw)
      +v = N.VV(b, ref, alts)
      +W = {B.Var{q, s, y} : B.Var}
      +f3 = B.Rec.field(fs, 3n)
      +info = B.Rec.field(fs, 7n)
      +mv = B.Rec.moved(v, W)
      +i2 = N.info2(mv, info, q, s, y)
      +e2 = Nat.sub(Nat.add(q, L.len(s)), 1n)
      +hvv = N.nz_valid(fs, seq, ref, alts, B.Info.end_ok(info, N.E1(b)), em, er, ea, ec)
      +hv = {(%ew : {L.valid(seq, _) == True{} : Bool}; PV.stays_valid(seq, v, hvv)) : {L.valid(seq, W) == True{} : Bool}}
      +or4 = Bool.or(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
        Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3)))
      +or2F = P.or_false_inv(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n))),
        P.or_false_inv(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))),
          Bool.not(B.Text.is_letters(f3)), P.or_false_inv(or4, B.Text.any_empty(B.Rec.alts(fs)), em)))
      +m1 = P.or_false_inv(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n)), or2F)
      +k = Nat.sub(J.slen(fs), 8n)
      +hl = J.ge8(J.slen(fs), m1)
      +htab = X.pieces_noc(b, '\t')
      +hi2 = N.inf_noc(mv, info, q, s, y, '\t', C.field_noc(fs, 7n, '\t', htab), C.digits_noc(Nat.show(e2), '\t', D.show_digits(e2), {==}), {==})
      +F = J.fsA(fs, q, s, y, i2)
      +rf = J.rb_fields(fs, q, s, y, i2, k, hl, htab, hi2)
      +hy1 = C.valid_c3(seq, q, s, y, hv)
      +f1 = J.fa_f1(fs, q, s, y, i2, k, hl)
      +f3e = J.fa_f3(fs, q, s, y, i2, k, hl)
      +f4 = J.fa_f4(fs, q, s, y, i2, k, hl)
      +ef0 = J.fa_f0(fs, q, s, y, i2)
      +aF = {(%Equal.sym(String, B.Rec.field(F, 4n), J.J(y), f4) : {String.split(_, ',') == B.Alleles.show(y) : List<&2, String>}; J.alts_rt.go(y, hy1)) :
        {B.Rec.alts(F) == B.Alleles.show(y) : List<&2, String>}}
      +pF = {(%Equal.sym(String, B.Rec.field(F, 1n), Nat.show(q), f1) : {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == q : Nat};
        %Equal.sym(Maybe<&2, Nat>, B.Pos.read(Nat.show(q)), Some{q}, D.show_read(q)) : {Maybe.default(&2, Nat, _, 0n) == q : Nat}; {==}) : {B.Rec.pos(F) == q : Nat}}
      +hR = {(%Equal.sym(String, B.Rec.field(F, 3n), B.Allele.show(s), f3e) : {B.Allele.read(_) == Some{s} : Maybe<&2, Bs()>}; C.allele_rt(s)) :
        {B.Allele.read(B.Rec.field(F, 3n)) == Some{s} : Maybe<&2, Bs()>}}
      +hA = {(%Equal.sym(List<&2, String>, B.Rec.alts(F), B.Alleles.show(y), aF) : {B.Alleles.read(_) == Some{y} : Maybe<&2, Vs()>}; C.alleles_rt(y)) :
        {B.Alleles.read(B.Rec.alts(F)) == Some{y} : Maybe<&2, Vs()>}}
      +hc = PV.same_change(seq, v, hvv)
      %Equal.sym(List<&2, String>, String.split(String.join(F, "\t"), '\t'), F, rf) :
        {L.line_change.contig(B.Fasta.find(fa, B.Rec.field(_, 0n)), _) == L.haps(seq, v) : Vs()}
      %Equal.sym(String, B.Rec.field(F, 0n), B.Rec.field(fs, 0n), ef0) : {L.line_change.contig(B.Fasta.find(fa, _), F) == L.haps(seq, v) : Vs()}
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(fs, 0n)), Some{raw}, ef) : {L.line_change.contig(_, F) == L.haps(seq, v) : Vs()}
      %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(B.Rec.field(F, 3n)), Some{s}, hR) :
        {L.line_change.vars(_, B.Alleles.read(B.Rec.alts(F)), seq, B.Rec.pos(F)) == L.haps(seq, v) : Vs()}
      %Equal.sym(Maybe<&2, Vs()>, B.Alleles.read(B.Rec.alts(F)), Some{y}, hA) :
        {L.line_change.vars(Some{s}, _, seq, B.Rec.pos(F)) == L.haps(seq, v) : Vs()}
      %Equal.sym(Nat, B.Rec.pos(F), q, pF) : {L.haps(seq, B.Var{_, s, y}) == L.haps(seq, v) : Vs()}
      {(%ew : {L.haps(seq, _) == L.haps(seq, v) : Vs()}; hc) : {L.haps(seq, W) == L.haps(seq, v) : Vs()}}

def wc.problem(c: Maybe<&2, B.Code>, +fa: List<&2, B.Contig>, +b: String, +raw: String, +ref: Bs(), +alts: Vs(), +eok: Bool,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == Some{alts} : Maybe<&2, Vs()>},
  +heok: {B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)) == eok : Bool},
  +ec: {L.checks(eok, B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == c : Maybe<&2, B.Code>}) ->
  {LC(fa, L.res_text(L.problem(c, N.FS(b), b, B.Bases.of_fasta(raw), N.VV(b, ref, alts)))) == LC(fa, b) : Vs()}:
  match c:
    case Some{+cd}:
      {==}
    case None{}:
      +seq = B.Bases.of_fasta(raw)
      +v = N.VV(b, ref, alts)
      +ec2 = Equal.trans(Maybe<&2, B.Code>, L.checks(B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), seq, v), L.checks(eok, seq, v), None{},
        Equal.cong(Bool, Maybe<&2, B.Code>, z => L.checks(z, seq, v), B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), eok, heok), ec)
      Equal.trans(Vs(), LC(fa, B.Rec.rebuild(N.FS(b), v, Tan.normal(seq, v))), L.haps(seq, v), LC(fa, b),
        nz_case(fa, b, raw, ref, alts, Tan.normal(seq, v), {==}, em, ef, er, ea, ec2),
        Equal.sym(Vs(), LC(fa, b), L.haps(seq, v), lc_b(fa, b, raw, ref, alts, ef, er, ea)))

def wc.bases(+eok: Bool, r: Maybe<&2, Bs()>, a: Maybe<&2, Vs()>, +fa: List<&2, B.Contig>, +b: String, +raw: String,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == r : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == a : Maybe<&2, Vs()>},
  +heok: {B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)) == eok : Bool}) ->
  {LC(fa, L.res_text(L.judge.bases(eok, r, a, N.FS(b), b, B.Bases.of_fasta(raw)))) == LC(fa, b) : Vs()}:
  match r a:
    case Some{+ref} Some{+alts}:
      wc.problem(L.checks(eok, B.Bases.of_fasta(raw), N.VV(b, ref, alts)), fa, b, raw, ref, alts, eok, em, ef, er, ea, heok, {==})
    case None{} _:
      {==}
    case Some{+ref} None{}:
      {==}

def wc.contig(m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +b: String,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == m : Maybe<&2, String>}) ->
  {LC(fa, L.res_text(L.judge.contig(m, N.FS(b), b))) == LC(fa, b) : Vs()}:
  match m:
    case None{}:
      {==}
    case Some{+raw}:
      +fs = N.FS(b)
      wc.bases(B.Info.end_ok(B.Rec.field(fs, 7n), N.E1(b)), B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), fa, b, raw, em, ef, {==}, {==}, {==})

def wc.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +b: String, +em: {B.Rec.malformed(N.FS(b)) == bad : Bool}) ->
  {LC(fa, L.res_text(L.judge.shape(bad, skip, fa, N.FS(b), b))) == LC(fa, b) : Vs()}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      wc.contig(B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)), fa, b, em, {==})

# The text judge gives a line makes the line's change.
law written_change:
  for +fa: List<&2, B.Contig>
  for +b: String
  {L.line_change(fa, L.written(fa, b)) == L.line_change(fa, b) : Vs()}

def written_change(fa, b):
  wc.shape(B.Rec.malformed(N.FS(b)), B.Rec.out_of_scope(N.FS(b)), fa, b, {==})

# A record of a split line
# ========================

def Ss() -> Data:
  List<&2, String>

def some_inj(+x: String, +y: String, +h: {Some{x} == Some{y} : Maybe<&2, String>}) -> {x == y : String}:
  Equal.cong(Maybe<&2, String>, String, z => Maybe.default(&2, String, z, x), Some{x}, Some{y}, h)

def none_some(+y: String, +h: {None{} == Some{y} : Maybe<&2, String>}) -> Empty:
  P.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, z => Maybe.is_some(&2, String, z), None{}, Some{y}, h))

law ss_get:
  for +ps: Ss()
  for +i: Nat
  for +fs: Ss()
  for +p: String
  for +hs: {L.all_same_site(fs, ps) == True{} : Bool}
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  {L.same_site(fs, p) == True{} : Bool}

def ss_get(ps, i, fs, p, hs, hp):
  match ps i:
    case Nil{} _:
      Empty.absurd({L.same_site(fs, p) == True{} : Bool}, none_some(p, hp))
    case Con{+q, +t} 0n:
      {(%some_inj(q, p, hp) : {L.same_site(fs, _) == True{} : Bool}; P.and_true_l(L.same_site(fs, q), L.all_same_site(fs, t), hs)) : {L.same_site(fs, p) == True{} : Bool}}
    case Con{+q, +t} 1n+(+j):
      ss_get(t, j, fs, p, P.and_true_r(L.same_site(fs, q), L.all_same_site(fs, t), hs), hp)

law get_af:
  for +ps: Ss()
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  {List.get(&2, String, L.alt_fields(ps), i) == Some{B.Rec.field(B.Rec.fields(p), 4n)} : Maybe<&2, String>}

def get_af(ps, i, p, hp):
  match ps i:
    case Nil{} _:
      Empty.absurd({List.get(&2, String, L.alt_fields(Nil{}), i) == Some{B.Rec.field(B.Rec.fields(p), 4n)} : Maybe<&2, String>}, none_some(p, hp))
    case Con{+q, +t} 0n:
      Equal.cong(String, Maybe<&2, String>, z => Some{B.Rec.field(B.Rec.fields(z), 4n)}, q, p, some_inj(q, p, hp))
    case Con{+q, +t} 1n+(+j):
      get_af(t, j, p, hp)

law noc_get:
  for +xs: Ss()
  for +i: Nat
  for +a: String
  for +c: Char
  for +h: {ST.allnoc(xs, c) == True{} : Bool}
  for +hg: {List.get(&2, String, xs, i) == Some{a} : Maybe<&2, String>}
  {ST.noc(a, c) == True{} : Bool}

def noc_get(xs, i, a, c, h, hg):
  match xs i:
    case Nil{} _:
      Empty.absurd({ST.noc(a, c) == True{} : Bool}, none_some(a, hg))
    case Con{+q, +t} 0n:
      {(%some_inj(q, a, hg) : {ST.noc(_, c) == True{} : Bool}; P.and_true_l(ST.noc(q, c), ST.allnoc(t, c), h)) : {ST.noc(a, c) == True{} : Bool}}
    case Con{+q, +t} 1n+(+j):
      noc_get(t, j, a, c, P.and_true_r(ST.noc(q, c), ST.allnoc(t, c), h), hg)

def RD(+b: String, +t: Ss(), +xs: Vs()) -> Type:
  {B.Allele.read(b) == Some{V.hdx(xs)} : Maybe<&2, Bs()>} & ({B.Alleles.read(t) == Some{V.tlx(xs)} : Maybe<&2, Vs()>} & {xs == Con{V.hdx(xs), V.tlx(xs)} : Vs()})

def rdk0(+b: String, +t: Ss(), +a: String, +xs: Vs(), +hg: {Some{b} == Some{a} : Maybe<&2, String>}, r: RD(b, t, xs)) ->
  {B.Allele.read(a) == List.get(&2, Bs(), xs, 0n) : Maybe<&2, Bs()>}:
  match r:
    case (ea, q):
      match q:
        case (et, ex):
          %Equal.sym(Vs(), xs, Con{V.hdx(xs), V.tlx(xs)}, ex) : {B.Allele.read(a) == List.get(&2, Bs(), _, 0n) : Maybe<&2, Bs()>}
          {(%some_inj(b, a, hg) : {B.Allele.read(_) == Some{V.hdx(xs)} : Maybe<&2, Bs()>}; ea) : {B.Allele.read(a) == Some{V.hdx(xs)} : Maybe<&2, Bs()>}}

def rdk1(+b: String, +t: Ss(), +a: String, +xs: Vs(), +j: Nat, r: RD(b, t, xs),
  k: {B.Alleles.read(t) == Some{V.tlx(xs)} : Maybe<&2, Vs()>} -> {B.Allele.read(a) == List.get(&2, Bs(), V.tlx(xs), j) : Maybe<&2, Bs()>}) ->
  {B.Allele.read(a) == List.get(&2, Bs(), xs, 1n+j) : Maybe<&2, Bs()>}:
  match r:
    case (ea, q):
      match q:
        case (et, ex):
          %Equal.sym(Vs(), xs, Con{V.hdx(xs), V.tlx(xs)}, ex) : {B.Allele.read(a) == List.get(&2, Bs(), _, 1n+j) : Maybe<&2, Bs()>}
          k(et)

law rd_get:
  for +alts: Ss()
  for +i: Nat
  for +xs: Vs()
  for +a: String
  for +ha: {B.Alleles.read(alts) == Some{xs} : Maybe<&2, Vs()>}
  for +hg: {List.get(&2, String, alts, i) == Some{a} : Maybe<&2, String>}
  {B.Allele.read(a) == List.get(&2, Bs(), xs, i) : Maybe<&2, Bs()>}

def rd_get(alts, i, xs, a, ha, hg):
  match alts i:
    case Nil{} _:
      Empty.absurd({B.Allele.read(a) == List.get(&2, Bs(), xs, i) : Maybe<&2, Bs()>}, none_some(a, hg))
    case Con{+b, +t} 0n:
      rdk0(b, t, a, xs, hg, V.rd_k(B.Allele.read(b), B.Alleles.read(t), xs, ha))
    case Con{+b, +t} 1n+(+j):
      rdk1(b, t, a, xs, j, V.rd_k(B.Allele.read(b), B.Alleles.read(t), xs, ha), et => rd_get(t, j, V.tlx(xs), a, et, hg))

def some_injb(+x: Bs(), +y: Bs(), +h: {Some{x} == Some{y} : Maybe<&2, Bs()>}) -> {x == y : Bs()}:
  Equal.cong(Maybe<&2, Bs()>, Bs(), z => Maybe.default(&2, Bs(), z, x), Some{x}, Some{y}, h)

law haps_get:
  for +xs: Vs()
  for +i: Nat
  for +x: Bs()
  for +seq: Bs()
  for +pos: Nat
  for +ref: Bs()
  for +hx: {List.get(&2, Bs(), xs, i) == Some{x} : Maybe<&2, Bs()>}
  {List.get(&2, Bs(), L.haps.go(seq, pos, ref, xs), i) == Some{L.apply(seq, pos, ref, x)} : Maybe<&2, Bs()>}

def haps_get(xs, i, x, seq, pos, ref, hx):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, Bs(), L.haps.go(seq, pos, ref, Nil{}), i) == Some{L.apply(seq, pos, ref, x)} : Maybe<&2, Bs()>},
        P.false_ne_true(Equal.cong(Maybe<&2, Bs()>, Bool, z => Maybe.is_some(&2, Bs(), z), None{}, Some{x}, hx)))
    case Con{+y, +t} 0n:
      Equal.cong(Bs(), Maybe<&2, Bs()>, z => Some{L.apply(seq, pos, ref, z)}, y, x, some_injb(y, x, hx))
    case Con{+y, +t} 1n+(+j):
      haps_get(t, j, x, seq, pos, ref, hx)

law haps_none:
  for +xs: Vs()
  for +i: Nat
  for +seq: Bs()
  for +pos: Nat
  for +ref: Bs()
  for +hx: {List.get(&2, Bs(), xs, i) == None{} : Maybe<&2, Bs()>}
  {List.get(&2, Bs(), L.haps.go(seq, pos, ref, xs), i) == None{} : Maybe<&2, Bs()>}

def haps_none(xs, i, seq, pos, ref, hx):
  match xs i:
    case Nil{} _:
      {==}
    case Con{+y, +t} 0n:
      Empty.absurd({List.get(&2, Bs(), L.haps.go(seq, pos, ref, Con{y, t}), 0n) == None{} : Maybe<&2, Bs()>},
        P.false_ne_true(Equal.cong(Maybe<&2, Bs()>, Bool, z => Maybe.is_some(&2, Bs(), z), None{}, Some{y}, Equal.sym(Maybe<&2, Bs()>, Some{y}, None{}, hx))))
    case Con{+y, +t} 1n+(+j):
      haps_none(t, j, seq, pos, ref, hx)

def Rp(+fa: List<&2, B.Contig>, +body: String, +p: String, +i: Nat) -> Type:
  {LC(fa, p) == L.one_of(List.get(&2, Bs(), LC(fa, body), i)) : Vs()}

# The record's change read from its text, given the ALT's bases (mx).
def rec_lc(mx: Maybe<&2, Bs()>, +fa: List<&2, B.Contig>, +body: String, +p: String, +raw: String, +ref: Bs(),
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +e0: {B.Rec.field(N.FS(body), 0n) == B.Rec.field(N.FS(p), 0n) : String},
  +e1: {B.Rec.field(N.FS(body), 1n) == B.Rec.field(N.FS(p), 1n) : String},
  +e3: {B.Rec.field(N.FS(body), 3n) == B.Rec.field(N.FS(p), 3n) : String},
  +er: {B.Allele.read(B.Rec.field(N.FS(body), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +hca: {ST.noc(B.Rec.field(N.FS(p), 4n), ',') == True{} : Bool},
  +hr: {B.Allele.read(B.Rec.field(N.FS(p), 4n)) == mx : Maybe<&2, Bs()>}) ->
  {LC(fa, p) == L.line_change.vars(Some{ref}, B.Alleles.read.cons(mx, Some{Nil{}}), B.Bases.of_fasta(raw), B.Rec.pos(N.FS(body))) : Vs()}:
  +a = B.Rec.field(N.FS(p), 4n)
  +seq = B.Bases.of_fasta(raw)
  +R0 = L.line_change.vars(Some{ref}, B.Alleles.read.cons(mx, Some{Nil{}}), seq, B.Rec.pos(N.FS(body)))
  %e0 : {L.line_change.contig(B.Fasta.find(fa, _), N.FS(p)) == R0 : Vs()}
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(N.FS(body), 0n)), Some{raw}, ef) : {L.line_change.contig(_, N.FS(p)) == R0 : Vs()}
  %e3 : {L.line_change.vars(B.Allele.read(_), B.Alleles.read(B.Rec.alts(N.FS(p))), seq, B.Rec.pos(N.FS(p))) == R0 : Vs()}
  %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(B.Rec.field(N.FS(body), 3n)), Some{ref}, er) :
    {L.line_change.vars(_, B.Alleles.read(B.Rec.alts(N.FS(p))), seq, B.Rec.pos(N.FS(p))) == R0 : Vs()}
  %Equal.sym(Ss(), String.split(a, ','), [a], ST.split_noc(a, ',', hca)) :
    {L.line_change.vars(Some{ref}, B.Alleles.read(_), seq, B.Rec.pos(N.FS(p))) == R0 : Vs()}
  %Equal.sym(Maybe<&2, Bs()>, B.Allele.read(a), mx, hr) :
    {L.line_change.vars(Some{ref}, B.Alleles.read.cons(_, Some{Nil{}}), seq, B.Rec.pos(N.FS(p))) == R0 : Vs()}
  %e1 : {L.line_change.vars(Some{ref}, B.Alleles.read.cons(mx, Some{Nil{}}), seq, Maybe.default(&2, Nat, B.Pos.read(_), 0n)) == R0 : Vs()}
  {==}

def sc.x(mx: Maybe<&2, Bs()>, +fa: List<&2, B.Contig>, +body: String, +p: String, +i: Nat, +raw: String, +ref: Bs(), +xs: Vs(),
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +e0: {B.Rec.field(N.FS(body), 0n) == B.Rec.field(N.FS(p), 0n) : String},
  +e1: {B.Rec.field(N.FS(body), 1n) == B.Rec.field(N.FS(p), 1n) : String},
  +e3: {B.Rec.field(N.FS(body), 3n) == B.Rec.field(N.FS(p), 3n) : String},
  +er: {B.Allele.read(B.Rec.field(N.FS(body), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(body))) == Some{xs} : Maybe<&2, Vs()>},
  +hca: {ST.noc(B.Rec.field(N.FS(p), 4n), ',') == True{} : Bool},
  +hr: {B.Allele.read(B.Rec.field(N.FS(p), 4n)) == mx : Maybe<&2, Bs()>},
  +hx: {List.get(&2, Bs(), xs, i) == mx : Maybe<&2, Bs()>}) -> Rp(fa, body, p, i):
  match mx:
    case None{}:
      +seq = B.Bases.of_fasta(raw)
      +P0 = B.Rec.pos(N.FS(body))
      +l1 = rec_lc(None{}, fa, body, p, raw, ref, ef, e0, e1, e3, er, hca, hr)
      +eb = lc_b(fa, body, raw, ref, xs, ef, er, ea)
      +l2 = {(%Equal.sym(Vs(), LC(fa, body), L.haps(seq, N.VV(body, ref, xs)), eb) : {L.one_of(List.get(&2, Bs(), _, i)) == Nil{} : Vs()};
        %Equal.sym(Maybe<&2, Bs()>, List.get(&2, Bs(), L.haps.go(seq, P0, ref, xs), i), None{}, haps_none(xs, i, seq, P0, ref, hx)) : {L.one_of(_) == Nil{} : Vs()};
        {==}) : {L.one_of(List.get(&2, Bs(), LC(fa, body), i)) == Nil{} : Vs()}}
      Equal.trans(Vs(), LC(fa, p), Nil{}, L.one_of(List.get(&2, Bs(), LC(fa, body), i)), l1,
        Equal.sym(Vs(), L.one_of(List.get(&2, Bs(), LC(fa, body), i)), Nil{}, l2))
    case Some{+x}:
      +seq = B.Bases.of_fasta(raw)
      +P0 = B.Rec.pos(N.FS(body))
      +l1 = rec_lc(Some{x}, fa, body, p, raw, ref, ef, e0, e1, e3, er, hca, hr)
      +eb = lc_b(fa, body, raw, ref, xs, ef, er, ea)
      +Y = {[L.apply(seq, P0, ref, x)] : Vs()}
      +l2 = {(%Equal.sym(Vs(), LC(fa, body), L.haps(seq, N.VV(body, ref, xs)), eb) : {L.one_of(List.get(&2, Bs(), _, i)) == Y : Vs()};
        %Equal.sym(Maybe<&2, Bs()>, List.get(&2, Bs(), L.haps.go(seq, P0, ref, xs), i), Some{L.apply(seq, P0, ref, x)}, haps_get(xs, i, x, seq, P0, ref, hx)) : {L.one_of(_) == Y : Vs()};
        {==}) : {L.one_of(List.get(&2, Bs(), LC(fa, body), i)) == Y : Vs()}}
      Equal.trans(Vs(), LC(fa, p), Y, L.one_of(List.get(&2, Bs(), LC(fa, body), i)), l1,
        Equal.sym(Vs(), L.one_of(List.get(&2, Bs(), LC(fa, body), i)), Y, l2))

def sc.vars(r: Maybe<&2, Bs()>, am: Maybe<&2, Vs()>, +fa: List<&2, B.Contig>, +body: String, +p: String, +i: Nat, +raw: String,
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +e0: {B.Rec.field(N.FS(body), 0n) == B.Rec.field(N.FS(p), 0n) : String},
  +e1: {B.Rec.field(N.FS(body), 1n) == B.Rec.field(N.FS(p), 1n) : String},
  +e3: {B.Rec.field(N.FS(body), 3n) == B.Rec.field(N.FS(p), 3n) : String},
  +er: {B.Allele.read(B.Rec.field(N.FS(body), 3n)) == r : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(body))) == am : Maybe<&2, Vs()>},
  +hv: {L.line_valid.vars(r, am, B.Bases.of_fasta(raw), B.Rec.pos(N.FS(body))) == True{} : Bool},
  +ga: {List.get(&2, String, B.Rec.alts(N.FS(body)), i) == Some{B.Rec.field(N.FS(p), 4n)} : Maybe<&2, String>}) -> Rp(fa, body, p, i):
  match r am:
    case Some{+ref} Some{+xs}:
      +a = B.Rec.field(N.FS(p), 4n)
      sc.x(List.get(&2, Bs(), xs, i), fa, body, p, i, raw, ref, xs, ef, e0, e1, e3, er, ea,
        noc_get(B.Rec.alts(N.FS(body)), i, a, ',', ST.split_all(B.Rec.field(N.FS(body), 4n), ','), ga),
        rd_get(B.Rec.alts(N.FS(body)), i, xs, a, ea, ga), {==})
    case None{} _:
      Empty.absurd(Rp(fa, body, p, i), P.false_ne_true(hv))
    case Some{+ref} None{}:
      Empty.absurd(Rp(fa, body, p, i), P.false_ne_true(hv))

def sc.contig(m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +body: String, +p: String, +i: Nat,
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(body), 0n)) == m : Maybe<&2, String>},
  +hv: {L.line_valid.contig(m, N.FS(body)) == True{} : Bool},
  +e0: {B.Rec.field(N.FS(body), 0n) == B.Rec.field(N.FS(p), 0n) : String},
  +e1: {B.Rec.field(N.FS(body), 1n) == B.Rec.field(N.FS(p), 1n) : String},
  +e3: {B.Rec.field(N.FS(body), 3n) == B.Rec.field(N.FS(p), 3n) : String},
  +ga: {List.get(&2, String, B.Rec.alts(N.FS(body)), i) == Some{B.Rec.field(N.FS(p), 4n)} : Maybe<&2, String>}) -> Rp(fa, body, p, i):
  match m:
    case None{}:
      Empty.absurd(Rp(fa, body, p, i), P.false_ne_true(hv))
    case Some{+raw}:
      sc.vars(B.Allele.read(B.Rec.field(N.FS(body), 3n)), B.Alleles.read(B.Rec.alts(N.FS(body))), fa, body, p, i, raw, ef, e0, e1, e3, {==}, {==}, hv, ga)

law split_change_p:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +hv: {L.line_valid(fa, body) == True{} : Bool}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +hs: {L.stops(L.judge(fa, p), R.Opts.strict(o)) == False{} : Bool}
  {L.line_change(fa, L.written(fa, p)) == L.one_of(List.get(&2, Bs(), L.line_change(fa, body), i)) : Vs()}

def split_change_p(fa, defs, o, body, ps, h, hv, i, p, hp, hs):
  +fs = N.FS(body)
  +gs = N.FS(p)
  +ss = ss_get(ps, i, fs, p, SM.split_site(defs, o, body, ps, h), hp)
  +sf = P.and_true_r(Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)), L.same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n]), ss)
  +s0 = String.eq(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n))
  +s1 = String.eq(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n))
  +s2 = String.eq(B.Rec.field(fs, 2n), B.Rec.field(gs, 2n))
  +s3 = String.eq(B.Rec.field(fs, 3n), B.Rec.field(gs, 3n))
  +r0 = L.same_fields(fs, gs, [1n, 2n, 3n, 5n, 6n, 8n])
  +r1 = L.same_fields(fs, gs, [2n, 3n, 5n, 6n, 8n])
  +r2 = L.same_fields(fs, gs, [3n, 5n, 6n, 8n])
  +r3 = L.same_fields(fs, gs, [5n, 6n, 8n])
  +e0 = Q.str_eq_sound(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n), P.and_true_l(s0, r0, sf))
  +sf1 = P.and_true_r(s0, r0, sf)
  +e1 = Q.str_eq_sound(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n), P.and_true_l(s1, r1, sf1))
  +sf2 = P.and_true_r(s1, r1, sf1)
  +sf3 = P.and_true_r(s2, r2, sf2)
  +e3 = Q.str_eq_sound(B.Rec.field(fs, 3n), B.Rec.field(gs, 3n), P.and_true_l(s3, r3, sf3))
  +ga = Equal.trans(Maybe<&2, String>, List.get(&2, String, B.Rec.alts(fs), i), List.get(&2, String, L.alt_fields(ps), i), Some{B.Rec.field(gs, 4n)},
    Equal.sym(Maybe<&2, String>, List.get(&2, String, L.alt_fields(ps), i), List.get(&2, String, B.Rec.alts(fs), i),
      Equal.cong(Ss(), Maybe<&2, String>, z => List.get(&2, String, z, i), L.alt_fields(ps), B.Rec.alts(fs), SI.split_alts(defs, o, body, ps, h))),
    get_af(ps, i, p, hp))
  Equal.trans(Vs(), L.line_change(fa, L.written(fa, p)), LC(fa, p), L.one_of(List.get(&2, Bs(), L.line_change(fa, body), i)),
    written_change(fa, p),
    sc.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fa, body, p, i, {==}, hv, e0, e1, e3, ga))
