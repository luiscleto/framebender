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

# The text judge gives a line has as many ALTs as the line (a normalized
# record keeps one allele per ALT). So a record with one ALT is written with
# one ALT, and a second run under -m leaves it whole.

def Bs() -> Data:
  List<&2, B.Base>

def Vs() -> Data:
  List<&2, List<&2, B.Base>>

def NA(+b: String) -> Nat:
  L.n_alts(b)

law haps_len:
  for +seq: Bs()
  for +p: Nat
  for +r: Bs()
  for +xs: Vs()
  {List.length(&2, Bs(), L.haps.go(seq, p, r, xs)) == List.length(&2, Bs(), xs) : Nat}

def haps_len(seq, p, r, xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Bs(), L.haps.go(seq, p, r, t)), List.length(&2, Bs(), t), haps_len(seq, p, r, t))

# A list of ALT strings that reads as the alleles xs has their number.
law read_len:
  for +ss: List<&2, String>
  for +xs: Vs()
  for +h: {B.Alleles.read(ss) == Some{xs} : Maybe<&2, Vs()>}
  {List.length(&2, Bs(), xs) == J.slen(ss) : Nat}

def read_len(ss, xs, h):
  P.eq_sound(List.length(&2, Bs(), xs), J.slen(ss),
    {(%h : {C.alm(_, J.slen(ss)) == True{} : Bool}; C.alleles_len(ss)) : {C.alm(Some{xs}, J.slen(ss)) == True{} : Bool}})

# A normalized line: its rebuilt text has the line's ALTs.
def nz_alts(+fa: List<&2, B.Contig>, +b: String, +raw: String, +ref: Bs(), +alts: Vs(), w: B.Var,
  +ew: {Tan.normal(B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == w : B.Var},
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == Some{alts} : Maybe<&2, Vs()>},
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == None{} : Maybe<&2, B.Code>}) ->
  {NA(B.Rec.rebuild(N.FS(b), N.VV(b, ref, alts), w)) == NA(b) : Nat}:
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
      +f4 = J.fa_f4(fs, q, s, y, i2, k, hl)
      +aF = {(%Equal.sym(String, B.Rec.field(F, 4n), J.J(y), f4) : {String.split(_, ',') == B.Alleles.show(y) : List<&2, String>}; J.alts_rt.go(y, hy1)) :
        {B.Rec.alts(F) == B.Alleles.show(y) : List<&2, String>}}
      +hA = {(%Equal.sym(List<&2, String>, B.Rec.alts(F), B.Alleles.show(y), aF) : {B.Alleles.read(_) == Some{y} : Maybe<&2, Vs()>}; C.alleles_rt(y)) :
        {B.Alleles.read(B.Rec.alts(F)) == Some{y} : Maybe<&2, Vs()>}}
      +hc = {(%ew : {L.haps(seq, _) == L.haps(seq, v) : Vs()}; PV.same_change(seq, v, hvv)) : {L.haps(seq, W) == L.haps(seq, v) : Vs()}}
      +ly = read_len(B.Rec.alts(F), y, hA)
      +la = read_len(B.Rec.alts(fs), alts, ea)
      +hy = haps_len(seq, q, s, y)
      +hx = Equal.sym(Nat, List.length(&2, Bs(), L.haps.go(seq, B.Rec.pos(fs), ref, alts)), List.length(&2, Bs(), alts), haps_len(seq, B.Rec.pos(fs), ref, alts))
      %Equal.sym(List<&2, String>, String.split(String.join(F, "\t"), '\t'), F, rf) :
        {J.slen(B.Rec.alts(_)) == NA(b) : Nat}
      %ly : {_ == NA(b) : Nat}
      %hy : {_ == NA(b) : Nat}
      %Equal.sym(Vs(), L.haps(seq, W), L.haps(seq, v), hc) : {List.length(&2, Bs(), _) == NA(b) : Nat}
      %hx : {_ == NA(b) : Nat}
      la

def wn.problem(c: Maybe<&2, B.Code>, +fa: List<&2, B.Contig>, +b: String, +raw: String, +ref: Bs(), +alts: Vs(), +eok: Bool,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == Some{ref} : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == Some{alts} : Maybe<&2, Vs()>},
  +heok: {B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)) == eok : Bool},
  +ec: {L.checks(eok, B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == c : Maybe<&2, B.Code>}) ->
  {NA(L.res_text(L.problem(c, N.FS(b), b, B.Bases.of_fasta(raw), N.VV(b, ref, alts)))) == NA(b) : Nat}:
  match c:
    case Some{+cd}:
      {==}
    case None{}:
      +seq = B.Bases.of_fasta(raw)
      +v = N.VV(b, ref, alts)
      +ec2 = Equal.trans(Maybe<&2, B.Code>, L.checks(B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), seq, v), L.checks(eok, seq, v), None{},
        Equal.cong(Bool, Maybe<&2, B.Code>, z => L.checks(z, seq, v), B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)), eok, heok), ec)
      nz_alts(fa, b, raw, ref, alts, Tan.normal(seq, v), {==}, em, ef, er, ea, ec2)

def wn.bases(+eok: Bool, r: Maybe<&2, Bs()>, a: Maybe<&2, Vs()>, +fa: List<&2, B.Contig>, +b: String, +raw: String,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(N.FS(b), 3n)) == r : Maybe<&2, Bs()>},
  +ea: {B.Alleles.read(B.Rec.alts(N.FS(b))) == a : Maybe<&2, Vs()>},
  +heok: {B.Info.end_ok(B.Rec.field(N.FS(b), 7n), N.E1(b)) == eok : Bool}) ->
  {NA(L.res_text(L.judge.bases(eok, r, a, N.FS(b), b, B.Bases.of_fasta(raw)))) == NA(b) : Nat}:
  match r a:
    case Some{+ref} Some{+alts}:
      wn.problem(L.checks(eok, B.Bases.of_fasta(raw), N.VV(b, ref, alts)), fa, b, raw, ref, alts, eok, em, ef, er, ea, heok, {==})
    case None{} _:
      {==}
    case Some{+ref} None{}:
      {==}

def wn.contig(m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +b: String,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)) == m : Maybe<&2, String>}) ->
  {NA(L.res_text(L.judge.contig(m, N.FS(b), b))) == NA(b) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{+raw}:
      +fs = N.FS(b)
      wn.bases(B.Info.end_ok(B.Rec.field(fs, 7n), N.E1(b)), B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), fa, b, raw, em, ef, {==}, {==}, {==})

def wn.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +b: String, +em: {B.Rec.malformed(N.FS(b)) == bad : Bool}) ->
  {NA(L.res_text(L.judge.shape(bad, skip, fa, N.FS(b), b))) == NA(b) : Nat}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      wn.contig(B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)), fa, b, em, {==})

# The text judge gives a line has the line's ALTs.
law written_nalts:
  for +fa: List<&2, B.Contig>
  for +b: String
  {L.n_alts(L.written(fa, b)) == L.n_alts(b) : Nat}

def written_nalts(fa, b):
  wn.shape(B.Rec.malformed(N.FS(b)), B.Rec.out_of_scope(N.FS(b)), fa, b, {==})
