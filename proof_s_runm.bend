import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_s_laws.bend as SL

# Laws items_without_m and biallelic_run: without -m the records are the
# body lines; on a file whose body lines have one ALT each, -m changes
# nothing (no_m keeps the recorded arguments). Every variable is reusable.

# items_without_m
# ===============

def ostep_eq(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +h: {R.Opts.split(o) == False{} : Bool}, s: L.ItSt, +l: B.Line) ->
  {L.out_items.step(fa, defs, o, s, l) == L.items.step(fa, s, l) : L.ItSt}:
  match s:
    case L.ItSt{+i, +n, +acc}:
      match i:
        case False{}:
          {==}
        case True{}:
          %Equal.sym(B.Parts, B.Rec.parts(defs, o, B.Line.body(l)), B.Whole{}, SL.whole_without_m(defs, o, B.Line.body(l), h)) :
            {L.ItSt{True{}, 1n+n, List.append(&2, R.Item, acc, L.items.line(_, fa, l, 1n+n))} ==
              L.ItSt{True{}, 1n+n, List.append(&2, R.Item, acc, [L.item(fa, l, 1n+n)])} : L.ItSt}
          {==}

law oi_go:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +h: {R.Opts.split(o) == False{} : Bool}
  for +s: L.ItSt
  {L.out_items.go(ls, fa, defs, o, s) == L.items.go(ls, fa, s) : L.ItSt}

def oi_go(ls, fa, defs, o, h, s):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      %Equal.sym(L.ItSt, L.out_items.step(fa, defs, o, s, l), L.items.step(fa, s, l), ostep_eq(fa, defs, o, h, s, l)) :
        {L.out_items.go(t, fa, defs, o, _) == L.items.go(t, fa, L.items.step(fa, s, l)) : L.ItSt}
      oi_go(t, fa, defs, o, h, L.items.step(fa, s, l))

law items_without_m_p:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Opts.split(o) == False{} : Bool}
  {L.out_items(fasta, vcf, o) == L.items(fasta, vcf) : List<&2, R.Item>}

def items_without_m_p(fasta, vcf, o, h):
  +ls = B.Text.lines(vcf)
  +fa = B.Fasta.parse(fasta)
  Equal.cong(L.ItSt, List<&2, R.Item>, z => L.ItSt.acc(z), L.out_items.go(ls, fa, L.defs(vcf), o, L.ItSt{False{}, 0n, Nil{}}), L.items.go(ls, fa, L.ItSt{False{}, 0n, Nil{}}),
    oi_go(ls, fa, L.defs(vcf), o, h, L.ItSt{False{}, 0n, Nil{}}))

# biallelic_run
# =============

def bl_eq(r: B.Res, +st: R.RunSt, +s: Bool, +w: Nat, +m: Bool, +z: Bool, +a: List<&2, String>, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {R.body_line(r, st, B.Opts{s, w, m, z, a}, l, at, inpos) == R.body_line(r, st, B.Opts{s, w, False{}, z, a}, l, at, inpos) : R.RunSt}:
  match r:
    case B.Res{B.Broken{}, +k, +t, +x}:
      {==}
    case B.Res{B.NoContig{}, +k, +t, +x}:
      {==}
    case B.Res{B.Problem{+c}, +k, +t, +x}:
      {==}
    case B.Res{B.Skipped{}, +k, +t, +x}:
      {==}
    case B.Res{B.Normalized{}, +k, +t, +x}:
      {==}

def hl_eq(isc: Bool, st: R.RunSt, l: B.Line, +s: Bool, +w: Nat, +m: Bool, +z: Bool, +a: List<&2, String>) ->
  {R.head_line(isc, st, B.Opts{s, w, m, z, a}, l) == R.head_line(isc, st, B.Opts{s, w, False{}, z, a}, l) : R.RunSt}:
  match isc st l:
    case True{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x} B.Line{+bd, +term}:
      {==}
    case False{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x} B.Line{+bd, +term}:
      {==}

def sn.x(x: Bool, i: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +s: Bool, +w: Nat, +m: Bool, +z: Bool, +a: List<&2, String>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +l: B.Line, +hb: {Bool.or(Bool.not(i), Nat.is_lt(L.n_alts(B.Line.body(l)), 2n)) == True{} : Bool}) ->
  {L.line_step(fa, defs, B.Opts{s, w, m, z, a}, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, l) ==
   L.line_step(fa, defs, B.Opts{s, w, False{}, z, a}, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, l) : R.RunSt}:
  match x i:
    case True{} _:
      {==}
    case False{} False{}:
      hl_eq(R.is_chrom_line(B.Line.body(l)), R.RunSt{1n+n, False{}, h, c, e, la, b, k, out, ns, False{}}, l, s, w, m, z, a)
    case False{} True{}:
      +bd = B.Line.body(l)
      +fs = B.Rec.fields(bd)
      +O1 = {B.Opts{s, w, m, z, a} : B.Opts}
      +O2 = {B.Opts{s, w, False{}, z, a} : B.Opts}
      +ST1 = {R.RunSt{1n+n, True{}, h, c, e, la, b, k, out, ns, False{}} : R.RunSt}
      +AT = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +POS = B.Rec.pos(fs)
      %Equal.sym(B.Parts, B.Rec.parts(defs, O1, bd), B.Whole{}, SL.whole_biallelic(defs, O1, bd, hb)) :
        {L.body_in(_, fa, O1, ST1, l, AT, POS) == L.body_in(B.Rec.parts(defs, O2, bd), fa, O2, ST1, l, AT, POS) : R.RunSt}
      %Equal.sym(B.Parts, B.Rec.parts(defs, O2, bd), B.Whole{}, SL.whole_biallelic(defs, O2, bd, hb)) :
        {L.body_in(B.Whole{}, fa, O1, ST1, l, AT, POS) == L.body_in(_, fa, O2, ST1, l, AT, POS) : R.RunSt}
      bl_eq(L.judge(fa, bd), ST1, s, w, m, z, a, l, AT, POS)

# One line: the same step with and without -m, before the body or when the
# line has fewer than two ALTs.
def step_nm(+fa: List<&2, B.Contig>, +defs: B.Defs, o: B.Opts, st: R.RunSt, +l: B.Line,
  +hb: {Bool.or(Bool.not(R.RunSt.inbody(st)), Nat.is_lt(L.n_alts(B.Line.body(l)), 2n)) == True{} : Bool}) ->
  {L.line_step(fa, defs, o, st, l) == L.line_step(fa, defs, L.no_m(o), st, l) : R.RunSt}:
  match o st:
    case B.Opts{+s, +w, +m, +z, +a} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      sn.x(x, i, fa, defs, s, w, m, z, a, n, h, c, e, la, b, k, out, ns, l, hb)

def or_t(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hl_inb(isc: Bool, l: B.Line, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  {Bool.or(isc, Bool.not(R.RunSt.inbody(R.head_line(isc, R.RunSt{1n+n, False{}, h, c, e, la, b, k, out, ns, False{}}, o, l)))) == True{} : Bool}:
  match isc l:
    case True{} B.Line{+bd, +term}:
      {==}
    case False{} B.Line{+bd, +term}:
      {==}

def ib.x(x: Bool, i: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +l: B.Line) ->
  {Bool.or(Bool.or(i, R.is_chrom_line(B.Line.body(l))), Bool.not(R.RunSt.inbody(L.line_step(fa, defs, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, l)))) == True{} : Bool}:
  match x i:
    case True{} True{}:
      {==}
    case True{} False{}:
      or_t(R.is_chrom_line(B.Line.body(l)))
    case False{} True{}:
      {==}
    case False{} False{}:
      hl_inb(R.is_chrom_line(B.Line.body(l)), l, o, n, h, c, e, la, b, k, out, ns)

# A state in the body after a line was in the body before, or the line is
# the #CHROM line.
def inb_step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt, +l: B.Line) ->
  {Bool.or(Bool.or(R.RunSt.inbody(st), R.is_chrom_line(B.Line.body(l))), Bool.not(R.RunSt.inbody(L.line_step(fa, defs, o, st, l)))) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      ib.x(x, i, fa, defs, o, n, h, c, e, la, b, k, out, ns, l)

def or_r(a: Bool, +b: Bool, +hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def and_tt(a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

law go_true:
  for +t: List<&2, B.Line>
  for +x: Bool
  for +h: {L.biallelic.go(t, True{}) == True{} : Bool}
  {L.biallelic.go(t, x) == True{} : Bool}

def go_true(t, x, h):
  match t:
    case Nil{}:
      {==}
    case Con{+l, +r}:
      +lt = Nat.is_lt(L.n_alts(B.Line.body(l)), 2n)
      +isc = R.is_chrom_line(B.Line.body(l))
      and_tt(Bool.or(Bool.not(x), lt), L.biallelic.go(r, Bool.or(x, isc)),
        or_r(Bool.not(x), lt, P.and_true_l(lt, L.biallelic.go(r, True{}), h)),
        go_true(r, Bool.or(x, isc), P.and_true_r(lt, L.biallelic.go(r, True{}), h)))

def mono(+t: List<&2, B.Line>, a: Bool, b: Bool, +himp: {Bool.or(a, Bool.not(b)) == True{} : Bool}, +h: {L.biallelic.go(t, a) == True{} : Bool}) ->
  {L.biallelic.go(t, b) == True{} : Bool}:
  match a b:
    case True{} _:
      go_true(t, b, h)
    case False{} True{}:
      Empty.absurd({L.biallelic.go(t, True{}) == True{} : Bool}, P.false_ne_true(himp))
    case False{} False{}:
      h

law rg_nm:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +hb: {L.biallelic.go(ls, R.RunSt.inbody(st)) == True{} : Bool}
  {L.run.go(ls, fa, defs, o, st) == L.run.go(ls, fa, defs, L.no_m(o), st) : R.RunSt}

def rg_nm(ls, fa, defs, o, st, hb):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      +ib = R.RunSt.inbody(st)
      +lt = Nat.is_lt(L.n_alts(B.Line.body(l)), 2n)
      +isc = R.is_chrom_line(B.Line.body(l))
      +S1 = L.line_step(fa, defs, o, st, l)
      +S2 = L.line_step(fa, defs, L.no_m(o), st, l)
      +hb1 = P.and_true_l(Bool.or(Bool.not(ib), lt), L.biallelic.go(t, Bool.or(ib, isc)), hb)
      +hb2 = P.and_true_r(Bool.or(Bool.not(ib), lt), L.biallelic.go(t, Bool.or(ib, isc)), hb)
      +hb3 = mono(t, Bool.or(ib, isc), R.RunSt.inbody(S1), inb_step(fa, defs, o, st, l), hb2)
      Equal.trans(R.RunSt, L.run.go(t, fa, defs, o, S1), L.run.go(t, fa, defs, L.no_m(o), S1), L.run.go(t, fa, defs, L.no_m(o), S2),
        rg_nm(t, fa, defs, o, S1, hb3),
        Equal.cong(R.RunSt, R.RunSt, z => L.run.go(t, fa, defs, L.no_m(o), z), S1, S2, step_nm(fa, defs, o, st, l, hb1)))

law biallelic_run_p:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {L.biallelic(vcf) == True{} : Bool}
  {L.run(fasta, vcf, o) == L.run(fasta, vcf, L.no_m(o)) : R.Report}

def biallelic_run_p(fasta, vcf, o, h):
  +ls = B.Text.lines(vcf)
  +fa = B.Fasta.parse(fasta)
  Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, L.defs(vcf), o, R.start_st()), L.run.go(ls, fa, L.defs(vcf), L.no_m(o), R.start_st()),
    rg_nm(ls, fa, L.defs(vcf), o, R.start_st(), h))
