import Base
import ./types.bend as B
import ./tan.bend as Tan
import ./run.bend as R

# framebender: the laws.
#
# DRAFT 3 (2026-10-27): the science layer. The owner asked for two layers:
#
# Science (this file with types.bend, run.bend and tan.bend): what an expert
# reviews and approves once. Definitions (what a variant does, valid,
# normalized after Tan et al.), the whole-file definition run, and laws about
# them: the normal form is the same change, valid, normalized, unique and
# shortest; every record the tool normalizes is valid; a run sorts its output;
# running twice changes nothing. Nothing here mentions the program's code.
# tan.bend's algorithm need not be read: the laws same_change, stays_valid,
# standard_form and unique fix its result.
#
# Implementation (MACHINE.bend): the program writes exactly what run says. The
# program can change freely (faster, parallel); only proofs change.
#
# A law or definition, once approved, is never weakened or deleted without
# the owner's consent.
#
# The laws, from the top:
#   sorted, grouped_in, no_unsorted, twice_run   what run guarantees
#   normalized_valid                              records normalized are valid
#   same_change ... shortest, unique              the normal form of one variant
#   (MACHINE.bend: machine, usage)
#
# Sources: Tan, Abecasis and Kang, "Unified representation of genetic
# variants", Bioinformatics 2015; the VCF 4.3 specification; bcftools 1.24.

# ==========================================================================
# Definitions: what a variant does
# ==========================================================================

# A contig is the list of its bases. Positions are 1-based, as in VCF; list
# indexes are 0-based, so position p is index p - 1.

def len(xs: List<&2, B.Base>) -> Nat:
  List.length(&2, B.Base, xs)

# The n bases of xs from index i (fewer if xs ends first).
def slice(xs: List<&2, B.Base>, i: Nat, n: Nat) -> List<&2, B.Base>:
  List.take(&2, B.Base, List.drop(&2, B.Base, xs, i), n)

def pos_of(v: B.Var) -> Nat:
  match v:
    case B.Var{p, r, a}:
      p

# The contig after one alternative: the len(ref) bases from position pos are
# replaced by alt. Example: on contig GAAAT, pos 1, ref GA, alt G gives GAAT.
def apply(+seq: List<&2, B.Base>, +pos: Nat, ref: List<&2, B.Base>, alt: List<&2, B.Base>) -> List<&2, B.Base>:
  List.append(&2, B.Base, List.take(&2, B.Base, seq, Nat.sub(pos, 1n)),
    List.append(&2, B.Base, alt, List.drop(&2, B.Base, seq, Nat.add(Nat.sub(pos, 1n), len(ref)))))

def haps.go(+seq: List<&2, B.Base>, +pos: Nat, +ref: List<&2, B.Base>, alts: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match alts:
    case Nil{}:
      Nil{}
    case a <> t:
      apply(seq, pos, ref, a) <> haps.go(seq, pos, ref, t)

# What a variant does: the contig after each of its alternatives, in order.
def haps(+seq: List<&2, B.Base>, v: B.Var) -> List<&2, List<&2, B.Base>>:
  match v:
    case B.Var{+pos, +ref, alts}:
      haps.go(seq, pos, ref, alts)

# v and w make the same change: same number of alternatives, and each gives the
# same contig as the alternative at the same place in the other.
def same(+seq: List<&2, B.Base>, v: B.Var, w: B.Var) -> Bool:
  B.Alleles.eq(haps(seq, v), haps(seq, w))

def all_nonempty(xs: List<&2, List<&2, B.Base>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(1n, len(x)) && all_nonempty(t)

# A variant the tool normalizes: position at least 1; REF and at least one
# ALT, none of them empty; no two of REF and the ALTs equal; and REF is
# exactly the contig's bases at that position (so it also ends on the contig).
def valid(+seq: List<&2, B.Base>, v: B.Var) -> Bool:
  match v:
    case B.Var{+pos, +ref, +alts}:
      (Nat.is_le(1n, pos) && Nat.is_le(1n, len(ref))
        && Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) && all_nonempty(alts)
        && B.Alleles.distinct(ref <> alts)
        && B.Bases.eq(slice(seq, Nat.sub(pos, 1n), len(ref)), ref))

# ==========================================================================
# Definitions: normalized (Tan et al. 2015)
# ==========================================================================

def shift.alts(+seq: List<&2, B.Base>, +pos: Nat, +ref: List<&2, B.Base>, +i: Nat, alts: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match alts:
    case Nil{}:
      Nil{}
    case +a <> t:
      slice(apply(seq, pos, ref, a), i, len(a)) <> shift.alts(seq, pos, ref, i, t)

# v moved k bases to the left (for 1 <= k < pos), every allele keeping its
# length: REF becomes the contig's bases at the new place, each ALT the bases
# there of the contig that alternative gives.
def shift(+seq: List<&2, B.Base>, +v: B.Var, +k: Nat) -> B.Var:
  match v:
    case B.Var{+pos, +ref, +alts}:
      +p = Nat.sub(pos, k)
      +i = Nat.sub(p, 1n)
      B.Var{p, slice(seq, i, len(ref)), shift.alts(seq, pos, ref, i, alts)}

# Some shift by k, k-1, ..., 1 bases makes the same change.
def movable(+seq: List<&2, B.Base>, +v: B.Var, k: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+(+j):
      same(seq, shift(seq, v, 1n+j), v) || movable(seq, v, j)

# Left-aligned: "it is no longer possible to shift its position to the left
# while keeping the length of all its alleles constant" (Tan et al.), never
# moving before position 1.
def left_aligned(+seq: List<&2, B.Base>, +v: B.Var) -> Bool:
  Bool.not(movable(seq, v, Nat.sub(pos_of(v), 1n)))

def init(+xs: List<&2, B.Base>) -> List<&2, B.Base>:
  List.take(&2, B.Base, xs, Nat.sub(len(xs), 1n))

def inits(xs: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      init(x) <> inits(t)

def tails(xs: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      List.tail(&2, B.Base, x) <> tails(t)

# v without the first base of every allele (one position later).
def drop_first(v: B.Var) -> B.Var:
  match v:
    case B.Var{pos, ref, alts}:
      B.Var{1n+pos, List.tail(&2, B.Base, ref), tails(alts)}

# v without the last base of every allele.
def drop_last(v: B.Var) -> B.Var:
  match v:
    case B.Var{pos, ref, alts}:
      B.Var{pos, init(ref), inits(alts)}

def all_long.go(xs: List<&2, List<&2, B.Base>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(2n, len(x)) && all_long.go(t)

# Every allele has at least two bases.
def all_long(v: B.Var) -> Bool:
  match v:
    case B.Var{pos, ref, alts}:
      Nat.is_le(2n, len(ref)) && all_long.go(alts)

# Parsimonious: "represented in as few nucleotides as possible" (Tan et al.):
# no base can be dropped from the start, or from the end, of every allele
# (leaving every allele non-empty, as VCF requires) while still making the
# same change.
def parsimonious(+seq: List<&2, B.Base>, +v: B.Var) -> Bool:
  Bool.not(all_long(v) && (same(seq, drop_first(v), v) || same(seq, drop_last(v), v)))

# Normalized: "if and only if it is left aligned and parsimonious" (Tan et
# al.). When some allele would otherwise be empty, every allele keeps one
# unchanged neighbouring base: the one before the event or, when there is no
# base before it (the event starts at the first base of the contig), the one
# after it. Otherwise no neighbouring base is added.
def normalized(+seq: List<&2, B.Base>, +v: B.Var) -> Bool:
  left_aligned(seq, v) && parsimonious(seq, v)

def total(xs: List<&2, List<&2, B.Base>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(len(x), total(t))

# The number of letters in a variant's alleles.
def size(v: B.Var) -> Nat:
  match v:
    case B.Var{pos, ref, alts}:
      Nat.add(len(ref), total(alts))

# ==========================================================================
# Laws: the normal form of one variant (seq is the contig it is on)
# ==========================================================================

# Same change: the output makes exactly the change the input made, with the
# same alternatives in the same order.
law same_change:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  {haps(seq, Tan.normal(seq, v)) == haps(seq, v) : List<&2, List<&2, B.Base>>}

# The output is itself valid: its REF is the contig's bases at its position.
law stays_valid:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  {valid(seq, Tan.normal(seq, v)) == True{} : Bool}

# Standard form: the output is left-aligned and parsimonious.
law standard_form:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  {normalized(seq, Tan.normal(seq, v)) == True{} : Bool}

# A variant already in standard form is left as it is.
law normal_unchanged:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  for hn: {normalized(seq, v) == True{} : Bool}
  {Tan.normal(seq, v) == v : B.Var}

# Running it twice changes nothing.
law twice:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  {Tan.normal(seq, Tan.normal(seq, v)) == Tan.normal(seq, v) : B.Var}

# One form per change: two variants that make the same change come out as the
# same variant.
law one_form:
  for seq: List<&2, B.Base>
  for v: B.Var
  for w: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  for hw: {valid(seq, w) == True{} : Bool}
  for hs: {haps(seq, v) == haps(seq, w) : List<&2, List<&2, B.Base>>}
  {Tan.normal(seq, v) == Tan.normal(seq, w) : B.Var}

# Shortest: no valid variant making the same change has fewer letters.
law shortest:
  for seq: List<&2, B.Base>
  for v: B.Var
  for w: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  for hw: {valid(seq, w) == True{} : Bool}
  for hs: {haps(seq, v) == haps(seq, w) : List<&2, List<&2, B.Base>>}
  {Nat.is_le(size(Tan.normal(seq, v)), size(w)) == True{} : Bool}

# Unique: two valid, normalized variants that make the same change are the
# same variant. (With same_change, stays_valid and standard_form this fixes
# Tan.normal's result without reading its algorithm.)
law unique:
  for seq: List<&2, B.Base>
  for v: B.Var
  for w: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  for hw: {valid(seq, w) == True{} : Bool}
  for hnv: {normalized(seq, v) == True{} : Bool}
  for hnw: {normalized(seq, w) == True{} : Bool}
  for hs: {haps(seq, v) == haps(seq, w) : List<&2, List<&2, B.Base>>}
  {v == w : B.Var}

# ==========================================================================
# Definitions: one body line
# ==========================================================================

def res(o: B.Outcome, +fs: List<&2, String>, body: String) -> B.Res:
  B.Res{o, B.Rec.pos(fs), body, False{}}

def problem(c: Maybe<&2, B.Code>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var) -> B.Res:
  match c:
    case Some{k}:
      res(B.Problem{k}, fs, body)
    case None{}:
      +w = Tan.normal(seq, v)
      B.Res{B.Normalized{}, pos_of(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)}

def first(b: Bool, c: B.Code, rest: Maybe<&2, B.Code>) -> Maybe<&2, B.Code>:
  Bool.pick(Maybe<&2, B.Code>, b, Some{c}, rest)

# The problems a record with a known contig can have, in this order: BAD_END,
# then NON_ACGTN (handled before v exists), BAD_POS, ALT_DUP, REF_MISMATCH.
def checks(end_ok: Bool, +seq: List<&2, B.Base>, v: B.Var) -> Maybe<&2, B.Code>:
  match v:
    case B.Var{+pos, +ref, +alts}:
      first(Bool.not(end_ok), B.BadEnd{},
      first(Nat.is_eq(pos, 0n), B.BadPos{},
      first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{},
      first(Bool.not(B.Bases.eq(slice(seq, Nat.sub(pos, 1n), len(ref)), ref)), B.RefMismatch{},
      None{}))))

def judge.bases(end_ok: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>) -> B.Res:
  match r a:
    case Some{ref} Some{alts}:
      +v = {B.Var{B.Rec.pos(fs), ref, alts} : B.Var}
      problem(checks(end_ok, seq, v), fs, body, seq, v)
    case _ _:
      res(B.Problem{Bool.pick(B.Code, end_ok, B.NonAcgtn{}, B.BadEnd{})}, fs, body)

def judge.contig(m: Maybe<&2, String>, +fs: List<&2, String>, +body: String) -> B.Res:
  match m:
    case None{}:
      res(B.NoContig{}, fs, body)
    case Some{raw}:
      +seq = B.Bases.of_fasta(raw)
      +ref = B.Rec.field(fs, 3n)
      e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      judge.bases(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, body, seq)

def judge.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String) -> B.Res:
  match bad skip:
    case True{} _:
      res(B.Broken{}, fs, body)
    case False{} True{}:
      res(B.Skipped{}, fs, body)
    case False{} False{}:
      judge.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body)

# What happens to one body line (its text without the terminator), given the
# reference. Each line gets the first outcome that applies:
#   1. MALFORMED (B.Rec.malformed);
#   2. out of scope (B.Rec.out_of_scope), whatever its CHROM;
#   3. UNKNOWN_CHROM: CHROM is not a contig of the reference;
#   4. BAD_END: INFO's END is not exactly one "END=<digits>" equal to
#      POS + len(REF) - 1 (B.Info.end_ok);
#   5. NON_ACGTN: REF or an ALT has a letter other than A, C, G, T, N;
#   6. BAD_POS: POS is 0;
#   7. ALT_DUP: two of REF and the ALTs are equal (ignoring case);
#   8. REF_MISMATCH: REF is not the reference's bases at POS (ignoring case),
#      including a REF running past the contig's end;
#   9. normalized: the record is rewritten for Tan.normal's variant
#      (B.Rec.rebuild), sorted by its new POS.
# Every other outcome keeps the text and is sorted by the input POS.
def judge(+fa: List<&2, B.Contig>, +body: String) -> B.Res:
  +fs = B.Rec.fields(body)
  judge.shape(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, fs, body)

def line_valid.vars(r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +seq: List<&2, B.Base>, +pos: Nat) -> Bool:
  match r a:
    case Some{ref} Some{alts}:
      valid(seq, B.Var{pos, ref, alts})
    case _ _:
      False{}

def line_valid.contig(m: Maybe<&2, String>, +fs: List<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{raw}:
      line_valid.vars(B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), B.Bases.of_fasta(raw), B.Rec.pos(fs))

# The variant a record describes (POS, REF, ALTs read as bases) is valid on
# the contig its CHROM names.
def line_valid(+fa: List<&2, B.Contig>, body: String) -> Bool:
  +fs = B.Rec.fields(body)
  line_valid.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs)

def is_normalized(r: B.Res) -> Bool:
  match r:
    case B.Res{B.Normalized{}, k, t, s}:
      True{}
    case _:
      False{}

# A record the tool normalizes describes a valid variant on its contig, so the
# laws about the normal form (same_change ... unique) apply to it.
law normalized_valid:
  for fa: List<&2, B.Contig>
  for body: String
  for h: {is_normalized(judge(fa, body)) == True{} : Bool}
  {line_valid(fa, body) == True{} : Bool}

# ==========================================================================
# Definitions: the whole run
# ==========================================================================

def line_in(phase: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  match phase:
    case False{}:
      R.head_line(R.is_chrom_line(B.Line.body(l)), st, o, l)
    case True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{R.RunSt.n(st), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      R.body_line(judge(fa, B.Line.body(l)), st, o, l, at, B.Rec.pos(fs))

def line_step.go(halted: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  match halted:
    case True{}:
      st
    case False{}:
      line_in(R.RunSt.inbody(st), fa, o, R.tick(st), l)

# One more line of the file (nothing happens once the run has stopped).
def line_step(+fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  line_step.go(R.RunSt.halt(st), fa, o, st, l)

def run.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  match ls:
    case Nil{}:
      st
    case +l <> t:
      run.go(t, fa, o, line_step(fa, o, st, l))

# The whole run, defined over the whole files. Line by line:
#   - Header lines (up to the #CHROM line) are held, then written when the
#     #CHROM line is read, with the two added lines just before it.
#   - Each body line is judged (judge). If its outcome stops the run, the run
#     stops without writing anything more. Else, if its CHROM differs from the
#     current CHROM run, the whole buffer is written, and the run stops with
#     UNSORTED if this CHROM's run already ended. Then the line goes into the
#     buffer, sorted by key (equal keys in input order), and every buffered
#     item with key + w <= this line's input POS is written. Writing an item
#     whose key is below the last key written in this CHROM run stops the run
#     with UNSORTED.
#   - At the end of the file, the buffer is written.
def run(fasta: String, vcf: String, o: B.Opts) -> R.Report:
  R.finish(run.go(B.Text.lines(vcf), B.Fasta.parse(fasta), o, R.start_st()))

# ==========================================================================
# Laws: what a run guarantees
# ==========================================================================

def item_of(r: B.Res, +l: B.Line, at: B.At, +inpos: Nat) -> R.Item:
  match r l:
    case B.Res{B.Normalized{}, k, t, s} B.Line{b, term}:
      R.Item{k, inpos, at, t ++ term}
    case B.Res{_, k, t, s} _:
      R.Item{inpos, inpos, at, B.Line.text(l)}

# The item a body line becomes (for a line that does not stop the run).
def item(+fa: List<&2, B.Contig>, +l: B.Line, +n: Nat) -> R.Item:
  +fs = B.Rec.fields(B.Line.body(l))
  item_of(judge(fa, B.Line.body(l)), l, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

type ItSt is Data:
  ItSt{inbody: Bool, n: Nat, acc: List<&2, R.Item>}

def ItSt.acc(s: ItSt) -> List<&2, R.Item>:
  match s:
    case ItSt{i, n, acc}:
      acc

def items.step(+fa: List<&2, B.Contig>, s: ItSt, +l: B.Line) -> ItSt:
  match s:
    case ItSt{i, +n, acc}:
      match i:
        case False{}:
          ItSt{R.is_chrom_line(B.Line.body(l)), 1n+n, acc}
        case True{}:
          ItSt{True{}, 1n+n, List.append(&2, R.Item, acc, [item(fa, l, 1n+n)])}

def items.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, s: ItSt) -> ItSt:
  match ls:
    case Nil{}:
      s
    case +l <> t:
      items.go(t, fa, items.step(fa, s, l))

# The body lines as items, in input order.
def items(fasta: String, vcf: String) -> List<&2, R.Item>:
  ItSt.acc(items.go(B.Text.lines(vcf), B.Fasta.parse(fasta), ItSt{False{}, 0n, Nil{}}))

def head.step(done: Bool, +acc: String, +o: B.Opts, +l: B.Line) -> String:
  match done:
    case True{}:
      acc
    case False{}:
      Bool.pick(String, R.is_chrom_line(B.Line.body(l)), acc ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l), acc ++ B.Line.text(l))

def head.go(ls: List<&2, B.Line>, +o: B.Opts, +done: Bool, acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case +l <> t:
      head.go(t, o, done || R.is_chrom_line(B.Line.body(l)), head.step(done, acc, o, l))

# The header as written: the header lines with the two added lines before the
# #CHROM line.
def head(vcf: String, +o: B.Opts) -> String:
  head.go(B.Text.lines(vcf), o, False{}, "")

def ins_first.put(le: Bool, +x: R.Item, +y: R.Item, +t: List<&2, R.Item>, rest: List<&2, R.Item>) -> List<&2, R.Item>:
  match le:
    case True{}:
      x <> y <> t
    case False{}:
      y <> rest

def ins_first(+x: R.Item, ys: List<&2, R.Item>) -> List<&2, R.Item>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +t:
      ins_first.put(Nat.is_le(R.Item.key(x), R.Item.key(y)), x, y, t, ins_first(x, t))

# Sorted by key; items with equal keys keep their order.
def isort(xs: List<&2, R.Item>) -> List<&2, R.Item>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      ins_first(x, isort(t))

def same_chrom(run: List<&2, R.Item>, +c: String) -> Bool:
  match run:
    case Nil{}:
      True{}
    case x <> t:
      String.eq(R.Item.chrom(x), c)

def gsort.go(xs: List<&2, R.Item>, +run: List<&2, R.Item>, +done: List<&2, R.Item>) -> List<&2, R.Item>:
  match xs:
    case Nil{}:
      List.append(&2, R.Item, done, isort(run))
    case +x <> t:
      +same = same_chrom(run, R.Item.chrom(x))
      gsort.go(t,
        Bool.pick(List<&2, R.Item>, same, List.append(&2, R.Item, run, [x]), [x]),
        Bool.pick(List<&2, R.Item>, same, done, List.append(&2, R.Item, done, isort(run))))

# Each run of consecutive items with the same CHROM sorted by key, runs kept
# in input order.
def gsort(xs: List<&2, R.Item>) -> List<&2, R.Item>:
  gsort.go(xs, Nil{}, Nil{})

def texts(xs: List<&2, R.Item>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      R.Item.text(x) ++ texts(t)

def grouped.go(xs: List<&2, R.Item>, +cur: String, +ended: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      +c = R.Item.chrom(x)
      (String.eq(c, cur) || Bool.not(R.has(c, cur <> ended)))
        && grouped.go(t, c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended))

# Each CHROM forms one run: once the items move on from a CHROM, it does not
# come back.
def grouped(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      grouped.go(t, R.Item.chrom(x), Nil{})

# Sorted output: a run that succeeds writes the header with the two added
# lines, then the body lines grouped by CHROM (in input order) and, within each
# CHROM, sorted by position, lines with equal positions in input order.
law sorted:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
  {R.Report.out(run(fasta, vcf, o)) == head(vcf, o) ++ texts(gsort(items(fasta, vcf))) : String}

# A run that succeeds had each CHROM in one run (so the output is grouped too).
law grouped_in:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
  {grouped(items(fasta, vcf)) == True{} : Bool}

def ascending.go(xs: List<&2, R.Item>, +a: R.Item) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +b <> t:
      (Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))) || Nat.is_le(R.Item.inpos(a), R.Item.inpos(b)))
        && ascending.go(t, b)

# Within each CHROM, input positions never go down.
def ascending(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +a <> t:
      ascending.go(t, a)

# Every item moved left by less than w bases (moving right is fine).
def small_moves(+w: Nat, xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Nat.is_lt(R.Item.inpos(x), Nat.add(R.Item.key(x), w)) && small_moves(w, t)

def is_unsorted(n: B.Note) -> Bool:
  match n:
    case B.Stop{B.Unsorted{}, a, c}:
      True{}
    case _:
      False{}

def any_unsorted(ns: List<&2, B.Note>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> t:
      is_unsorted(n) || any_unsorted(t)

# Sorted in, no UNSORTED: if the input is grouped by CHROM and sorted by
# position, and no line moves left by w bases or more, the run never stops
# with UNSORTED.
law no_unsorted:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for hw: {Nat.is_le(1n, R.Opts.w(o)) == True{} : Bool}
  for hg: {grouped(items(fasta, vcf)) == True{} : Bool}
  for ha: {ascending(items(fasta, vcf)) == True{} : Bool}
  for hm: {small_moves(R.Opts.w(o), items(fasta, vcf)) == True{} : Bool}
  {any_unsorted(R.Report.notes(run(fasta, vcf, o))) == False{} : Bool}

def body.go(ls: List<&2, B.Line>, +inbody: Bool, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case +l <> t:
      body.go(t, inbody || R.is_chrom_line(B.Line.body(l)), Bool.pick(String, inbody, acc ++ B.Line.text(l), acc))

# The lines after the #CHROM line.
def body(vcf: String) -> String:
  body.go(B.Text.lines(vcf), False{}, "")

# Running the tool on its own output succeeds and gives the same body lines
# (the header gains another pair of added lines).
law twice_run:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
  {(Nat.is_eq(R.Report.code(run(fasta, R.Report.out(run(fasta, vcf, o)), o)), 0n)
    && String.eq(body(R.Report.out(run(fasta, R.Report.out(run(fasta, vcf, o)), o))), body(R.Report.out(run(fasta, vcf, o))))) == True{} : Bool}
