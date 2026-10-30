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
#   whole_without_m ... split_format_values       splitting a record per ALT (-m)
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

def piece_in(halted: Bool, +p: String, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) -> R.RunSt:
  match halted:
    case True{}:
      st
    case False{}:
      R.body_line(judge(fa, p), st, o, B.Line{p, term}, at, inpos)

# The records a split line gives, one after the other, each as a body line of
# its own (judge), with the line's terminator, its place for messages and its
# input POS; nothing happens once the run has stopped.
def pieces_in(ps: List<&2, String>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) -> R.RunSt:
  match ps:
    case Nil{}:
      st
    case +p <> t:
      pieces_in(t, fa, o, piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos), term, at, inpos)

# The outcome r stops the run: MALFORMED, UNKNOWN_CHROM, or a problem under
# -c e (strict).
def stops(r: B.Res, strict: Bool) -> Bool:
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      True{}
    case B.Res{B.NoContig{}, k, t, s}:
      True{}
    case B.Res{B.Problem{c}, k, t, s}:
      strict
    case _:
      False{}

# A line -m cannot split (code c): if judge's outcome for the whole line
# stops the run, that outcome comes first (as without -m); else c is a
# problem: it stops the run under -c e, and under -c w the line is passed
# through as it came, unsplit, with a warning.
def unsplit_in(+r: B.Res, +c: B.Code, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
  Bool.pick(R.RunSt, stops(r, R.Opts.strict(o)), R.body_line(r, st, o, l, at, inpos),
    R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))

# A body line, by what -m does with it (B.Rec.parts): Whole, judged as one
# record (as without -m); Pieces, each record in ALT order; Unsplit, as
# unsplit_in says.
def body_in(pt: B.Parts, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
  match pt:
    case B.Whole{}:
      R.body_line(judge(fa, B.Line.body(l)), st, o, l, at, inpos)
    case B.Pieces{ps}:
      pieces_in(ps, fa, o, st, B.Line.term(l), at, inpos)
    case B.Unsplit{c}:
      unsplit_in(judge(fa, B.Line.body(l)), c, o, st, l, at, inpos)

def line_in(phase: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  match phase:
    case False{}:
      R.head_line(R.is_chrom_line(B.Line.body(l)), st, o, l)
    case True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{R.RunSt.n(st), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      body_in(B.Rec.parts(defs, o, B.Line.body(l)), fa, o, st, l, at, B.Rec.pos(fs))

def line_step.go(halted: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  match halted:
    case True{}:
      st
    case False{}:
      line_in(R.RunSt.inbody(st), fa, defs, o, R.tick(st), l)

# One more line of the file (nothing happens once the run has stopped).
def line_step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  line_step.go(R.RunSt.halt(st), fa, defs, o, st, l)

def run.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  match ls:
    case Nil{}:
      st
    case +l <> t:
      run.go(t, fa, defs, o, line_step(fa, defs, o, st, l))

def defs.go(ls: List<&2, B.Line>, +done: Bool, +d: B.Defs) -> B.Defs:
  match ls:
    case Nil{}:
      d
    case +l <> t:
      defs.go(t, done || R.is_chrom_line(B.Line.body(l)), Bool.pick(B.Defs, done, d, B.Defs.line(d, B.Line.body(l))))

# The header's INFO and FORMAT definitions (B.Defs.line): those of the lines
# before the #CHROM line.
def defs(vcf: String) -> B.Defs:
  defs.go(B.Text.lines(vcf), False{}, B.Defs{Nil{}, Nil{}})

# The whole run, defined over the whole files. Line by line:
#   - Header lines (up to the #CHROM line) are held, then written when the
#     #CHROM line is read, with the two added lines just before it.
#   - With -m, a body line with two or more ALTs is first split into one
#     record per ALT (B.Rec.parts, reading the header's definitions); each
#     record then goes through the rest of this rule in ALT order, as a line of
#     its own with the line's number and input POS. A line that cannot be
#     split (ALT_DUP, UNDEFINED_TAG, BAD_COUNT, BAD_GT) is a problem, after
#     any outcome of the whole line that stops the run (unsplit_in).
#   - Each body line is judged (judge). If its outcome stops the run, the run
#     stops without writing anything more. Else, if its CHROM differs from the
#     current CHROM run, the whole buffer is written, and the run stops with
#     UNSORTED if this CHROM's run already ended. Then the line goes into the
#     buffer, sorted by key (equal keys in input order), and every buffered
#     item with key + w <= this line's input POS is written. Writing an item
#     whose key is below the last key written in this CHROM run stops the run
#     with UNSORTED.
#   - At the end of the file, the buffer is written.
def run(fasta: String, +vcf: String, o: B.Opts) -> R.Report:
  R.finish(run.go(B.Text.lines(vcf), B.Fasta.parse(fasta), defs(vcf), o, R.start_st()))

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

def items.pieces(ps: List<&2, String>, +fa: List<&2, B.Contig>, +term: String, +n: Nat) -> List<&2, R.Item>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      item(fa, B.Line{p, term}, n) <> items.pieces(t, fa, term, n)

# The items a body line becomes: one (Whole), one per ALT in ALT order
# (Pieces), or the line as it came (Unsplit, in a run that goes on: -c w).
def items.line(pt: B.Parts, +fa: List<&2, B.Contig>, +l: B.Line, +n: Nat) -> List<&2, R.Item>:
  match pt:
    case B.Whole{}:
      [item(fa, l, n)]
    case B.Pieces{ps}:
      items.pieces(ps, fa, B.Line.term(l), n)
    case B.Unsplit{c}:
      +fs = B.Rec.fields(B.Line.body(l))
      [R.Item{B.Rec.pos(fs), B.Rec.pos(fs), B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Line.text(l)}]

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

def out_items.step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, s: ItSt, +l: B.Line) -> ItSt:
  match s:
    case ItSt{i, +n, acc}:
      match i:
        case False{}:
          ItSt{R.is_chrom_line(B.Line.body(l)), 1n+n, acc}
        case True{}:
          ItSt{True{}, 1n+n, List.append(&2, R.Item, acc, items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n))}

def out_items.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, s: ItSt) -> ItSt:
  match ls:
    case Nil{}:
      s
    case +l <> t:
      out_items.go(t, fa, defs, o, out_items.step(fa, defs, o, s, l))

# The records a run writes as items, in input order: one per body line, or,
# with -m, one per ALT of a split line, in ALT order. Without -m these are
# items(fasta, vcf) (law items_without_m).
def out_items(fasta: String, +vcf: String, o: B.Opts) -> List<&2, R.Item>:
  ItSt.acc(out_items.go(B.Text.lines(vcf), B.Fasta.parse(fasta), defs(vcf), o, ItSt{False{}, 0n, Nil{}}))

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
# lines, then the records (the body lines, or with -m the records of split
# lines) grouped by CHROM (in input order) and, within each CHROM, sorted by
# position, records with equal positions in input order.
law sorted:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
  {R.Report.out(run(fasta, vcf, o)) == head(vcf, o) ++ texts(gsort(out_items(fasta, vcf, o))) : String}

# A run that succeeds had each CHROM in one run (so the output is grouped too).
law grouped_in:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
  {grouped(out_items(fasta, vcf, o)) == True{} : Bool}

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
  for hg: {grouped(out_items(fasta, vcf, o)) == True{} : Bool}
  for ha: {ascending(out_items(fasta, vcf, o)) == True{} : Bool}
  for hm: {small_moves(R.Opts.w(o), out_items(fasta, vcf, o)) == True{} : Bool}
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

# ==========================================================================
# Definitions: splitting multiallelic records (-m)
# ==========================================================================

def alt_fields(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      B.Rec.field(B.Rec.fields(p), 4n) <> alt_fields(t)

def same_fields(+fs: List<&2, String>, +gs: List<&2, String>, ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +k <> t:
      String.eq(B.Rec.field(fs, k), B.Rec.field(gs, k)) && same_fields(fs, gs, t)

# p has as many fields as fs and the same CHROM, POS, ID, REF, QUAL, FILTER
# and FORMAT, byte for byte.
def same_site(+fs: List<&2, String>, p: String) -> Bool:
  +gs = B.Rec.fields(p)
  Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)) && same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n])

def all_same_site(+fs: List<&2, String>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      same_site(fs, p) && all_same_site(fs, t)

# The number of ALTs of a record.
def n_alts(body: String) -> Nat:
  List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))

# A record's INFO entries (separated by ';'), in order.
def info_entries(body: String) -> List<&2, String>:
  String.split(B.Rec.field(B.Rec.fields(body), 7n), ';')

def info_keys.go(es: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      B.Info.key(e) <> info_keys.go(t)

# The keys of a record's INFO entries, in order.
def info_keys(body: String) -> List<&2, String>:
  info_keys.go(info_entries(body))

# The entry has a value: it has '=' ("key=values"; not a flag, not empty).
def has_value(+e: String) -> Bool:
  Nat.is_lt(String.length(B.Info.key(e)), String.length(e))

# An entry's text after its first '='.
def value_text(+e: String) -> String:
  String.drop(e, Nat.add(String.length(B.Info.key(e)), 1n))

# The values written in a value, separated by commas.
def values(v: String) -> List<&2, String>:
  String.split(v, ',')

def entry_values(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      Some{values(value_text(e))}

def values_of(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{values(x)}

# The FORMAT keys of a record, in order.
def format_keys(body: String) -> List<&2, String>:
  String.split(B.Rec.field(B.Rec.fields(body), 8n), ':')

def column_values(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{String.split(c, ':')}

# Sample s's column (0: the first sample), as its values; None when the line
# has no such column.
def sample_column(body: String, +s: Nat) -> Maybe<&2, List<&2, String>>:
  column_values(List.get(&2, String, B.Rec.fields(body), Nat.add(9n, s)))

def sample_at.of(m: Maybe<&2, List<&2, String>>, +j: Nat) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      List.get(&2, String, vs, j)

# Sample s's value for FORMAT's j-th key (0: the first); None when the line
# has no such column, or the column is shorter.
def sample_at(body: String, +s: Nat, +j: Nat) -> Maybe<&2, String>:
  sample_at.of(sample_column(body, s), j)

def len_of(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      Some{List.length(&2, String, vs)}

def copies_of(m: Maybe<&2, List<&2, String>>, +ks: List<&2, String>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{2n}
    case Some{vs}:
      B.Gt.copies(B.Fmt.gt(ks, vs))

# How many copies sample s's GT says (B.Gt.copies: two without a GT value;
# None, one or two by the count, for a lone '.').
def sample_copies(+body: String, +s: Nat) -> Maybe<&2, Nat>:
  copies_of(sample_column(body, s), format_keys(body))

def gt_cut(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      List.append(&2, String, String.split(x, '|'), gt_cut(t))

# The alleles of a genotype as written, in order (separated by '/' or '|').
def gt_tokens(g: String) -> List<&2, String>:
  gt_cut(String.split(g, '/'))

def gt_read(+t: String) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, String.eq(t, "."), None{}, B.Pos.read(t))

def gt_alleles.go(ts: List<&2, String>) -> List<&2, Maybe<&2, Nat>>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      gt_read(t) <> gt_alleles.go(r)

# The alleles a genotype names, in order: a number (0 REF, 1, 2, ... the
# ALTs), or None for '.' (missing).
def gt_alleles(g: String) -> List<&2, Maybe<&2, Nat>>:
  gt_alleles.go(gt_tokens(g))

def gt_well.go(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> r:
      (String.eq(t, ".") || B.Gt.canon(t)) && gt_well.go(r)

# A genotype is written as VCF writes it: alleles separated by '/' or '|',
# each '.' or a number without leading zeros.
def gt_well(g: String) -> Bool:
  gt_well.go(gt_tokens(g))

def gt_view.if(ok: Bool, g: String) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
  match ok:
    case True{}:
      Some{gt_alleles(g)}
    case False{}:
      None{}

# A genotype value's alleles, if it is there and well written.
def gt_view(m: Maybe<&2, String>) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
  match m:
    case None{}:
      None{}
    case Some{+g}:
      gt_view.if(gt_well(g), g)

def gt_seps.put(sep: Bool, h: Char, rest: String) -> String:
  match sep:
    case True{}:
      SCon{h, rest}
    case False{}:
      rest

# The separators of a genotype, in order ('/' unphased, '|' phased).
def gt_seps(g: String) -> String:
  match g:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      gt_seps.put(B.Gt.is_sep(h), h, gt_seps(t))

def seps_of(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{gt_seps(g)}

def gt_rule_all(+over0: Bool, +i: Nat, xs: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> t:
      B.Gt.rule(over0, i, a) <> gt_rule_all(over0, i, t)

# The value values vs give allele j (0 REF, 1 to n the ALTs): Number R, and G
# of one copy, value j; Number A (no value for REF), value j - 1.
def allele_value(num: B.Num, +vs: List<&2, String>, +j: Nat) -> Maybe<&2, String>:
  match num:
    case B.NumA{}:
      Bool.pick(Maybe<&2, String>, Nat.is_eq(j, 0n), None{}, List.get(&2, String, vs, Nat.sub(j, 1n)))
    case _:
      List.get(&2, String, vs, j)

# The value Number G values vs give genotype j/k (j <= k) of two copies (VCF
# 4.3, section 1.6.2: value k(k+1)/2 + j).
def genotype_value(+vs: List<&2, String>, +j: Nat, +k: Nat) -> Maybe<&2, String>:
  List.get(&2, String, vs, Nat.add(Nat.div(Nat.mul(k, 1n+k), 2n), j))

def somes(ms: List<&2, Maybe<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match ms:
    case Nil{}:
      Some{Nil{}}
    case m <> t:
      B.Vals.pick.cons(m, somes(t))

# The values the record for ALT i gives a per-allele tag, from the input's
# values vs, ALT i becoming the record's one ALT (allele 1), for ploidy p:
#   A: the value of ALT i;
#   R: the values of REF and of ALT i;
#   G, one copy (p = 1): the values of REF and of ALT i;
#   G, two copies: the values of genotypes REF/REF, REF/ALT i, ALT i/ALT i
#     (0/0, 0/i, i/i), which become the record's 0/0, 0/1, 1/1.
def lifted(num: B.Num, +p: Nat, +i: Nat, +vs: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match num:
    case B.NumA{}:
      somes([allele_value(B.NumA{}, vs, i)])
    case B.NumR{}:
      somes([allele_value(B.NumR{}, vs, 0n), allele_value(B.NumR{}, vs, i)])
    case B.NumG{}:
      Bool.pick(Maybe<&2, List<&2, String>>, Nat.is_eq(p, 1n),
        somes([allele_value(B.NumG{}, vs, 0n), allele_value(B.NumG{}, vs, i)]),
        somes([genotype_value(vs, 0n, 0n), genotype_value(vs, 0n, i), genotype_value(vs, i, i)]))
    case _:
      Some{vs}

def first_code.put(m: Maybe<&2, B.Code>, rest: Maybe<&2, B.Code>) -> Maybe<&2, B.Code>:
  match m:
    case Some{c}:
      Some{c}
    case None{}:
      rest

def first_code(ms: List<&2, Maybe<&2, B.Code>>) -> Maybe<&2, B.Code>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      first_code.put(m, first_code(t))

# A per-allele value v is '.' or has the expected number of values for its
# copies cp: expected_count(num, n, p), p the copies the sample's GT says,
# and for a lone '.' GT either n + 1 (one copy) or (n+1)(n+2)/2 (two).
def count_problem(num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +v: String) -> Maybe<&2, B.Code>:
  +c = List.length(&2, String, values(v))
  Bool.pick(Maybe<&2, B.Code>, String.eq(v, ".") || B.Vals.fits(B.Vals.expected_count(num, n, B.Vals.copies(cp, n, c)), c), None{}, Some{B.BadCount{}})

def info_problem.of(m: Maybe<&2, B.Num>, +e: String, +n: Nat) -> Maybe<&2, B.Code>:
  match m:
    case None{}:
      Some{B.UndefinedTag{"INFO/" ++ B.Info.key(e)}}
    case Some{B.NumUnknown{}}:
      Some{B.UndefinedTag{"INFO/" ++ B.Info.key(e)}}
    case Some{B.NumOther{}}:
      None{}
    case Some{num}:
      count_problem(num, n, Some{2n}, value_text(e))

# What is wrong with an INFO entry, for a record with n ALTs: an entry
# without a value (a flag, an empty entry) is fine unless its tag is A, R or
# G (BAD_COUNT); an entry with a value whose tag the header does not define,
# or defines with an Unknown Number, is UNDEFINED_TAG; an A, R or G value that
# is not '.' and has not expected_count(Number, n, 2) values is BAD_COUNT.
def info_problem(+m: Maybe<&2, B.Num>, +e: String, +n: Nat) -> Maybe<&2, B.Code>:
  Bool.pick(Maybe<&2, B.Code>, has_value(e), info_problem.of(m, e, n),
    Bool.pick(Maybe<&2, B.Code>, B.Num.per_allele(m), Some{B.BadCount{}}, None{}))

def info_problems(es: List<&2, String>, +tags: List<&2, B.Tag>, +n: Nat) -> List<&2, Maybe<&2, B.Code>>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      info_problem(B.Tags.find(tags, B.Info.key(e)), e, n) <> info_problems(t, tags, n)

def gt_ok.go(ts: List<&2, String>, +n: Nat) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> r:
      (String.eq(t, ".") || (B.Gt.canon(t) && Nat.is_le(Maybe.default(&2, Nat, B.Pos.read(t), 0n), n))) && gt_ok.go(r, n)

# What is wrong with a genotype of a record with n ALTs: an allele that is
# not '.' or a number from 0 to n without leading zeros is BAD_GT.
def gt_problem(+n: Nat, g: String) -> Maybe<&2, B.Code>:
  Bool.pick(Maybe<&2, B.Code>, gt_ok.go(gt_tokens(g), n), None{}, Some{B.BadGt{}})

def format_problem(m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>) -> Maybe<&2, B.Code>:
  match m:
    case None{}:
      Some{B.UndefinedTag{"FORMAT/" ++ k}}
    case Some{B.NumUnknown{}}:
      Some{B.UndefinedTag{"FORMAT/" ++ k}}
    case Some{B.NumOther{}}:
      None{}
    case Some{num}:
      count_problem(num, n, p, v)

# What is wrong with one sample's values, read against the FORMAT keys, for
# ploidy p: GT as gt_problem says; another key the header does not define,
# or defines with an Unknown Number, is UNDEFINED_TAG; an A, R or G value
# that is not '.' and has not expected_count(Number, n, p) values is
# BAD_COUNT; a value with no key is BAD_COUNT.
def sample_problems(ks: List<&2, String>, vs: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat, +p: Maybe<&2, Nat>) -> List<&2, Maybe<&2, B.Code>>:
  match ks vs:
    case _ Nil{}:
      Nil{}
    case Nil{} v <> t:
      [Some{B.BadCount{}}]
    case +k <> kt +v <> vt:
      Bool.pick(Maybe<&2, B.Code>, String.eq(k, "GT"), gt_problem(n, v), format_problem(B.Tags.find(fmt, k), k, v, n, p))
        <> sample_problems(kt, vt, fmt, n, p)

def samples_problems(cols: List<&2, String>, +ks: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat) -> List<&2, Maybe<&2, B.Code>>:
  match cols:
    case Nil{}:
      Nil{}
    case c <> t:
      +vs = String.split(c, ':')
      List.append(&2, Maybe<&2, B.Code>, sample_problems(ks, vs, fmt, n, B.Gt.copies(B.Fmt.gt(ks, vs))), samples_problems(t, ks, fmt, n))

# Why a line cannot be split, the first reason reading it left to right; None
# when it can be:
#   ALT_DUP: two of its ALTs are equal (ignoring case);
#   then its INFO entries, in order (info_problem);
#   then its samples, in order, each value in FORMAT's order (sample_problems,
#   the sample's copies from its GT, B.Gt.copies).
def split_problem(+defs: B.Defs, +body: String) -> Maybe<&2, B.Code>:
  +fs = B.Rec.fields(body)
  +n = n_alts(body)
  first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(fs)), None{}, Some{B.DupAlts{}})
    <> List.append(&2, Maybe<&2, B.Code>, info_problems(info_entries(body), B.Defs.info(defs), n),
         samples_problems(List.drop(&2, String, fs, 9n), format_keys(body), B.Defs.fmt(defs), n)))

# What B.Rec.parts says, as a refusal: Some{None} for Pieces, Some{Some{c}}
# for Unsplit{c}, None for Whole.
def refusal(pt: B.Parts) -> Maybe<&2, Maybe<&2, B.Code>>:
  match pt:
    case B.Whole{}:
      None{}
    case B.Pieces{ps}:
      Some{None{}}
    case B.Unsplit{c}:
      Some{Some{c}}

# The Number is Other (a count, '.', P).
def is_other(m: Maybe<&2, B.Num>) -> Bool:
  match m:
    case Some{B.NumOther{}}:
      True{}
    case _:
      False{}

# The entry is copied whole by -m: it has no value (a flag, an empty entry,
# INFO '.'), its value is '.', or its tag's Number is Other.
def info_copied(+tags: List<&2, B.Tag>, +e: String) -> Bool:
  Bool.not(has_value(e)) || String.eq(value_text(e), ".") || is_other(B.Tags.find(tags, B.Info.key(e)))

# The value is copied by -m: it is '.', or its tag's Number is Other.
def format_copied(+tags: List<&2, B.Tag>, +k: String, +v: String) -> Bool:
  String.eq(v, ".") || is_other(B.Tags.find(tags, k))

def per_allele_num(n: B.Num) -> Bool:
  B.Num.per_allele(Some{n})

def line_change.vars(r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +seq: List<&2, B.Base>, +pos: Nat) -> List<&2, List<&2, B.Base>>:
  match r a:
    case Some{ref} Some{alts}:
      haps(seq, B.Var{pos, ref, alts})
    case _ _:
      Nil{}

def line_change.contig(m: Maybe<&2, String>, +fs: List<&2, String>) -> List<&2, List<&2, B.Base>>:
  match m:
    case None{}:
      Nil{}
    case Some{raw}:
      line_change.vars(B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), B.Bases.of_fasta(raw), B.Rec.pos(fs))

# The change a record makes, read from its text: the contig after each of its
# ALTs (haps), in order; nothing when it cannot be read as a variant.
def line_change(+fa: List<&2, B.Contig>, body: String) -> List<&2, List<&2, B.Base>>:
  +fs = B.Rec.fields(body)
  line_change.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs)

def res_text(r: B.Res) -> String:
  match r:
    case B.Res{o, k, t, s}:
      t

# The text judge gives a record: what the run writes for it when its outcome
# does not stop the run (normalized, or as it came; the item's text in
# out_items, without the terminator).
def written(+fa: List<&2, B.Contig>, p: String) -> String:
  res_text(judge(fa, p))

def one_of(m: Maybe<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

def all_line_valid(+fa: List<&2, B.Contig>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      line_valid(fa, p) && all_line_valid(fa, t)

def all_normalized(+fa: List<&2, B.Contig>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      is_normalized(judge(fa, p)) && all_normalized(fa, t)

def biallelic.go(ls: List<&2, B.Line>, +inbody: Bool) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      (Bool.not(inbody) || Nat.is_lt(n_alts(B.Line.body(l)), 2n)) && biallelic.go(t, inbody || R.is_chrom_line(B.Line.body(l)))

# No body line has two or more ALTs.
def biallelic(vcf: String) -> Bool:
  biallelic.go(B.Text.lines(vcf), False{})

# The options o without -m (everything else, the recorded arguments too,
# kept).
def no_m(o: B.Opts) -> B.Opts:
  match o:
    case B.Opts{s, w, m, z, a}:
      B.Opts{s, w, False{}, z, a}

# ==========================================================================
# Laws: splitting multiallelic records (-m)
# ==========================================================================

# Without -m, every line is one record, handled as before -m existed.
law whole_without_m:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for h: {R.Opts.split(o) == False{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

# Without -m, the records written are the body lines, as before -m existed:
# so sorted, grouped_in and no_unsorted say, without -m, what they said
# before.
law items_without_m:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {R.Opts.split(o) == False{} : Bool}
  {out_items(fasta, vcf, o) == items(fasta, vcf) : List<&2, R.Item>}

# With -m, a record with one ALT is handled as without -m.
law whole_biallelic:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for h: {Nat.is_lt(n_alts(body), 2n) == True{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

# A MALFORMED line is handled as without -m (it stops the run, MALFORMED).
law whole_malformed:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for h: {B.Rec.malformed(B.Rec.fields(body)) == True{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

# On a file whose body lines have one ALT each, -m changes nothing but the
# arguments recorded in the header (no_m keeps them): the same output,
# messages and exit code.
law biallelic_run:
  for fasta: String
  for vcf: String
  for o: B.Opts
  for h: {biallelic(vcf) == True{} : Bool}
  {run(fasta, vcf, o) == run(fasta, vcf, no_m(o)) : R.Report}

# Which lines split: with -m, a line that is not MALFORMED and has two or
# more ALTs is split exactly when split_problem finds nothing wrong with it,
# and refused with exactly the code split_problem gives otherwise.
law split_when:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for hs: {R.Opts.split(o) == True{} : Bool}
  for hm: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool}
  for hn: {Nat.is_le(2n, n_alts(body)) == True{} : Bool}
  {refusal(B.Rec.parts(defs, o, body)) == Some{split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}

# One record per ALT: the records' ALT fields are the input's ALTs, one each,
# in the input's order.
law split_alts:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {alt_fields(ps) == B.Rec.alts(B.Rec.fields(body)) : List<&2, String>}

# Each record keeps the input's CHROM, POS, ID, REF, QUAL, FILTER and FORMAT,
# and its number of fields (so its samples).
law split_site:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {all_same_site(B.Rec.fields(body), ps) == True{} : Bool}

# If the line describes a valid variant on its contig, so does each record
# (the line's POS and REF with one of its ALTs): so the laws of the normal
# form, same_change ... unique, apply to each.
law split_valid:
  for fa: List<&2, B.Contig>
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for hv: {line_valid(fa, body) == True{} : Bool}
  {all_line_valid(fa, ps) == True{} : Bool}

# If the whole line would be normalized (no problem), every record is.
law split_normalized:
  for fa: List<&2, B.Contig>
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for hn: {is_normalized(judge(fa, body)) == True{} : Bool}
  {all_normalized(fa, ps) == True{} : Bool}

# The record for ALT i+1, as written (its outcome does not stop the run:
# normalized, or passed as it came), read back as a variant on the
# reference, makes exactly the change of the line's ALT i+1: the contig after
# that ALT. (The records' order in the output is the sorted one, law sorted;
# this law pairs each record with its ALT.)
law split_change:
  for fa: List<&2, B.Contig>
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for hv: {line_valid(fa, body) == True{} : Bool}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for hs: {stops(judge(fa, p), R.Opts.strict(o)) == False{} : Bool}
  {line_change(fa, written(fa, p)) == one_of(List.get(&2, List<&2, B.Base>, line_change(fa, body), i)) : List<&2, List<&2, B.Base>>}

# Genotypes: in the record for ALT i+1, every GT value of every sample (s,
# j: the sample and the FORMAT key's place) is well written and names, copy
# by copy, B.Gt.rule's allele for the one the input named there: REF stays
# REF; ALT i+1 becomes the record's ALT (1); another ALT becomes REF
# (--multi-overlaps 0) or missing (--multi-overlaps .); missing stays
# missing.
law split_gt:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for s: Nat
  for j: Nat
  for hk: {List.get(&2, String, format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
  for g: String
  for hg: {sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
  {gt_view(sample_at(p, s, j)) == Some{gt_rule_all(R.Opts.over0(o), 1n+i, gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}

# ... and keeps the input's separators, so its phasing and ploidy.
law split_phase:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for s: Nat
  for j: Nat
  for hk: {List.get(&2, String, format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
  for g: String
  for hg: {sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
  {seps_of(sample_at(p, s, j)) == Some{gt_seps(g)} : Maybe<&2, String>}

# INFO: each record has the input's INFO keys, in order (so as many entries).
law split_info_keys:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  {info_keys(p) == info_keys(body) : List<&2, String>}

# Every INFO entry (e: its place) whose tag is A, R or G and whose value is
# not '.' gives, in the record for ALT i+1, exactly the values of that
# record's alleles (lifted; split_when says the input had exactly
# expected_count values).
law split_info_values:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for e: Nat
  for x: String
  for hx: {List.get(&2, String, info_entries(body), e) == Some{x} : Maybe<&2, String>}
  for num: B.Num
  for hk: {B.Tags.find(B.Defs.info(defs), B.Info.key(x)) == Some{num} : Maybe<&2, B.Num>}
  for ha: {per_allele_num(num) == True{} : Bool}
  for hv: {has_value(x) == True{} : Bool}
  for hm: {String.eq(value_text(x), ".") == False{} : Bool}
  {entry_values(List.get(&2, String, info_entries(p), e)) == lifted(num, 2n, 1n+i, values(value_text(x))) : Maybe<&2, List<&2, String>>}

# Every other INFO entry is copied by the split, byte for byte: a flag, an
# empty entry, a value '.', a tag of Number Other. (judge then rewrites END
# for a record normalization moves, by the END rule, as without -m.)
law split_info_kept:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for e: Nat
  for x: String
  for hx: {List.get(&2, String, info_entries(body), e) == Some{x} : Maybe<&2, String>}
  for hc: {info_copied(B.Defs.info(defs), x) == True{} : Bool}
  {List.get(&2, String, info_entries(p), e) == Some{x} : Maybe<&2, String>}

# FORMAT: each sample has as many values as in the input (none when the line
# has no such column).
law split_format_shape:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for s: Nat
  {len_of(sample_column(p, s)) == len_of(sample_column(body, s)) : Maybe<&2, Nat>}

# Every FORMAT value (other than GT) whose tag is A, R or G and that is not
# '.' gives, in the record for ALT i+1, exactly the values of that record's
# alleles (lifted), for the copies its sample's GT names: G of one copy gives
# REF's and ALT i+1's values; G of two copies (or no GT value) the three
# genotype values; a lone '.' GT, one or two copies as its count says.
law split_format_values:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for s: Nat
  for j: Nat
  for k: String
  for hk: {List.get(&2, String, format_keys(body), j) == Some{k} : Maybe<&2, String>}
  for hgt: {String.eq(k, "GT") == False{} : Bool}
  for num: B.Num
  for hn: {B.Tags.find(B.Defs.fmt(defs), k) == Some{num} : Maybe<&2, B.Num>}
  for ha: {per_allele_num(num) == True{} : Bool}
  for v: String
  for hv: {sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
  for hm: {String.eq(v, ".") == False{} : Bool}
  {values_of(sample_at(p, s, j)) == lifted(num, B.Vals.copies(sample_copies(body, s), n_alts(body), List.length(&2, String, values(v))), 1n+i, values(v)) : Maybe<&2, List<&2, String>>}

# Every other FORMAT value (other than GT) is copied byte for byte: a value
# '.', a tag of Number Other.
law split_format_kept:
  for defs: B.Defs
  for o: B.Opts
  for body: String
  for ps: List<&2, String>
  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for i: Nat
  for p: String
  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for s: Nat
  for j: Nat
  for k: String
  for hk: {List.get(&2, String, format_keys(body), j) == Some{k} : Maybe<&2, String>}
  for hgt: {String.eq(k, "GT") == False{} : Bool}
  for v: String
  for hv: {sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
  for hc: {format_copied(B.Defs.fmt(defs), k, v) == True{} : Bool}
  {sample_at(p, s, j) == Some{v} : Maybe<&2, String>}
