import Base

# framebender: the types shared by the laws and the code, and how text is read.
#
# Part of the spec: the owner reviews this file with LAWS.bend. Text is a
# String of bytes (one Char per byte); the driver reads and writes files byte
# for byte.

# ===========================================================================
# Bases and variants
# ===========================================================================

# One DNA base. N means "unknown base"; it is compared as a fifth letter, equal
# only to N (as in Tan et al. and bcftools), not as a wildcard.
type Base is Data:
  A{}
  C{}
  G{}
  T{}
  N{}

# A variant (one VCF record's change): from 1-based position pos, the bases ref
# are replaced by each of the alternatives in alts (a multiallelic record has
# several). The order of alts matters: genotypes refer to alternatives by index.
type Var is Data:
  Var{pos: Nat, ref: List<&2, Base>, alts: List<&2, List<&2, Base>>}

def Var.pos(v: Var) -> Nat:
  match v:
    case Var{p, r, a}:
      p

def Base.is_eq(a: Base, b: Base) -> Bool:
  match a b:
    case A{} A{}:
      True{}
    case C{} C{}:
      True{}
    case G{} G{}:
      True{}
    case T{} T{}:
      True{}
    case N{} N{}:
      True{}
    case _ _:
      False{}

def Bases.eq(xs: List<&2, Base>, ys: List<&2, Base>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Base.is_eq(x, y) && Bases.eq(xt, yt)
    case _ _:
      False{}

# Two lists of alleles are equal: same length, equal one by one.
def Alleles.eq(xs: List<&2, List<&2, Base>>, ys: List<&2, List<&2, Base>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Bases.eq(x, y) && Alleles.eq(xt, yt)
    case _ _:
      False{}

# ===========================================================================
# Letters
# ===========================================================================

def Char.code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

def Base.maybe(b: Bool, x: Base, m: Maybe<&2, Base>) -> Maybe<&2, Base>:
  Bool.pick(Maybe<&2, Base>, b, Some{x}, m)

# A VCF allele letter: A, C, G, T or N, in either case. Any other character
# (an IUPAC code such as R, '*', '<', '.') is not one.
def Base.of_letter(c: Char) -> Maybe<&2, Base>:
  +x = Char.code(Char.to_upper(c))
  Base.maybe(U32.is_eq(x, 65), A{},
  Base.maybe(U32.is_eq(x, 67), C{},
  Base.maybe(U32.is_eq(x, 71), G{},
  Base.maybe(U32.is_eq(x, 84), T{},
  Base.maybe(U32.is_eq(x, 78), N{},
  None{})))))

def Base.when(b: Bool, x: Base, y: Base) -> Base:
  Bool.pick(Base, b, x, y)

# A reference (FASTA) letter, in either case. IUPAC ambiguity codes become the
# alphabetically first base they stand for (VCF 4.3, section 1.6.1, as bcftools
# does): R, M, W, D, H, V read as A; Y, S, B as C; K as G. A, C, G, T, N read as
# themselves; any other character reads as N.
def Base.of_fasta(c: Char) -> Base:
  +x = Char.code(Char.to_upper(c))
  Base.when(U32.is_eq(x, 65) || U32.is_eq(x, 82) || U32.is_eq(x, 77) || U32.is_eq(x, 87) || U32.is_eq(x, 68) || U32.is_eq(x, 72) || U32.is_eq(x, 86), A{},
  Base.when(U32.is_eq(x, 67) || U32.is_eq(x, 89) || U32.is_eq(x, 83) || U32.is_eq(x, 66), C{},
  Base.when(U32.is_eq(x, 71) || U32.is_eq(x, 75), G{},
  Base.when(U32.is_eq(x, 84), T{},
  N{}))))

# The upper-case letter the tool writes for a base.
def Base.letter(b: Base) -> Char:
  match b:
    case A{}:
      'A'
    case C{}:
      'C'
    case G{}:
      'G'
    case T{}:
      'T'
    case N{}:
      'N'

# ===========================================================================
# Alleles and numbers as text
# ===========================================================================

def Text.all_letters(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Char.is_alpha(h) && Text.all_letters(t)

# One or more letters A-Z or a-z, nothing else.
def Text.is_letters(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Text.all_letters(SCon{h, t})

def Allele.read.cons(b: Maybe<&2, Base>, rest: Maybe<&2, List<&2, Base>>) -> Maybe<&2, List<&2, Base>>:
  match b rest:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def Allele.read.go(s: String) -> Maybe<&2, List<&2, Base>>:
  match s:
    case SNil{}:
      Some{Nil{}}
    case SCon{h, t}:
      Allele.read.cons(Base.of_letter(h), Allele.read.go(t))

# An allele made only of the letters A, C, G, T, N (either case), read as
# bases; None if it has any other character.
def Allele.read(s: String) -> Maybe<&2, List<&2, Base>>:
  Allele.read.go(s)

def Allele.show(xs: List<&2, Base>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> t:
      SCon{Base.letter(x), Allele.show(t)}

def Alleles.show(xs: List<&2, List<&2, Base>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      Allele.show(x) <> Alleles.show(t)

def Pos.digit.if(x: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(U32.sub(x, 48))}
    case False{}:
      None{}

def Pos.digit(c: Char) -> Maybe<&2, Nat>:
  match c:
    case Chr{+x}:
      Pos.digit.if(x, U32.is_ge(x, 48) && U32.is_le(x, 57))

def Pos.read.push(acc: Maybe<&2, Nat>, d: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match acc d:
    case Some{a} Some{k}:
      Some{Nat.add(Nat.mul(a, 10n), k)}
    case _ _:
      None{}

def Pos.read.go(s: String, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      Pos.read.go(t, Pos.read.push(acc, Pos.digit(h)))

# A number: one or more decimal digits (leading zeros allowed), nothing else.
# No upper limit: positions above VCF's 32-bit integers are accepted, as
# htslib and bcftools (64-bit positions) do.
def Pos.read(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Pos.read.go(SCon{h, t}, Some{0n})

# ===========================================================================
# Lines
# ===========================================================================

# A line of the VCF file: its text and its terminator, "\n" or "\r\n".
type Line is Data:
  Line{body: String, term: String}

def Text.line.if(cr: Bool, +p: String) -> Line:
  match cr:
    case True{}:
      Line{String.take(p, Nat.sub(String.length(p), 1n)), "\r\n"}
    case False{}:
      Line{p, "\n"}

# A piece of text between two LFs: a CR at its end belongs to the terminator.
def Text.line(+p: String) -> Line:
  Text.line.if(String.ends_with(p, "\r"), p)

def Text.last(p: String) -> List<&2, Line>:
  match p:
    case SNil{}:
      Nil{}
    case SCon{h, t}:
      [Text.line(SCon{h, t})]

def Text.lines.go(ps: List<&2, String>, p: String) -> List<&2, Line>:
  match ps:
    case Nil{}:
      Text.last(p)
    case q <> t:
      Text.line(p) <> Text.lines.go(t, q)

def Text.lines.start(ps: List<&2, String>) -> List<&2, Line>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      Text.lines.go(t, p)

# The lines of a file. A line ends just after each LF. If the file does not end
# with LF, the remaining bytes form the last line and are given a terminator
# (LF, or CR LF when they end with CR); an empty remainder is not a line, so an
# empty file has no lines.
def Text.lines(s: String) -> List<&2, Line>:
  Text.lines.start(String.split(s, '\n'))

def Line.body(l: Line) -> String:
  match l:
    case Line{b, t}:
      b

def Line.term(l: Line) -> String:
  match l:
    case Line{b, t}:
      t

def Line.text(l: Line) -> String:
  match l:
    case Line{b, t}:
      b ++ t

def Lines.text(ls: List<&2, Line>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> t:
      Line.text(l) ++ Lines.text(t)

# ===========================================================================
# Records (VCF data lines)
# ===========================================================================

# The tab-separated fields of a line's text.
def Rec.fields(body: String) -> List<&2, String>:
  String.split(body, '\t')

# Field i (0-based: CHROM 0, POS 1, ID 2, REF 3, ALT 4, QUAL 5, FILTER 6,
# INFO 7), or "" when the line has fewer fields.
def Rec.field(fs: List<&2, String>, i: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, fs, i), "")

# The ALT field's alleles (separated by commas).
def Rec.alts(fs: List<&2, String>) -> List<&2, String>:
  String.split(Rec.field(fs, 4n), ',')

# The key of an INFO entry: the text before its first '='.
def Info.key(piece: String) -> String:
  Rec.field(String.split(piece, '='), 0n)

def Info.has.go(pieces: List<&2, String>, +k: String) -> Bool:
  match pieces:
    case Nil{}:
      False{}
    case p <> t:
      String.eq(Info.key(p), k) || Info.has.go(t, k)

# The INFO field has an entry with key k (as "END" in "DP=10;END=500").
def Info.has(info: String, +k: String) -> Bool:
  Info.has.go(String.split(info, ';'), k)

def Info.ends.put(is_end: Bool, +p: String, rest: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match is_end:
    case True{}:
      Pos.read(String.drop(p, 4n)) <> rest
    case False{}:
      rest

def Info.ends.go(pieces: List<&2, String>) -> List<&2, Maybe<&2, Nat>>:
  match pieces:
    case Nil{}:
      Nil{}
    case +p <> t:
      Info.ends.put(String.eq(Info.key(p), "END"), p, Info.ends.go(t))

# The values of the INFO entries with key END: Some number when the entry is
# "END=<digits>", None when it is anything else ("END", "END=.", "END=1,2").
def Info.ends(info: String) -> List<&2, Maybe<&2, Nat>>:
  Info.ends.go(String.split(info, ';'))

def Info.set_end.put(is_end: Bool, p: String, +e: Nat) -> String:
  match is_end:
    case True{}:
      "END=" ++ Nat.show(e)
    case False{}:
      p

def Info.set_end.go(pieces: List<&2, String>, +e: Nat) -> List<&2, String>:
  match pieces:
    case Nil{}:
      Nil{}
    case +p <> t:
      Info.set_end.put(String.eq(Info.key(p), "END"), p, e) <> Info.set_end.go(t, e)

# The INFO field with the value of its END entry replaced by e (in decimal);
# every other byte kept.
def Info.set_end(info: String, +e: Nat) -> String:
  String.join(Info.set_end.go(String.split(info, ';'), e), ";")

def Alleles.member(+x: List<&2, Base>, xs: List<&2, List<&2, Base>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> t:
      Bases.eq(x, y) || Alleles.member(x, t)

# No allele appears twice.
def Alleles.distinct(xs: List<&2, List<&2, Base>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +t:
      Bool.not(Alleles.member(x, t)) && Alleles.distinct(t)

def Text.any_empty(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      String.is_empty(x) || Text.any_empty(t)

def Text.any_not_letters(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.not(Text.is_letters(x)) || Text.any_not_letters(t)

def Alleles.read.cons(a: Maybe<&2, List<&2, Base>>, rest: Maybe<&2, List<&2, List<&2, Base>>>) -> Maybe<&2, List<&2, List<&2, Base>>>:
  match a rest:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

# The ALT alleles as bases; None if any has a letter other than A, C, G, T, N.
def Alleles.read(xs: List<&2, String>) -> Maybe<&2, List<&2, List<&2, Base>>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case x <> t:
      Alleles.read.cons(Allele.read(x), Alleles.read(t))

# MALFORMED: fewer than 8 fields, an empty CHROM, a POS that is not a number,
# a REF that is not one or more letters, or an empty allele in ALT (including
# an empty ALT field). A blank line is MALFORMED.
def Rec.malformed(+fs: List<&2, String>) -> Bool:
  Nat.is_lt(List.length(&2, String, fs), 8n)
    || String.is_empty(Rec.field(fs, 0n))
    || Maybe.is_none(&2, Nat, Pos.read(Rec.field(fs, 1n)))
    || Bool.not(Text.is_letters(Rec.field(fs, 3n)))
    || Text.any_empty(Rec.alts(fs))

# Out of scope: some ALT allele is not made only of letters (a symbolic allele
# <...> including <*> and <NON_REF>, '*', '.', a breakend).
def Rec.out_of_scope(fs: List<&2, String>) -> Bool:
  Text.any_not_letters(Rec.alts(fs))

# The record's POS as a number (0 if it is not one).
def Rec.pos(fs: List<&2, String>) -> Nat:
  Maybe.default(&2, Nat, Pos.read(Rec.field(fs, 1n)), 0n)

def Info.end_ok.go(ends: List<&2, Maybe<&2, Nat>>, +e: Nat) -> Bool:
  match ends:
    case Nil{}:
      True{}
    case Some{v} <> Nil{}:
      Nat.is_eq(v, e)
    case _:
      False{}

# INFO/END is fine: there is no END entry, or exactly one, "END=<digits>" with
# the value e (the record's last position, POS + len(REF) - 1).
def Info.end_ok(info: String, +e: Nat) -> Bool:
  Info.end_ok.go(Info.ends(info), e)

def Rec.put(fs: List<&2, String>, i: Nat, s: String) -> List<&2, String>:
  match fs i:
    case Nil{} _:
      Nil{}
    case f <> t 0n:
      s <> t
    case f <> t 1n+j:
      f <> Rec.put(t, j, s)

def Rec.moved(v: Var, w: Var) -> Bool:
  match v w:
    case Var{p, r, x} Var{q, s, y}:
      Bool.not(Nat.is_eq(p, q) && Nat.is_eq(List.length(&2, Base, r), List.length(&2, Base, s)))

def Rec.info(moved: Bool, info: String, w: Var) -> String:
  match moved w:
    case True{} Var{+q, s, y}:
      Info.set_end(info, Nat.sub(Nat.add(q, List.length(&2, Base, s)), 1n))
    case False{} _:
      info

# The record's fields rewritten for the normalized variant w of v: POS in
# decimal without leading zeros, REF and ALT in upper case, the END entry of
# INFO set to w's last position when POS or the length of REF changed; every
# other byte kept. Joined back with tabs.
def Rec.rebuild(+fs: List<&2, String>, +v: Var, +w: Var) -> String:
  match w:
    case Var{+q, +s, +y}:
      info = Rec.info(Rec.moved(v, Var{q, s, y}), Rec.field(fs, 7n), Var{q, s, y})
      fs2 = Rec.put(Rec.put(Rec.put(Rec.put(fs, 1n, Nat.show(q)), 3n, Allele.show(s)), 4n, String.join(Alleles.show(y), ",")), 7n, info)
      String.join(fs2, "\t")

def Rec.same_var(v: Var, w: Var) -> Bool:
  match v w:
    case Var{p, r, x} Var{q, s, y}:
      Nat.is_eq(p, q) && Bases.eq(r, s) && Alleles.eq(x, y)

# POSSIBLY_STALE: the representation changed (POS or the allele sequences,
# not just their case or leading zeros) and INFO has one of the reserved keys
# that describe the alleles' sequence or breakpoints: CIGAR, HOMLEN, HOMSEQ,
# AA. The list is not exhaustive; other fields are copied without any claim
# that they stay true.
def Rec.stale.if(same: Bool, +fs: List<&2, String>) -> Bool:
  match same:
    case True{}:
      False{}
    case False{}:
      +info = Rec.field(fs, 7n)
      Info.has(info, "CIGAR") || Info.has(info, "HOMLEN") || Info.has(info, "HOMSEQ") || Info.has(info, "AA")

# (Written as a match so INFO is only searched when the representation
# changed; `&&` evaluates both sides.)
def Rec.stale(+fs: List<&2, String>, v: Var, w: Var) -> Bool:
  Rec.stale.if(Rec.same_var(v, w), fs)

# ===========================================================================
# The reference (FASTA)
# ===========================================================================

# One sequence of the reference: its name and its letters as written (the
# FASTA bytes of its sequence lines, without line breaks, spaces and tabs).
type Contig is Data:
  Contig{name: String, raw: String}

def Fasta.is_head(l: String) -> Bool:
  String.starts_with(l, ">")

# The whitespace FASTA lines may hold: space, tab, CR (LF ends the line).
def Fasta.ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      U32.is_eq(x, 32) || U32.is_eq(x, 9) || U32.is_eq(x, 13)

def Fasta.name.put(stop: Bool, h: Char, rest: String) -> String:
  match stop:
    case True{}:
      SNil{}
    case False{}:
      SCon{h, rest}

def Fasta.name.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Fasta.name.put(Fasta.ws(h), h, Fasta.name.go(t))

# A header line's name: the text after '>' up to the first space, tab or CR.
def Fasta.name(l: String) -> String:
  Fasta.name.go(String.drop(l, 1n))

def Fasta.strip.put(space: Bool, h: Char, rest: String) -> String:
  match space:
    case True{}:
      rest
    case False{}:
      SCon{h, rest}

# A sequence line without its spaces, tabs and CRs.
def Fasta.strip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Fasta.strip.put(Fasta.ws(h), h, Fasta.strip(t))

def Fasta.seq.put(head: Bool, +l: String, rest: String) -> String:
  match head:
    case True{}:
      SNil{}
    case False{}:
      Fasta.strip(l) ++ rest

# The letters of the lines up to the next header line.
def Fasta.seq(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> t:
      Fasta.seq.put(Fasta.is_head(l), l, Fasta.seq(t))

def Fasta.go.put(head: Bool, +l: String, +t: List<&2, String>, rest: List<&2, Contig>) -> List<&2, Contig>:
  match head:
    case True{}:
      Contig{Fasta.name(l), Fasta.seq(t)} <> rest
    case False{}:
      rest

def Fasta.go(ls: List<&2, String>) -> List<&2, Contig>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +t:
      Fasta.go.put(Fasta.is_head(l), l, t, Fasta.go(t))

def Fasta.seen(+n: String, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case m <> t:
      String.eq(n, m) || Fasta.seen(n, t)

def Fasta.keep.put(skip: Bool, +n: String, +r: String, t: List<&2, Contig>, +seen: List<&2, String>, rest: List<&2, Contig>) -> List<&2, Contig>:
  match skip:
    case True{}:
      rest
    case False{}:
      Contig{n, r} <> rest

def Fasta.keep(cs: List<&2, Contig>, +seen: List<&2, String>) -> List<&2, Contig>:
  match cs:
    case Nil{}:
      Nil{}
    case Contig{+n, +r} <> +t:
      +skip = String.is_empty(n) || Fasta.seen(n, seen)
      Fasta.keep.put(skip, n, r, t, seen, Fasta.keep(t, Bool.pick(List<&2, String>, skip, seen, n <> seen)))

# The contigs of a FASTA file, in order: one for each header line (a line
# starting with '>'), with the letters of the lines up to the next header line.
# Text before the first header line is ignored. A header with an empty name,
# or a name already seen, is skipped with its lines (as samtools faidx keeps
# the first of two contigs with the same name).
def Fasta.parse(text: String) -> List<&2, Contig>:
  Fasta.keep(Fasta.go(String.split(text, '\n')), Nil{})

def Fasta.find.put(hit: Bool, raw: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{raw}
    case False{}:
      rest

# The letters of the contig named name, if there is one.
def Fasta.find(fa: List<&2, Contig>, +name: String) -> Maybe<&2, String>:
  match fa:
    case Nil{}:
      None{}
    case Contig{n, r} <> t:
      Fasta.find.put(String.eq(n, name), r, Fasta.find(t, name))

# A contig's letters read as bases (Base.of_fasta).
def Bases.of_fasta(s: String) -> List<&2, Base>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{h, t}:
      Base.of_fasta(h) <> Bases.of_fasta(t)

# ===========================================================================
# Outcomes, messages and options
# ===========================================================================

# The codes the tool reports on stderr.
type Code is Data:
  Malformed{}
  UnknownChrom{}
  BadEnd{}
  NonAcgtn{}
  BadPos{}
  AltDup{}
  RefMismatch{}
  Unsorted{}
  NoHeader{}
  Stale{}

def Code.name(c: Code) -> String:
  match c:
    case Malformed{}:
      "MALFORMED"
    case UnknownChrom{}:
      "UNKNOWN_CHROM"
    case BadEnd{}:
      "BAD_END"
    case NonAcgtn{}:
      "NON_ACGTN"
    case BadPos{}:
      "BAD_POS"
    case AltDup{}:
      "ALT_DUP"
    case RefMismatch{}:
      "REF_MISMATCH"
    case Unsorted{}:
      "UNSORTED"
    case NoHeader{}:
      "NO_HEADER"
    case Stale{}:
      "POSSIBLY_STALE"

# What happens to one body line (every line after the #CHROM line).
#   Broken: MALFORMED, the run stops.
#   Skipped: out of scope, passed through unchanged.
#   NoContig: CHROM is not in the reference, the run stops.
#   Problem: one of BAD_END, NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH; the run
#     stops under -c e, the line is passed through under -c w.
#   Normalized: the line is written in normal form.
type Outcome is Data:
  Broken{}
  Skipped{}
  NoContig{}
  Problem{c: Code}
  Normalized{}

# The result for one body line: its outcome, the position it is sorted by
# (its output POS when normalized, else its input POS), its output text (without
# terminator), and whether to report POSSIBLY_STALE.
type Res is Data:
  Res{out: Outcome, key: Nat, text: String, stale: Bool}

# Where a message points: the line number in the file (from 1), and the line's
# CHROM and POS fields as written.
type At is Data:
  At{line: Nat, chrom: String, pos: String}

# A message on stderr.
#   Warning: a line was passed through with a problem (-c w), or POSSIBLY_STALE.
#   Stop: the run stops (exit code 1). For UNSORTED, at is the line that would
#     come out of order and prev the line already written that it would have
#     to come before (none when a CHROM comes back after another one).
#   Summary: the run succeeded (exit code 0), with counts of body lines: all,
#     changed by normalization, out of scope, passed through with a problem.
type Note is Data:
  Warning{code: Code, at: At}
  Stop{code: Code, at: Maybe<&2, At>, prev: Maybe<&2, At>}
  Summary{lines: Nat, changed: Nat, skipped: Nat, warned: Nat}

def At.show(a: At) -> String:
  match a:
    case At{l, c, p}:
      c ++ "\t" ++ p ++ "\tline " ++ Nat.show(l)

def At.show_maybe(m: Maybe<&2, At>, lead: String) -> String:
  match m:
    case None{}:
      ""
    case Some{a}:
      lead ++ At.show(a)

# The text of a message: one line.
def Note.render(n: Note) -> String:
  match n:
    case Warning{c, a}:
      Code.name(c) ++ "\t" ++ At.show(a) ++ "\n"
    case Stop{c, a, k}:
      "error: " ++ Code.name(c) ++ At.show_maybe(a, "\t") ++ At.show_maybe(k, "\tbefore\t") ++ "\n"
    case Summary{n, ch, sk, wa}:
      "framebender: " ++ Nat.show(n) ++ " records, " ++ Nat.show(ch) ++ " changed, " ++ Nat.show(sk) ++ " out of scope, " ++ Nat.show(wa) ++ " passed with a problem\n"

# The options of one run.
#   strict: True for -c e (the default: a problem stops the run), False for -c w.
#   w: the sorting window (-w, default 1000, at least 1).
#   args: the command-line arguments that decide the output, recorded in the
#     header: all those after "norm" except --threads, -o and -O and their
#     values (which only size the program's work, or choose how and where the
#     text is written), so the text is the same for every N, every output
#     file and every output type.
type Opts is Data:
  Opts{strict: Bool, w: Nat, args: List<&2, String>}

# A parsed command line: the options, the FASTA path, the VCF path. The thread
# count (--threads) and the output options (-o, -O) are not part of it (see
# Args.threads, Args.output).
type Cfg is Data:
  Cfg{opts: Opts, ref: String, vcf: String}

# The usage message, printed on a usage error (exit code 2).
def usage() -> String:
  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"

# The largest thread count --threads accepts: a chosen limit, the most worker
# threads Bend's runtime runs and the size of the driver's tables.
def Args.max_threads() -> Nat:
  128n

# Reading the command line: which option is waiting for its value.
type Pend is Data:
  PNone{}
  PRef{}
  PCheck{}
  PWin{}
  PThr{}
  POut{}
  PType{}

# An output type, as -O names it: v, plain VCF (z False), or z, VCF in BGZF
# (z True), with a compression level from 0 to 9 (level, on htslib's scale;
# None when -O gives no digit).
type OType is Data:
  OType{z: Bool, level: Maybe<&2, Nat>}

# What the command line says about how the program works and writes, never
# about what it writes: the thread count (--threads N), the output path (-o),
# the output type (-O: z True for BGZF) and the compression level (the digit
# of -O z0 ... z9). For each, the last one given; a later -O without a digit
# keeps the level, as in bcftools 1.24 (-Oz0 -Oz is level 0).
type Drv is Data:
  Drv{thr: Maybe<&2, Nat>, out: Maybe<&2, String>, z: Maybe<&2, Bool>, lvl: Maybe<&2, Nat>}

def Drv.none() -> Drv:
  Drv{None{}, None{}, None{}, None{}}

def Drv.thr(d: Drv) -> Maybe<&2, Nat>:
  match d:
    case Drv{t, o, z, l}:
      t

def Drv.set_thr(+n: Nat, d: Drv) -> Drv:
  match d:
    case Drv{t, o, z, l}:
      Drv{Some{n}, o, z, l}

def Drv.set_out(+x: String, d: Drv) -> Drv:
  match d:
    case Drv{t, o, z, l}:
      Drv{t, Some{x}, z, l}

def Drv.keep_lvl(m: Maybe<&2, Nat>, l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{+x}:
      Some{x}
    case None{}:
      l

def Drv.set_typ(x: OType, d: Drv) -> Drv:
  match x d:
    case OType{y, m} Drv{t, o, z, l}:
      Drv{t, o, Some{y}, Drv.keep_lvl(m, l)}

# Two characters are equal ignoring ASCII case (b in lower case).
def Args.ceq(a: Char, b: Char) -> Bool:
  +x = Char.code(a)
  +y = Char.code(b)
  U32.is_eq(x, y) || (U32.is_ge(x, 65) && U32.is_le(x, 90) && U32.is_eq(U32.add(x, 32), y))

def Args.eq_ci(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{x, s} SCon{y, t}:
      Args.ceq(x, y) && Args.eq_ci(s, t)
    case _ _:
      False{}

# The word x ends with e (in lower case), in any case: how bcftools 1.24
# compares a file name's extension.
def Args.ends_ci(+x: String, +e: String) -> Bool:
  Nat.is_le(String.length(e), String.length(x)) && Args.eq_ci(String.drop(x, Nat.sub(String.length(x), String.length(e))), e)

# A path that names a BCF file (.bcf): bcftools writes BCF there, whatever -O
# says. framebender writes no BCF, so -o refuses it.
def Args.bcf(+x: String) -> Bool:
  Args.ends_ci(x, ".bcf")

def Args.otype.lvl(ok: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, OType>:
  match ok m:
    case True{} Some{+d}:
      Some{OType{True{}, Some{d}}}
    case _ _:
      None{}

# The value of -O: v, z, or z and one digit (the level). BCF (b, u) is not
# written: a usage error.
def Args.otype(+x: String) -> Maybe<&2, OType>:
  Bool.pick(Maybe<&2, OType>, String.eq(x, "v"), Some{OType{False{}, None{}}},
  Bool.pick(Maybe<&2, OType>, String.eq(x, "z"), Some{OType{True{}, None{}}},
  Args.otype.lvl(String.starts_with(x, "z") && Nat.is_eq(String.length(x), 2n), Pos.read(String.drop(x, 1n)))))

# The command line read so far; ok turns False on any error. drv: the thread
# count and the output options; keep: the arguments recorded in the header
# (all but --threads, -o, -O and their values), in order.
type ArgSt is Data:
  ArgSt{pend: Pend, strict: Bool, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}

def Args.typ(m: Maybe<&2, OType>, st: ArgSt) -> ArgSt:
  match m st:
    case Some{y} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, Drv.set_typ(y, t), r, v, ok, k}
    case None{} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, t, r, v, False{}, k}

def Args.word(+x: String, st: ArgSt) -> ArgSt:
  match st:
    case ArgSt{p, +s, +w, +t, +r, +v, +ok, +k}:
      +opt = String.starts_with(x, "-") && Nat.is_lt(1n, String.length(x))
      +kx = List.append(&2, String, k, [x])
      Bool.pick(ArgSt, String.eq(x, "-f"), ArgSt{PRef{}, s, w, t, r, v, ok, kx},
      Bool.pick(ArgSt, String.eq(x, "-c"), ArgSt{PCheck{}, s, w, t, r, v, ok, kx},
      Bool.pick(ArgSt, String.eq(x, "-w"), ArgSt{PWin{}, s, w, t, r, v, ok, kx},
      Bool.pick(ArgSt, String.eq(x, "--threads"), ArgSt{PThr{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.eq(x, "-o"), ArgSt{POut{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.eq(x, "-O"), ArgSt{PType{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.starts_with(x, "-O"), Args.typ(Args.otype(String.drop(x, 2n)), ArgSt{PType{}, s, w, t, r, v, ok, k}),
      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx})))))))

def Args.win(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
  match m st:
    case Some{+n} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, Some{n}, t, r, v, ok && Nat.is_le(1n, n), k}
    case None{} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, t, r, v, False{}, k}

def Args.thr(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
  match m st:
    case Some{+n} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, Drv.set_thr(n, t), r, v, ok && Nat.is_le(1n, n) && Nat.is_le(n, Args.max_threads()), k}
    case None{} ArgSt{p, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, t, r, v, False{}, k}

# The state after one more argument x. Every argument is recorded (keep)
# except --threads, -o and -O (glued -OT too) and their values.
def Args.step(st: ArgSt, +x: String) -> ArgSt:
  match st:
    case ArgSt{PNone{}, s, w, t, r, v, ok, k}:
      Args.word(x, ArgSt{PNone{}, s, w, t, r, v, ok, k})
    case ArgSt{PRef{}, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, t, Some{x}, v, ok && Maybe.is_none(&2, String, r), List.append(&2, String, k, [x])}
    case ArgSt{PCheck{}, +s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, String.eq(x, "e") || (s && Bool.not(String.eq(x, "w"))), w, t, r, v, ok && (String.eq(x, "e") || String.eq(x, "w")), List.append(&2, String, k, [x])}
    case ArgSt{PWin{}, s, w, t, r, v, ok, k}:
      Args.win(Pos.read(x), ArgSt{PWin{}, s, w, t, r, v, ok, List.append(&2, String, k, [x])})
    case ArgSt{PThr{}, s, w, t, r, v, ok, k}:
      Args.thr(Pos.read(x), ArgSt{PThr{}, s, w, t, r, v, ok, k})
    case ArgSt{POut{}, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, s, w, Drv.set_out(x, t), r, v, ok && Bool.not(Args.bcf(x)), k}
    case ArgSt{PType{}, s, w, t, r, v, ok, k}:
      Args.typ(Args.otype(x), ArgSt{PType{}, s, w, t, r, v, ok, k})

def Args.go(xs: List<&2, String>, st: ArgSt) -> ArgSt:
  match xs:
    case Nil{}:
      st
    case +x <> t:
      Args.go(t, Args.step(st, x))

def Args.done(st: ArgSt) -> Maybe<&2, Cfg>:
  match st:
    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
      Some{Cfg{Opts{s, Maybe.default(&2, Nat, w, 1000n), k}, r, v}}
    case _:
      None{}

# The state before the first argument after "norm".
def Args.init() -> ArgSt:
  ArgSt{PNone{}, True{}, None{}, Drv.none(), None{}, None{}, True{}, Nil{}}

def Args.done.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Cfg>:
  match ok:
    case True{}:
      Args.done(Args.go(rest, Args.init()))
    case False{}:
      None{}

# The command line after the program name: "norm", then the options -f FASTA
# (required), -c e or -c w (default e), -w N (N at least 1, default 1000),
# --threads N (N from 1 to Args.max_threads()), -o PATH (any word not ending
# in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9) in any order, and one
# VCF path. None for anything else (a usage error). For -c, -w, --threads, -o
# and -O every one given must be valid, and the last one counts.
def Args.parse(argv: List<&2, String>) -> Maybe<&2, Cfg>:
  match argv:
    case Nil{}:
      None{}
    case +cmd <> +rest:
      Args.done.if(String.eq(cmd, "norm"), rest)

def Args.expecting.of(st: ArgSt) -> Bool:
  match st:
    case ArgSt{PNone{}, s, w, t, r, v, ok, k}:
      True{}
    case _:
      False{}

# The words pre, read after "norm", leave the parser where an option may come:
# no option waiting for its value (after an error too: the line is refused
# then, with or without the words that follow).
def Args.expecting(pre: List<&2, String>) -> Bool:
  Args.expecting.of(Args.go(pre, Args.init()))

def Args.thr.done(st: ArgSt) -> Maybe<&2, Nat>:
  match st:
    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
      Drv.thr(t)
    case _:
      None{}

def Args.threads.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Args.thr.done(Args.go(rest, Args.init()))
    case False{}:
      None{}

# The thread count of a command line Args.parse accepts: Some{n} for its last
# --threads n (then 1 <= n <= Args.max_threads()), None when it has none. None
# for every command line Args.parse refuses. The program may size its work by
# it; law threads (MACHINE.bend) says that changes nothing it writes.
def Args.threads(argv: List<&2, String>) -> Maybe<&2, Nat>:
  match argv:
    case Nil{}:
      None{}
    case +cmd <> +rest:
      Args.threads.if(String.eq(cmd, "norm"), rest)

# ---------------------------------------------------------------------------
# Output options (they choose how and where the text is written; law output)
# ---------------------------------------------------------------------------

def Args.out_opt.two(+a: String, +b: String) -> Bool:
  (String.eq(a, "-o") && Bool.not(Args.bcf(b))) || (String.eq(a, "-O") && Maybe.is_some(&2, OType, Args.otype(b)))

def Args.out_opt.more(+a: String, t: List<&2, String>) -> Bool:
  match t:
    case Nil{}:
      String.starts_with(a, "-O") && Maybe.is_some(&2, OType, Args.otype(String.drop(a, 2n)))
    case +b <> u:
      match u:
        case Nil{}:
          Args.out_opt.two(a, b)
        case _:
          False{}

# One output option, as its words: -o PATH (PATH not ending in .bcf), -O T or
# the glued -OT (T a type Args.otype accepts).
def Args.out_opt(o: List<&2, String>) -> Bool:
  match o:
    case Nil{}:
      False{}
    case +a <> t:
      Args.out_opt.more(a, t)

# The default compression level of -O z (htslib's and bgzip's default).
def Args.level() -> Nat:
  6n

# Where and how the text is written.
#   file: the path to write, None for stdout (no -o, or -o -);
#   z: BGZF (True) or plain text; level: the compression level (0 to 9),
#   unused when z is False.
type Sink is Data:
  Sink{file: Maybe<&2, String>, z: Bool, level: Nat}

def Args.file(o: Maybe<&2, String>) -> Maybe<&2, String>:
  match o:
    case None{}:
      None{}
    case Some{+p}:
      Bool.pick(Maybe<&2, String>, String.eq(p, "-"), None{}, Some{p})

# The type a path's extension names, as bcftools 1.24 reads it: .vcf plain,
# .vcf.gz and .vcf.bgz BGZF (in any case); None for any other path.
def Args.ext(+p: String) -> Maybe<&2, Bool>:
  Bool.pick(Maybe<&2, Bool>, Args.ends_ci(p, ".vcf"), Some{False{}},
  Bool.pick(Maybe<&2, Bool>, Args.ends_ci(p, ".vcf.gz") || Args.ends_ci(p, ".vcf.bgz"), Some{True{}}, None{}))

def Args.ext.of(o: Maybe<&2, String>) -> Maybe<&2, Bool>:
  match o:
    case None{}:
      None{}
    case Some{+p}:
      Args.ext(p)

def Args.z.of(e: Maybe<&2, Bool>, y: Maybe<&2, Bool>) -> Bool:
  match e y:
    case Some{b} _:
      b
    case None{} Some{z}:
      z
    case None{} None{}:
      False{}

# The output: to the -o path (stdout without one, or for -o -); BGZF or plain
# by the path's extension if it names one (as bcftools 1.24, whatever -O
# says), else by the last -O (plain without one); the last level given, else
# Args.level().
def Args.sink(d: Drv) -> Sink:
  match d:
    case Drv{t, +o, z, l}:
      Sink{Args.file(o), Args.z.of(Args.ext.of(o), z), Maybe.default(&2, Nat, l, Args.level())}

def Args.sink.done(st: ArgSt) -> Maybe<&2, Sink>:
  match st:
    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
      Some{Args.sink(t)}
    case _:
      None{}

def Args.output.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Sink>:
  match ok:
    case True{}:
      Args.sink.done(Args.go(rest, Args.init()))
    case False{}:
      None{}

# The output of a command line Args.parse accepts; None for every command
# line it refuses. The driver writes the text there; law output
# (MACHINE.bend) says the output options change nothing in the text.
def Args.output(argv: List<&2, String>) -> Maybe<&2, Sink>:
  match argv:
    case Nil{}:
      None{}
    case +cmd <> +rest:
      Args.output.if(String.eq(cmd, "norm"), rest)
