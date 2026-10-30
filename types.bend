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
  UndefinedTag{tag: String}
  BadCount{}
  BadGt{}
  DupAlts{}

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
    case UndefinedTag{t}:
      "UNDEFINED_TAG"
    case BadCount{}:
      "BAD_COUNT"
    case BadGt{}:
      "BAD_GT"
    case DupAlts{}:
      "ALT_DUP"

# What a message adds after where it points: for a line -m could not split,
# that it was not split, and for UNDEFINED_TAG the tag (INFO/XX or
# FORMAT/XX) and how to fix it. Nothing for any other code.
def Code.detail(c: Code) -> String:
  match c:
    case UndefinedTag{t}:
      "\t" ++ t ++ " has no usable header line (add one, e.g. with bcftools annotate -h); not split"
    case BadCount{}:
      "\tnot split"
    case BadGt{}:
      "\tnot split"
    case DupAlts{}:
      "\tnot split"
    case _:
      ""

# What happens to one body line (every line after the #CHROM line).
#   Broken: MALFORMED, the run stops.
#   Skipped: out of scope, passed through unchanged.
#   NoContig: CHROM is not in the reference, the run stops.
#   Problem: one of BAD_END, NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH; the run
#     stops under -c e, the line is passed through under -c w. (-m adds
#     UNDEFINED_TAG, BAD_COUNT and BAD_GT for a line it cannot split: B.Parts.)
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
#   Summary: the run succeeded (exit code 0), with counts of records (with
#     -m, after splitting: each record of a split line counts): all, changed
#     by normalization, out of scope, passed through with a problem.
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
    case Warning{+c, a}:
      Code.name(c) ++ "\t" ++ At.show(a) ++ Code.detail(c) ++ "\n"
    case Stop{+c, a, k}:
      "error: " ++ Code.name(c) ++ At.show_maybe(a, "\t") ++ At.show_maybe(k, "\tbefore\t") ++ Code.detail(c) ++ "\n"
    case Summary{n, ch, sk, wa}:
      "framebender: " ++ Nat.show(n) ++ " records, " ++ Nat.show(ch) ++ " changed, " ++ Nat.show(sk) ++ " out of scope, " ++ Nat.show(wa) ++ " passed with a problem\n"

# The options of one run.
#   strict: True for -c e (the default: a problem stops the run), False for -c w.
#   w: the sorting window (-w, default 1000, at least 1).
#   split: -m -any (or -m -both, -m -): a record with two or more ALTs is
#     written as one record per ALT (B.Rec.parts).
#   over0: --multi-overlaps 0 (the default): in the record for one ALT, a
#     genotype's other ALTs become REF (0); False for --multi-overlaps '.':
#     they become missing ('.').
#   args: the command-line arguments that decide the output, recorded in the
#     header: all those after "norm" except --threads, -o and -O and their
#     values (which only size the program's work, or choose how and where the
#     text is written), so the text is the same for every N, every output
#     file and every output type.
type Opts is Data:
  Opts{strict: Bool, w: Nat, split: Bool, over0: Bool, args: List<&2, String>}

# A parsed command line: the options, the FASTA path, the VCF path. The thread
# count (--threads) and the output options (-o, -O) are not part of it (see
# Args.threads, Args.output).
type Cfg is Data:
  Cfg{opts: Opts, ref: String, vcf: String}

# The usage message, printed on a usage error (exit code 2).
def usage() -> String:
  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [-m -any|-both|-] [--multi-overlaps 0|.] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"

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
  PMulti{}
  POver{}

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

# The options read so far that decide the text: -c (strict), -m (split),
# --multi-overlaps (over0).
type Sci is Data:
  Sci{strict: Bool, split: Bool, over0: Bool}

def Sci.check(+x: String, s: Sci) -> Sci:
  match s:
    case Sci{+c, m, z}:
      Sci{String.eq(x, "e") || (c && Bool.not(String.eq(x, "w"))), m, z}

def Sci.multi(s: Sci) -> Sci:
  match s:
    case Sci{c, m, z}:
      Sci{c, True{}, z}

def Sci.over(+x: String, s: Sci) -> Sci:
  match s:
    case Sci{c, m, +z}:
      Sci{c, m, String.eq(x, "0") || (z && Bool.not(String.eq(x, ".")))}

# The values -m accepts: -any, -both and - (all three split every record with
# two or more ALTs, as in bcftools 1.24). -snps, -indels and the joining forms
# (+...) are not accepted.
def Args.multi(+x: String) -> Bool:
  String.eq(x, "-any") || String.eq(x, "-both") || String.eq(x, "-")

# The command line read so far; ok turns False on any error. drv: the thread
# count and the output options; keep: the arguments recorded in the header
# (all but --threads, -o, -O and their values), in order.
type ArgSt is Data:
  ArgSt{pend: Pend, sci: Sci, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}

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
      Bool.pick(ArgSt, String.eq(x, "-m"), ArgSt{PMulti{}, s, w, t, r, v, ok, kx},
      Bool.pick(ArgSt, String.eq(x, "--multi-overlaps"), ArgSt{POver{}, s, w, t, r, v, ok, kx},
      Bool.pick(ArgSt, String.starts_with(x, "-m"), ArgSt{PNone{}, Sci.multi(s), w, t, r, v, ok && Args.multi(String.drop(x, 2n)), kx},
      Bool.pick(ArgSt, String.eq(x, "--threads"), ArgSt{PThr{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.eq(x, "-o"), ArgSt{POut{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.eq(x, "-O"), ArgSt{PType{}, s, w, t, r, v, ok, k},
      Bool.pick(ArgSt, String.starts_with(x, "-O"), Args.typ(Args.otype(String.drop(x, 2n)), ArgSt{PType{}, s, w, t, r, v, ok, k}),
      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx}))))))))))

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
    case ArgSt{PCheck{}, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, Sci.check(x, s), w, t, r, v, ok && (String.eq(x, "e") || String.eq(x, "w")), List.append(&2, String, k, [x])}
    case ArgSt{PMulti{}, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, Sci.multi(s), w, t, r, v, ok && Args.multi(x), List.append(&2, String, k, [x])}
    case ArgSt{POver{}, s, w, t, r, v, ok, k}:
      ArgSt{PNone{}, Sci.over(x, s), w, t, r, v, ok && (String.eq(x, "0") || String.eq(x, ".")), List.append(&2, String, k, [x])}
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
    case ArgSt{PNone{}, Sci{c, m, z}, w, t, Some{r}, Some{v}, True{}, k}:
      Some{Cfg{Opts{c, Maybe.default(&2, Nat, w, 1000n), m, z, k}, r, v}}
    case _:
      None{}

# The state before the first argument after "norm".
def Args.init() -> ArgSt:
  ArgSt{PNone{}, Sci{True{}, False{}, True{}}, None{}, Drv.none(), None{}, None{}, True{}, Nil{}}

def Args.done.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Cfg>:
  match ok:
    case True{}:
      Args.done(Args.go(rest, Args.init()))
    case False{}:
      None{}

# The command line after the program name: "norm", then the options -f FASTA
# (required), -c e or -c w (default e), -w N (N at least 1, default 1000),
# -m X or the glued -mX (X: -any, -both or -; no -m: records are not split),
# --multi-overlaps 0 or --multi-overlaps . (default 0; without -m it changes
# nothing but the header's command line),
# --threads N (N from 1 to Args.max_threads()), -o PATH (any word not ending
# in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9) in any order, and one
# VCF path. None for anything else (a usage error). For -c, -w, -m,
# --multi-overlaps, --threads, -o and -O every one given must be valid, and
# the last one counts.
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


# ===========================================================================
# Splitting multiallelic records (-m)
# ===========================================================================

# How many values an INFO or FORMAT tag has, as its header definition's
# Number says (VCF 4.3, section 1.4.2): A, one per ALT allele; R, one per
# allele, REF first; G, one per genotype; Other, a count (0 for a flag), '.'
# (any number) or P (one per copy of the chromosome), which -m copies whole;
# Unknown, no Number or one framebender does not read (such as VCF 4.4's LA,
# LR, LG), which -m refuses to guess about.
type Num is Data:
  NumA{}
  NumR{}
  NumG{}
  NumOther{}
  NumUnknown{}

# One INFO or FORMAT definition of the header: the tag's ID and its Number.
type Tag is Data:
  Tag{id: String, num: Num}

# The header's definitions, in header order: the INFO tags, the FORMAT tags.
type Defs is Data:
  Defs{info: List<&2, Tag>, fmt: List<&2, Tag>}

def Defs.info(d: Defs) -> List<&2, Tag>:
  match d:
    case Defs{i, f}:
      i

def Defs.fmt(d: Defs) -> List<&2, Tag>:
  match d:
    case Defs{i, f}:
      f

def Hdr.push(h: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{h, SNil{}}]
    case p <> t:
      SCon{h, p} <> t

def Hdr.cut.put(comma: Bool, h: Char, rest: List<&2, String>) -> List<&2, String>:
  match comma:
    case True{}:
      "" <> rest
    case False{}:
      Hdr.push(h, rest)

# A definition's text cut at every comma outside double quotes (q: inside
# quotes; esc: inside quotes, after a backslash, so this character does not
# end them). The Description of ##INFO=<ID=DP,Number=1,Description="a, b">
# stays one piece.
def Hdr.cut(s: String, +q: Bool, +esc: Bool) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+h, t}:
      +x = Char.code(h)
      +quote = U32.is_eq(x, 34) && Bool.not(esc)
      Hdr.cut.put(U32.is_eq(x, 44) && Bool.not(q), h,
        Hdr.cut(t, Bool.pick(Bool, quote, Bool.not(q), q), q && Bool.not(esc) && U32.is_eq(x, 92)))

def Hdr.ltrim.put(keep: Bool, h: Char, rest: String) -> String:
  match keep:
    case True{}:
      SCon{h, rest}
    case False{}:
      rest

def Hdr.ltrim.go(s: String, +keep: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      +k = keep || Bool.not(U32.is_eq(Char.code(h), 32))
      Hdr.ltrim.put(k, h, Hdr.ltrim.go(t, k))

# Text without the spaces at its start and at its end (htslib 1.24 reads
# "ID=IA, Number=A" and "Number = A " as Number A; a tab is not trimmed).
def Hdr.trim(s: String) -> String:
  String.reverse(Hdr.ltrim.go(String.reverse(Hdr.ltrim.go(s, False{})), False{}))

def Hdr.value.put(hit: Bool, +p: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{Hdr.trim(String.drop(p, Nat.add(String.length(Info.key(p)), 1n)))}
    case False{}:
      rest

# The value of the first piece "k=value" (key and value trimmed).
def Hdr.value(ps: List<&2, String>, +k: String) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case +p <> t:
      Hdr.value.put(String.eq(Hdr.trim(Info.key(p)), k) && Nat.is_lt(String.length(Info.key(p)), String.length(p)), p, Hdr.value(t, k))

# A Number: A, R, G; '.', P or a count (digits) are Other; anything else, or
# none, is Unknown.
def Num.of(m: Maybe<&2, String>) -> Num:
  match m:
    case None{}:
      NumUnknown{}
    case Some{+v}:
      Bool.pick(Num, String.eq(v, "A"), NumA{},
      Bool.pick(Num, String.eq(v, "R"), NumR{},
      Bool.pick(Num, String.eq(v, "G"), NumG{},
      Bool.pick(Num, String.eq(v, ".") || String.eq(v, "P") || Maybe.is_some(&2, Nat, Pos.read(v)), NumOther{}, NumUnknown{}))))

def Hdr.tag.of(m: Maybe<&2, String>, +ps: List<&2, String>) -> Maybe<&2, Tag>:
  match m:
    case None{}:
      None{}
    case Some{id}:
      Some{Tag{id, Num.of(Hdr.value(ps, "Number"))}}

# The tag a definition defines, from its text after '<' (one '>' at its end
# dropped, after trimming): its first ID and its first Number. None without an
# ID.
def Hdr.tag(+s: String) -> Maybe<&2, Tag>:
  +t = Hdr.trim(s)
  +ps = Hdr.cut(Bool.pick(String, String.ends_with(t, ">"), String.take(t, Nat.sub(String.length(t), 1n)), t), False{}, False{})
  Hdr.tag.of(Hdr.value(ps, "ID"), ps)

def Defs.add_info(m: Maybe<&2, Tag>, d: Defs) -> Defs:
  match m d:
    case None{} _:
      d
    case Some{t} Defs{i, f}:
      Defs{List.append(&2, Tag, i, [t]), f}

def Defs.add_fmt(m: Maybe<&2, Tag>, d: Defs) -> Defs:
  match m d:
    case None{} _:
      d
    case Some{t} Defs{i, f}:
      Defs{i, List.append(&2, Tag, f, [t])}

# One more header line: "##INFO=<...>" adds an INFO tag, "##FORMAT=<...>" a
# FORMAT tag; any other line changes nothing.
def Defs.line(+d: Defs, +body: String) -> Defs:
  Bool.pick(Defs, String.starts_with(body, "##INFO=<"), Defs.add_info(Hdr.tag(String.drop(body, 8n)), d),
  Bool.pick(Defs, String.starts_with(body, "##FORMAT=<"), Defs.add_fmt(Hdr.tag(String.drop(body, 10n)), d), d))

def Tags.find.put(hit: Bool, n: Num, rest: Maybe<&2, Num>) -> Maybe<&2, Num>:
  match hit:
    case True{}:
      Some{n}
    case False{}:
      rest

# The Number of tag k: its first definition counts (as in htslib 1.24); None
# when the header does not define k.
def Tags.find(ts: List<&2, Tag>, +k: String) -> Maybe<&2, Num>:
  match ts:
    case Nil{}:
      None{}
    case Tag{id, n} <> t:
      Tags.find.put(String.eq(id, k), n, Tags.find(t, k))

# The Number is A, R or G: the tag has values per allele or per genotype.
def Num.per_allele(m: Maybe<&2, Num>) -> Bool:
  match m:
    case Some{NumA{}}:
      True{}
    case Some{NumR{}}:
      True{}
    case Some{NumG{}}:
      True{}
    case _:
      False{}

# A field of a split record (its text), or the reason the record cannot be
# split.
type Got is Data:
  Got{s: String}
  Refuse{c: Code}

def Got.cat(a: Got, +sep: String, b: Got) -> Got:
  match a b:
    case Refuse{c} _:
      Refuse{c}
    case Got{x} Refuse{c}:
      Refuse{c}
    case Got{x} Got{y}:
      Got{x ++ sep ++ y}

def Got.join.put(g: Got, t: List<&2, Got>, +sep: String, rest: Got) -> Got:
  match t:
    case Nil{}:
      g
    case _:
      Got.cat(g, sep, rest)

# The texts joined with sep, from the right (each text is copied once); the
# first refusal, if any.
def Got.join(gs: List<&2, Got>, +sep: String) -> Got:
  match gs:
    case Nil{}:
      Got{""}
    case g <> +t:
      Got.join.put(g, t, sep, Got.join(t, sep))

def Got.of(m: Maybe<&2, String>, c: Code) -> Got:
  match m:
    case Some{x}:
      Got{x}
    case None{}:
      Refuse{c}

def Vals.pick.cons(m: Maybe<&2, String>, rest: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match m rest:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def Vals.pick(+vs: List<&2, String>, ks: List<&2, Nat>) -> Maybe<&2, List<&2, String>>:
  match ks:
    case Nil{}:
      Some{Nil{}}
    case k <> t:
      Vals.pick.cons(List.get(&2, String, vs, k), Vals.pick(vs, t))

# The place of genotype j/k (j <= k) among a diploid sample's G values:
# k(k+1)/2 + j (VCF 4.3, section 1.6.2: 0/0, 0/1, 1/1, 0/2, 1/2, 2/2, ...).
def Gt.index(j: Nat, +k: Nat) -> Nat:
  Nat.add(Nat.div(Nat.mul(k, 1n+k), 2n), j)

# The number of diploid genotypes of a record with n ALTs: (n+1)(n+2)/2.
def Gt.count(+n: Nat) -> Nat:
  Nat.div(Nat.mul(1n+n, 2n+n), 2n)

# How many values a tag with Number A, R or G has in a record with n ALTs,
# for ploidy p (the number of chromosome copies; INFO counts as 2): A, n; R,
# n + 1; G, n + 1 when p is 1 (one value per allele), (n+1)(n+2)/2 when p is
# 2 (one per diploid genotype). None for G with any other p (-m does not split
# G values of more than two copies), and for any other Number.
def Vals.expected_count(num: Num, +n: Nat, +p: Nat) -> Maybe<&2, Nat>:
  match num:
    case NumA{}:
      Some{n}
    case NumR{}:
      Some{1n+n}
    case NumG{}:
      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(p, 1n), Some{1n+n},
      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(p, 2n), Some{Gt.count(n)}, None{}))
    case _:
      None{}

def Vals.fits(m: Maybe<&2, Nat>, +c: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, c)

# Which values the record for ALT i keeps, for ploidy p: A, ALT i's (value
# i - 1); R, REF's and ALT i's (0 and i); G with p = 1, REF's and ALT i's (0
# and i); G with p = 2, those of the genotypes 0/0, 0/i and i/i.
def Vals.idx(num: Num, +p: Nat, +i: Nat) -> List<&2, Nat>:
  match num:
    case NumA{}:
      [Nat.sub(i, 1n)]
    case NumR{}:
      [0n, i]
    case NumG{}:
      Bool.pick(List<&2, Nat>, Nat.is_eq(p, 1n), [0n, i], [0n, Gt.index(0n, i), Gt.index(i, i)])
    case _:
      Nil{}

def Vals.join(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{String.join(xs, ",")}

# The number of copies c values are for, given what the sample's GT says
# (Gt.copies): its count of copies; for a lone '.' GT (None), one copy when
# there are n + 1 values, else two ((n+1)(n+2)/2 and n + 1 never coincide for
# n >= 2, so the values kept are never in doubt).
def Vals.copies(m: Maybe<&2, Nat>, +n: Nat, +c: Nat) -> Nat:
  match m:
    case Some{p}:
      p
    case None{}:
      Bool.pick(Nat, Nat.is_eq(c, 1n+n), 1n, 2n)

def Vals.keep(+num: Num, +n: Nat, +p: Nat, +i: Nat, +vs: List<&2, String>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Vals.fits(Vals.expected_count(num, n, p), List.length(&2, String, vs)),
    Vals.join(Vals.pick(vs, Vals.idx(num, p, i))), None{})

def Vals.split.if(missing: Bool, +num: Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, v: String) -> Maybe<&2, String>:
  match missing:
    case True{}:
      Some{"."}
    case False{}:
      +vs = String.split(v, ',')
      Vals.keep(num, n, Vals.copies(cp, n, List.length(&2, String, vs)), i, vs)

# A per-allele value (comma-separated values) in the record for ALT i of n,
# for the copies cp (Gt.copies; Some{2} in INFO): a lone '.' (the whole value
# missing) stays '.'; else it must have expected_count values for its copies
# (Vals.copies), and the record keeps those Vals.idx names, joined by commas.
# None (BAD_COUNT) for any other count.
def Vals.split(+num: Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +v: String) -> Maybe<&2, String>:
  Vals.split.if(String.eq(v, "."), num, n, cp, i, v)

# An INFO entry with a value ("key=values"): UNDEFINED_TAG when the header
# does not define its key, or defines it with an Unknown Number; kept as it
# is for Number Other; per-allele values for A, R, G (ploidy 2).
def Info.split.eq(m: Maybe<&2, Num>, +k: String, +e: String, +n: Nat, +i: Nat) -> Got:
  match m:
    case None{}:
      Refuse{UndefinedTag{"INFO/" ++ k}}
    case Some{NumUnknown{}}:
      Refuse{UndefinedTag{"INFO/" ++ k}}
    case Some{NumOther{}}:
      Got{e}
    case Some{num}:
      Got.cat(Got{k}, "=", Got.of(Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), BadCount{}))

# An INFO entry: an entry without '=' (a flag, an empty entry between two
# ';') has no values to share and is kept, unless its tag is A, R or G
# (BAD_COUNT); an entry with a value as Info.split.eq says.
def Info.split.num(+m: Maybe<&2, Num>, +e: String, +n: Nat, +i: Nat) -> Got:
  +k = Info.key(e)
  Bool.pick(Got, String.eq(k, e), Bool.pick(Got, Num.per_allele(m), Refuse{BadCount{}}, Got{e}), Info.split.eq(m, k, e, n, i))

def Info.split.go(es: List<&2, String>, +info: List<&2, Tag>, +n: Nat, +i: Nat) -> List<&2, Got>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Info.split.num(Tags.find(info, Info.key(e)), e, n, i) <> Info.split.go(t, info, n, i)

# INFO in the record for ALT i of n: each entry as Info.split.num says, in
# order. A missing INFO ('.') is one entry without '=': kept.
def Info.split(+info: String, +tags: List<&2, Tag>, +n: Nat, +i: Nat) -> Got:
  Got.join(Info.split.go(String.split(info, ';'), tags, n, i), ";")

# The allele a genotype names, in the record for ALT i: REF (0) stays REF;
# ALT i becomes 1, the record's one ALT; any other ALT becomes REF under
# --multi-overlaps 0 (over0, the default) or missing under
# --multi-overlaps '.'; missing (None) stays missing.
def Gt.rule(over0: Bool, +i: Nat, a: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      None{}
    case Some{+x}:
      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(x, 0n), Some{0n},
      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(x, i), Some{1n},
      Bool.pick(Maybe<&2, Nat>, over0, Some{0n}, None{})))

def Gt.show(a: Maybe<&2, Nat>) -> String:
  match a:
    case None{}:
      "."
    case Some{x}:
      Nat.show(x)

def Text.all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Char.is_digit(h) && Text.all_digits(t)

# An allele number as VCF writes it: one or more digits, without leading
# zeros ("0", "12"; not "", "01", "+1").
def Gt.canon(+a: String) -> Bool:
  Bool.not(String.is_empty(a)) && Text.all_digits(a) && (String.eq(a, "0") || Bool.not(String.starts_with(a, "0")))

def Gt.num(m: Maybe<&2, Nat>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
  match m:
    case None{}:
      Refuse{BadGt{}}
    case Some{+a}:
      Bool.pick(Got, Nat.is_le(a, n), Got{Gt.show(Gt.rule(over0, i, Some{a}))}, Refuse{BadGt{}})

# One allele of a genotype as written, in the record for ALT i of n: '.'
# stays '.'; a number from 0 to n written as Gt.canon says gives Gt.rule's
# allele. BAD_GT for anything else.
def Gt.allele(+over0: Bool, +n: Nat, +i: Nat, +a: String) -> Got:
  Bool.pick(Got, String.eq(a, "."), Got{"."},
    Bool.pick(Got, Gt.canon(a), Gt.num(Pos.read(a), over0, n, i), Refuse{BadGt{}}))

def Gt.is_sep(c: Char) -> Bool:
  +x = Char.code(c)
  U32.is_eq(x, 47) || U32.is_eq(x, 124)

# A genotype read from the right: the first allele's text, and the rest
# (from the first separator on) as written in the record for one ALT.
type Gp is Data:
  Gp{tok: String, rest: Got}

def Gt.go.put(sep: Bool, +h: Char, r: Gp, +over0: Bool, +n: Nat, +i: Nat) -> Gp:
  match sep r:
    case True{} Gp{tk, rs}:
      Gp{"", Got.cat(Got.cat(Got{SCon{h, SNil{}}}, "", Gt.allele(over0, n, i, tk)), "", rs)}
    case False{} Gp{tk, rs}:
      Gp{SCon{h, tk}, rs}

def Gt.go(s: String, +over0: Bool, +n: Nat, +i: Nat) -> Gp:
  match s:
    case SNil{}:
      Gp{"", Got{""}}
    case SCon{+h, t}:
      Gt.go.put(Gt.is_sep(h), h, Gt.go(t, over0, n, i), over0, n, i)

def Gt.split.of(r: Gp, +over0: Bool, +n: Nat, +i: Nat) -> Got:
  match r:
    case Gp{tk, rs}:
      Got.cat(Gt.allele(over0, n, i, tk), "", rs)

# A genotype (GT: alleles separated by '/', unphased, or '|', phased) in the
# record for ALT i of n: each allele as Gt.allele says, every separator kept.
# 1/2 becomes 1/0 for ALT 1 and 0/1 for ALT 2. (A leading separator, VCF
# 4.4's "|0|1", is an empty allele: BAD_GT; htslib 1.24 refuses it too.)
def Gt.split(+over0: Bool, +n: Nat, +i: Nat, g: String) -> Got:
  Gt.split.of(Gt.go(g, over0, n, i), over0, n, i)

def Gt.seps(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+h, t}:
      Nat.add(Bool.pick(Nat, Gt.is_sep(h), 1n, 0n), Gt.seps(t))

def Gt.copies.of(+g: String) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, String.eq(g, "."), None{}, Some{1n+Gt.seps(g)})

# How many chromosome copies a sample's G values are for, from its GT: the
# number of alleles GT names (one plus its separators: '1' and './.' are 1
# and 2); Some{2} when the sample has no GT value (VCF 4.3, section 1.6.2:
# without GT, G values are diploid); None for a lone '.' GT, written by many
# tools for a no-call of any ploidy: one or two copies, as the count says
# (Vals.copies).
def Gt.copies(m: Maybe<&2, String>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{2n}
    case Some{+g}:
      Gt.copies.of(g)

def Fmt.gt.put(hit: Bool, v: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

# A sample's GT value: its value under FORMAT's first GT key, if it has one.
def Fmt.gt(ks: List<&2, String>, vs: List<&2, String>) -> Maybe<&2, String>:
  match ks vs:
    case +k <> kt +v <> vt:
      Fmt.gt.put(String.eq(k, "GT"), v, Fmt.gt(kt, vt))
    case _ _:
      None{}

def Fmt.split.num(m: Maybe<&2, Num>, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> Got:
  match m:
    case None{}:
      Refuse{UndefinedTag{"FORMAT/" ++ k}}
    case Some{NumUnknown{}}:
      Refuse{UndefinedTag{"FORMAT/" ++ k}}
    case Some{NumOther{}}:
      Got{v}
    case Some{num}:
      Got.of(Vals.split(num, n, p, i, v), BadCount{})

def Fmt.split.one(+k: String, +v: String, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> Got:
  Bool.pick(Got, String.eq(k, "GT"), Gt.split(over0, n, i, v), Fmt.split.num(Tags.find(fmt, k), k, v, n, p, i))

def Fmt.split.go(ks: List<&2, String>, vs: List<&2, String>, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> List<&2, Got>:
  match ks vs:
    case _ Nil{}:
      Nil{}
    case Nil{} v <> t:
      [Refuse{BadCount{}}]
    case +k <> kt +v <> vt:
      Fmt.split.one(k, v, fmt, over0, n, p, i) <> Fmt.split.go(kt, vt, fmt, over0, n, p, i)

# One sample's column in the record for ALT i of n, read against the FORMAT
# keys ks, in order: GT by Gt.split (GT needs no header line); a key the
# header does not define, or defines with an Unknown Number, is
# UNDEFINED_TAG; Number Other is kept; A, R, G give the values of the
# record's alleles (Vals.split, for the sample's copies, Gt.copies). A
# column with fewer values than keys keeps its length; more values than keys
# is BAD_COUNT.
def Fmt.split(+ks: List<&2, String>, +col: String, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
  +vs = String.split(col, ':')
  Got.join(Fmt.split.go(ks, vs, fmt, over0, n, Gt.copies(Fmt.gt(ks, vs)), i), ":")

def Rec.piece.field(+j: Nat, +f: String, +a: String, +defs: Defs, +ks: List<&2, String>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
  Bool.pick(Got, Nat.is_eq(j, 4n), Got{a},
  Bool.pick(Got, Nat.is_eq(j, 7n), Info.split(f, Defs.info(defs), n, i),
  Bool.pick(Got, Nat.is_le(9n, j), Fmt.split(ks, f, Defs.fmt(defs), over0, n, i), Got{f})))

def Rec.piece.go(fs: List<&2, String>, +j: Nat, +a: String, +defs: Defs, +ks: List<&2, String>, +over0: Bool, +n: Nat, +i: Nat) -> List<&2, Got>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> t:
      Rec.piece.field(j, f, a, defs, ks, over0, n, i) <> Rec.piece.go(t, 1n+j, a, defs, ks, over0, n, i)

# The record for ALT i (1 to n; a, its text) of a record with fields fs and n
# ALTs: ALT is a alone; INFO and the samples are split (Info.split,
# Fmt.split); every other field (CHROM, POS, ID, REF, QUAL, FILTER, FORMAT)
# is kept.
def Rec.piece(+fs: List<&2, String>, +a: String, +defs: Defs, +over0: Bool, +n: Nat, +i: Nat) -> Got:
  Got.join(Rec.piece.go(fs, 0n, a, defs, String.split(Rec.field(fs, 8n), ':'), over0, n, i), "\t")

def Rec.pieces.go(alts: List<&2, String>, +fs: List<&2, String>, +defs: Defs, +over0: Bool, +n: Nat, +i: Nat) -> List<&2, Got>:
  match alts:
    case Nil{}:
      Nil{}
    case +a <> t:
      Rec.piece(fs, a, defs, over0, n, i) <> Rec.pieces.go(t, fs, defs, over0, n, 1n+i)

def Alts.member(+x: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> t:
      String.eq(x, String.to_upper(y)) || Alts.member(x, t)

# No two ALTs are equal, ignoring case.
def Alts.distinct(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> +t:
      Bool.not(Alts.member(String.to_upper(x), t)) && Alts.distinct(t)

# What -m does with one body line.
#   Whole: the line is one record, handled as without -m.
#   Pieces: one record per ALT, in ALT order (their texts).
#   Unsplit: the line cannot be split (ALT_DUP, written DupAlts here so its
#     message can add "not split"; UNDEFINED_TAG, BAD_COUNT or BAD_GT).
type Parts is Data:
  Whole{}
  Pieces{ps: List<&2, String>}
  Unsplit{c: Code}

def Parts.cons(g: Got, rest: Parts) -> Parts:
  match g rest:
    case Refuse{c} _:
      Unsplit{c}
    case Got{x} Pieces{ps}:
      Pieces{x <> ps}
    case Got{x} r:
      r

def Parts.of(gs: List<&2, Got>) -> Parts:
  match gs:
    case Nil{}:
      Pieces{Nil{}}
    case g <> t:
      Parts.cons(g, Parts.of(t))

def Rec.parts.split(ok: Bool, +alts: List<&2, String>, +fs: List<&2, String>, +defs: Defs, +over0: Bool) -> Parts:
  match ok:
    case False{}:
      Unsplit{DupAlts{}}
    case True{}:
      Parts.of(Rec.pieces.go(alts, fs, defs, over0, List.length(&2, String, alts), 1n))

def Rec.parts.if(go: Bool, +defs: Defs, +over0: Bool, +fs: List<&2, String>) -> Parts:
  match go:
    case False{}:
      Whole{}
    case True{}:
      +alts = Rec.alts(fs)
      Rec.parts.split(Alts.distinct(alts), alts, fs, defs, over0)

# What happens to a body line under the options o, given the header's
# definitions: with -m (split), a line that is not MALFORMED and has two or
# more ALTs is split into one record per ALT (Rec.piece), unless two of its
# ALTs are equal (ALT_DUP) or a record refuses (the first refusal, reading the
# records in ALT order and each left to right); any other line is Whole.
def Rec.parts(+defs: Defs, o: Opts, +body: String) -> Parts:
  match o:
    case Opts{s, w, split, over0, args}:
      +fs = Rec.fields(body)
      Rec.parts.if(split && Bool.not(Rec.malformed(fs)) && Nat.is_le(2n, List.length(&2, String, Rec.alts(fs))), defs, over0, fs)
