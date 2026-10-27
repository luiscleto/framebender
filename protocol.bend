import Base
import ./types.bend as B

# framebender: the protocol between the program and its driver
# (implementation layer, used by MACHINE.bend; not part of the science laws).

# What the tool learns from one read of the reference.
#   Unknown: the contig is not in the reference.
#   Known: the contig has clen letters; raw holds its letters as written
#     (Contig.raw) from 0-based index off: all of them, or a window.
type Ans is Data:
  Unknown{}
  Known{clen: Nat, off: Nat, raw: String}

# A reference read: the letters of contig chrom from 0-based index from up to
# (not including) upto.
type Req is Data:
  Req{chrom: String, from: Nat, upto: Nat}

# What the machine is given at each step: the next piece of the VCF file, the
# end of the file, or the answers to its last reference reads (in order).
type In is Data:
  Chunk{s: String}
  Eof{}
  Ref{ans: List<&2, Ans>}

# What the machine wants next: more of the VCF file; any number of reference
# reads, all answered at once; or to stop with an exit code.
type Next is Data:
  More{}
  Ask{reqs: List<&2, Req>}
  Finish{code: Nat}

# A FASTA file that samtools faidx indexes and serves exactly as
# B.Fasta.parse reads it:
# - the file starts with a header line ('>'), or is empty;
# - no header line holds a vertical tab or form feed (samtools ends a name at
#   any whitespace, B.Fasta.name only at space, tab or CR);
# - in every contig (also the ones B.Fasta.parse ignores, which samtools still
#   reads), each sequence line is bytes 0x21-0x7E, then optionally one CR, the
#   same for all its non-empty lines; all lines have the same length except that the
#   last ones may be shorter or empty, with no letters after them;
# - every contig B.Fasta.parse keeps has at least one letter (samtools leaves
#   a contig without letters out of the index).
# The program's law covers only such files.

def Fasta.graph(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, t}:
      U32.is_ge(x, 33) && U32.is_le(x, 126) && Fasta.graph(t)

# A header line holds a vertical tab or form feed.
def Fasta.vtff(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+x}, t}:
      U32.is_eq(x, 11) || U32.is_eq(x, 12) || Fasta.vtff(t)

# The state while reading a contig's lines: the length of its first line (0
# before one), whether a shorter or empty line ended its letters, whether its
# lines end in CR (0: not known yet, 1: no, 2: yes), its letters so far, and
# whether B.Fasta.parse keeps it.
type Lay is Data:
  Lay{width: Nat, ended: Bool, cr: Nat, letters: Nat, kept: Bool}

# The verdict so far: the names seen, the contig being read (None before the
# first header), and whether the file is still fine.
type Plain is Data:
  Plain{seen: List<&2, String>, cur: Maybe<&2, Lay>, ok: Bool}

# A contig ends: a kept contig needs a letter.
def Fasta.close(m: Maybe<&2, Lay>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Lay{w, e, c, n, k}}:
      Bool.not(k) || Nat.is_lt(0n, n)

def Fasta.cr_ok(+cr: Nat, +has: Bool) -> Bool:
  Nat.is_eq(cr, 0n) || Nat.is_eq(cr, Bool.pick(Nat, has, 2n, 1n))

def Fasta.seq_line.go(ok: Bool, l: Lay) -> Maybe<&2, Lay>:
  match ok:
    case True{}:
      Some{l}
    case False{}:
      None{}

# One sequence line of a contig, without its CR if has: a line of length len.
def Fasta.seq_line(l: Lay, +len: Nat, +has: Bool, good: Bool) -> Maybe<&2, Lay>:
  match l:
    case Lay{+w, +e, +cr, n, k}:
      +blank = Nat.is_eq(len, 0n)
      Fasta.seq_line.go(good && (blank || (Fasta.cr_ok(cr, has) && Bool.not(e) && (Nat.is_eq(w, 0n) || Nat.is_le(len, w)))),
        Lay{Bool.pick(Nat, Nat.is_eq(w, 0n), len, w), e || blank || (Bool.not(Nat.is_eq(w, 0n)) && Nat.is_lt(len, w)), Bool.pick(Nat, blank, cr, Bool.pick(Nat, has, 2n, 1n)), Nat.add(n, len), k})

def Fasta.chomp.if(cr: Bool, +l: String) -> String:
  match cr:
    case True{}:
      String.take(l, Nat.sub(String.length(l), 1n))
    case False{}:
      l

def Fasta.after_line(m: Maybe<&2, Lay>, +seen: List<&2, String>) -> Plain:
  match m:
    case None{}:
      Plain{seen, None{}, False{}}
    case Some{lay}:
      Plain{seen, Some{lay}, True{}}

def Fasta.after_line.k(ok: Bool, m: Maybe<&2, Lay>, +seen: List<&2, String>) -> Plain:
  match ok:
    case False{}:
      Plain{seen, None{}, False{}}
    case True{}:
      Fasta.after_line(m, seen)

def Fasta.line.k(head: Bool, cur: Maybe<&2, Lay>, +l: String, +seen: List<&2, String>, +ok: Bool) -> Plain:
  match head cur:
    case True{} c:
      +n = B.Fasta.name(l)
      +keep = Bool.not(String.is_empty(n)) && Bool.not(B.Fasta.seen(n, seen))
      Plain{Bool.pick(List<&2, String>, keep, n <> seen, seen), Some{Lay{0n, False{}, 0n, 0n, keep}}, ok && Fasta.close(c) && Bool.not(Fasta.vtff(l))}
    case False{} None{}:
      Plain{seen, None{}, ok && String.is_empty(l)}
    case False{} Some{lay}:
      +has = String.ends_with(l, "\r")
      +body = Fasta.chomp.if(has, l)
      Fasta.after_line.k(ok, Fasta.seq_line(lay, String.length(body), has, Fasta.graph(body)), seen)

def Fasta.line(p: Plain, +head: Bool, +l: String) -> Plain:
  match p:
    case Plain{seen, cur, ok}:
      Fasta.line.k(head, cur, l, seen, ok)

def Fasta.plain.go(ls: List<&2, String>, p: Plain) -> Plain:
  match ls:
    case Nil{}:
      p
    case +l <> t:
      Fasta.plain.go(t, Fasta.line(p, B.Fasta.is_head(l), l))

def Fasta.plain.end(p: Plain) -> Bool:
  match p:
    case Plain{s, c, ok}:
      ok && Fasta.close(c)

def Fasta.plain(text: String) -> Bool:
  Fasta.plain.end(Fasta.plain.go(String.split(text, '\n'), Plain{Nil{}, None{}, True{}}))
