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

# A FASTA file the .fai index can serve. Only the contigs B.Fasta.parse keeps
# count (text before the first header, and a header with an empty or repeated
# name with its lines, are ignored there too); each must have at least one
# letter (samtools faidx leaves a contig without letters out of the index), and
# its lines must hold no space or tab and no CR except at the end of a line
# (the index cannot skip them). The program's law covers only such files.
# A line (without its LF) holds a space or tab, or a CR before its end.
def Fasta.blank(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+x}, +t}:
      U32.is_eq(x, 32) || U32.is_eq(x, 9) || (U32.is_eq(x, 13) && Bool.not(String.is_empty(t))) || Fasta.blank(t)

def Fasta.blank_seq.put(head: Bool, +l: String, rest: Bool) -> Bool:
  match head:
    case True{}:
      False{}
    case False{}:
      Fasta.blank(l) || rest

# Some line up to the next header line holds a blank.
def Fasta.blank_seq(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> t:
      Fasta.blank_seq.put(B.Fasta.is_head(l), l, Fasta.blank_seq(t))

# One header's contig: its name, and whether it is unusable (its lines hold a
# blank, or it has no letters).
type Flag is Data:
  Flag{name: String, blank: Bool}

def Fasta.flags.put(head: Bool, +l: String, +t: List<&2, String>, rest: List<&2, Flag>) -> List<&2, Flag>:
  match head:
    case True{}:
      Flag{B.Fasta.name(l), Fasta.blank_seq(t) || String.is_empty(B.Fasta.seq(t))} <> rest
    case False{}:
      rest

def Fasta.flags(ls: List<&2, String>) -> List<&2, Flag>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +t:
      Fasta.flags.put(B.Fasta.is_head(l), l, t, Fasta.flags(t))

def Fasta.kept_blank.put(skip: Bool, +n: String, b: Bool, +seen: List<&2, String>, rest: Bool) -> Bool:
  match skip:
    case True{}:
      rest
    case False{}:
      b || rest

# Some contig kept by B.Fasta.parse (the first of its name, a non-empty name)
# is unusable.
def Fasta.kept_blank(fs: List<&2, Flag>, +seen: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Flag{+n, b} <> t:
      +skip = String.is_empty(n) || B.Fasta.seen(n, seen)
      Fasta.kept_blank.put(skip, n, b, seen, Fasta.kept_blank(t, Bool.pick(List<&2, String>, skip, seen, n <> seen)))

def Fasta.plain(text: String) -> Bool:
  Bool.not(Fasta.kept_blank(Fasta.flags(String.split(text, '\n')), Nil{}))
