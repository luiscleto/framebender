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

# A FASTA file whose sequence lines (every line not starting with '>') hold no
# space or tab. The driver reads the reference through the .fai index, which
# cannot skip them, so the program's law covers only such files.
def Fasta.blank(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+x}, t}:
      U32.is_eq(x, 32) || U32.is_eq(x, 9) || Fasta.blank(t)

def Fasta.plain.go(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      (B.Fasta.is_head(l) || Bool.not(Fasta.blank(l))) && Fasta.plain.go(t)

def Fasta.plain(text: String) -> Bool:
  Fasta.plain.go(String.split(text, '\n'))
