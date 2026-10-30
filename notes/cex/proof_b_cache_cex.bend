import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import lawful-bytes@0.1.0.0/bytes.bend as BY

# A counterexample to proof_b_cache.bend's against_hit as stated: POS is
# 2^32 - 1, so the fast path's end (POS - 1 + rl, a U32) wraps to 1, and
# refeq reads the window's bytes at indices that wrap around its block.
# Contig chr1 = ACGT, window 0 .. 4, the line's bytes "chr1GTA": CHROM 0 .. 4,
# REF "GTA" (3 bytes from 4).

# proof_b_cache.bend's mkWin(fa, WPKnown{c, a, b}) when fa holds contig c
# with letters r (mkWin.k), and bases_of (copied: importing that file would
# import its open TODOs).
def letters(+r: String, +a: Nat, +b: Nat) -> String:
  String.take(String.drop(r, a), Nat.sub(b, a))

def known(+c: String, +r: String, +a: Nat, +b: Nat) -> Norm.Win:
  Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(letters(r, a, b))))

def lb(+x: U32) -> B.Base:
  Maybe.default(&2, B.Base, B.Base.of_letter(Chr{x}), B.N{})

def bases_of(xs: List<&2, U32>) -> List<&2, B.Base>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      lb(x) <> bases_of(t)

def wr(o: Norm.Wo) -> Norm.Wr:
  match o:
    case Norm.Wo{w, b, r}:
      r

# The fast path's verdict: WHit.
def hit() -> Norm.Wr:
  wr(Norm.against(known("chr1", "ACGT", 0n, 4n), E.enc("chr1GTA"), 0, 4, 4294967295, 4, 3))

# The String path's REF check on the same record: Some(False) (REF runs past
# the contig's end).
def check() -> Maybe<&2, Bool>:
  J.ref_check(4n, 0n, B.Bases.of_fasta("ACGT"), Nat.sub(U32.to_nat(4294967295), 1n), bases_of(E.codes("GTA")))

def main() -> Norm.Wr & Maybe<&2, Bool>:
  (hit(), check())
