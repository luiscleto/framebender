import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./bytes_enc.bend as E
import lawful-bytes@0.1.0.0/bytes.bend as BY

# A counterexample to proof_b_cache.bend's against_hit (second conjunct) as
# stated: the window's contig name c has a character past 255 (nothing says
# c is bytes). NR.of_str stores its low byte, so a line whose CHROM is that
# byte passes the CHROM test; the hit's CHROM text is then not c.
# Contig c = [256] with letters "A", window 0 .. 1; the line's bytes [0, 'A']:
# CHROM 0 .. 1, REF "A" (1 byte from 1), POS 1.

def letters(+r: String, +a: Nat, +b: Nat) -> String:
  String.take(String.drop(r, a), Nat.sub(b, a))

def known(+c: String, +r: String, +a: Nat, +b: Nat) -> Norm.Win:
  Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(letters(r, a, b))))

def wr(o: Norm.Wo) -> Norm.Wr:
  match o:
    case Norm.Wo{w, b, r}:
      r

def cname() -> String:
  SCon{Chr{256}, SNil{}}

def line() -> String:
  SCon{Chr{0}, SCon{Chr{65}, SNil{}}}

# The fast path's verdict (WHit) and the hit's CHROM text ("\0", not c).
def main() -> Norm.Wr & (String & Bool):
  (wr(Norm.against(known(cname(), "A", 0n, 1n), E.enc(line()), 0, 1, 1, 1, 1)), (Norm.text_of(E.enc(String.take(line(), 1n))), String.eq(String.take(line(), 1n), cname())))
