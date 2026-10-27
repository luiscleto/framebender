import Base
import ../lawful-words/defs.bend as W
import ../lawful-bytes/defs.bend as D

# framebender: text as packed bytes (implementation layer, used by
# protocol.bend and MACHINE.bend). The driver hands the program the VCF pieces
# and reference answers as packed buffers in one canonical encoding, enc; the
# program's output buffers mean the text they decode to, text.

# The byte value of each character (one Char per byte, codes 0-255, as the
# driver reads files).
def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), codes(t)}

def chars(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, t}:
      SCon{Chr{x}, chars(t)}

# The text a buffer holds: one character per byte.
def text(b: D.Bytes) -> String:
  chars(D.view(b))

# Bytes packed four to a word, little-endian; the last word zero-padded.
def words(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b0, Nil{}}:
      [W.pack4(b0, 0, 0, 0)]
    case Con{b0, Con{b1, Nil{}}}:
      [W.pack4(b0, b1, 0, 0)]
    case Con{b0, Con{b1, Con{b2, Nil{}}}}:
      [W.pack4(b0, b1, b2, 0)]
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      Con{W.pack4(b0, b1, b2, b3), words(t)}

def depth.go(fuel: Nat, +d: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      Bool.pick(Nat, Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))), d, depth.go(f, Nat.add(d, 1n), n))

# The smallest depth whose block holds n bytes (4 * 2^d >= n).
def depth(+n: Nat) -> Nat:
  depth.go(Nat.add(n, 1n), 0n, n)

# A perfect tree of depth d holding ws from the left, zero-padded.
def tree(+d: Nat, +ws: List<&2, U32>) -> Array<U32>:
  match d:
    case 0n:
      ALeaf{Maybe.default(&2, U32, List.get(&2, U32, ws, 0n), 0)}
    case 1n+p:
      ANode{tree(p, List.take(&2, U32, ws, Nat.pow(2n, p))), tree(p, List.drop(&2, U32, ws, Nat.pow(2n, p)))}

# The canonical buffer for a text: its bytes packed four to a word, little-
# endian, zero-padded, in the smallest block that holds them. The driver
# builds exactly this value for each VCF piece and each reference answer.
def enc(+s: String) -> D.Bytes:
  +n = String.length(s)
  D.Bytes{U32.from_nat(n), tree(depth(n), words(codes(s)))}
