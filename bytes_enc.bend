import Base
import ../lawful-words/defs.bend as W
import ../lawful-bytes/defs.bend as D
import ./protocol.bend as P

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

def shape.same(+d: Nat, +e: Nat) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, Nat.is_eq(d, e), Some{Nat.add(d, 1n)}, None{})

def shape.depth(l: Maybe<&2, Nat>, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l r:
    case Some{d} Some{e}:
      shape.same(d, e)
    case _ _:
      None{}

# The depth of a perfect tree, with its words left to right; None for a tree
# that is not perfect.
def shape.join(l: Maybe<&2, Nat> & List<&2, U32>, r: Maybe<&2, Nat> & List<&2, U32>) -> Maybe<&2, Nat> & List<&2, U32>:
  (ld, lw) = l
  (rd, rw) = r
  (shape.depth(ld, rd), List.append(&2, U32, lw, rw))

def shape(a: Array<U32>) -> Maybe<&2, Nat> & List<&2, U32>:
  match a:
    case ALeaf{x}:
      (Some{0n}, [x])
    case ANode{xs, ys}:
      shape.join(shape(xs), shape(ys))

def out.if(ok: Bool, xs: List<&2, U32>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{chars(xs)}
    case False{}:
      None{}

def out.depth(m: Maybe<&2, Nat>, +len: U32, ws: List<&2, U32>) -> Maybe<&2, String>:
  match m:
    case Some{+d}:
      out.if(Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))), List.take(&2, U32, D.unpack(ws), U32.to_nat(len)))
    case None{}:
      None{}

def out.of(+len: U32, s: Maybe<&2, Nat> & List<&2, U32>) -> Maybe<&2, String>:
  (m, ws) = s
  out.depth(m, len, ws)

# The text an output buffer holds, if it is well formed: a perfect block of
# depth at most 29 holding len bytes (so the driver can write len bytes from
# its flat block). None otherwise.
def out(b: D.Bytes) -> Maybe<&2, String>:
  D.Bytes{+len, buf} = b
  out.of(len, shape(buf))

# Every character is a byte (code below 256): what the driver reads from a
# file, one Char per byte.
def is_bytes(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      U32.is_lt(Char.to_u32(c), 256) && is_bytes(t)

def all_bytes(ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      is_bytes(s) && all_bytes(t)

# n is at most 2^31, stated on words: n fits a U32 (it reads back as n) and
# that word is at most 2^31. The checker evaluates words natively, and
# lawful-words relates them to numbers; a big Nat constant (a literal or a
# Nat.pow) can only be compared with an identical term in a proof.
def le31(+n: Nat) -> Bool:
  Nat.is_eq(U32.to_nat(U32.from_nat(n)), n) && U32.is_le(U32.from_nat(n), 2147483648)

# Every piece has at most 2^31 bytes (what a buffer holds).
def pieces_ok(cs: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      le31(String.length(c)) && pieces_ok(t)

# The inputs a packed driver can hand over: the command line, the FASTA and
# every VCF piece are bytes, and every piece fits a buffer.
def texts_ok(argv: List<&2, String>, fasta: String, +cs: List<&2, String>) -> Bool:
  all_bytes(argv) && (is_bytes(fasta) && (all_bytes(cs) && pieces_ok(cs)))

# Every reference read asks for at most 2^31 letters (what a buffer holds).
def reqs_ok(rs: List<&2, P.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{P.Req{c, a, b}, t}:
      Nat.is_le(Nat.sub(b, a), 2147483648n) && reqs_ok(t)
