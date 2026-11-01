import Base
import ../bytes_enc.bend as E
import lawful-bytes@0.1.1.0/defs.bend as D

# text(enc(s)) == s on a few texts, and the block depth.
def main() -> List<Bool>:
  [ String.eq(E.text(E.enc("")), "")
  , String.eq(E.text(E.enc("a")), "a")
  , String.eq(E.text(E.enc("abcd")), "abcd")
  , String.eq(E.text(E.enc("abcde")), "abcde")
  , String.eq(E.text(E.enc("chr1\t123\t.\tAC\tA\n")), "chr1\t123\t.\tAC\tA\n")
  , Nat.is_eq(E.depth(0n), 0n)
  , Nat.is_eq(E.depth(4n), 0n)
  , Nat.is_eq(E.depth(5n), 1n)
  , Nat.is_eq(E.depth(17n), 3n)
  , D.ok(E.enc("chr1\t123\t.\tAC\tA\n"), 2n)
    , Bool.not(E.is_bytes(SCon{Chr{256}, ""}))
  , E.is_bytes("ab\r\n")
  , E.texts_ok(["norm", "-f"], ">c\nA\n", ["ab", "cd"])
  , String.eq(Maybe.default(&2, String, E.out(E.enc("abcde")), "x"), "abcde")
  , Maybe.is_none(&2, String, E.out(D.Bytes{8, ALeaf{0}}))
  , Maybe.is_none(&2, String, E.out(D.Bytes{1, ANode{ALeaf{0}, ANode{ALeaf{0}, ALeaf{0}}}}))
  ]
