import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./norm_fast.bend as NF
import lawful-bytes@0.1.1.0/bytes.bend as BY
import ./proof_b_defs.bend as P

# The machine's reference cache (norm.bend: Win, win_of, serve, parts,
# Req.of, against). A window built from truthful answers is fixed by the
# contig and the bounds read (WP); mkWin builds it. Its answers are truthful,
# the reads it asks are within 2^31 letters, and the fast path's REF test
# means the String path's REF check passes.

# A window's picture: nothing; contig c unknown; contig c's letters read from
# a up to b in one read (Known) or in parts (Str).
type WP is Data:
  WPNone{}
  WPUnk{c: String}
  WPKnown{c: String, a: Nat, b: Nat}
  WPStr{c: String, a: Nat, b: Nat}

# The letters of a contig from a up to b (cut at its end), as truth gives them.
def letters(+r: String, +a: Nat, +b: Nat) -> String:
  String.take(String.drop(r, a), Nat.sub(b, a))

def mkWin.k(m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +str: Bool) -> Norm.Win:
  match m str:
    case None{} _:
      Norm.WNone{}
    case Some{+r} False{}:
      Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(letters(r, a, b))))
    case Some{+r} True{}:
      Norm.WStr{c, a, b, String.length(r), Nat.min(a, String.length(r)), letters(r, a, b)}

# The window a picture stands for, given the reference.
def mkWin(+fa: List<&2, B.Contig>, +wp: WP) -> Norm.Win:
  match wp:
    case WPNone{}:
      Norm.WNone{}
    case WPUnk{c}:
      Norm.WUnk{c}
    case WPKnown{+c, +a, +b}:
      mkWin.k(B.Fasta.find(fa, c), c, a, b, False{})
    case WPStr{+c, +a, +b}:
      mkWin.k(B.Fasta.find(fa, c), c, a, b, True{})

# The window the answers to Norm.parts(c, a, b) give: Unknown, one read, or
# parts.
def wpOf.k(m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat) -> WP:
  match m:
    case None{}:
      WPUnk{c}
    case Some{r}:
      Bool.pick(WP, Norm.le31(Nat.sub(b, a)), WPKnown{c, a, b}, WPStr{c, a, b})

def wpOf(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat) -> WP:
  wpOf.k(B.Fasta.find(fa, c), c, a, b)

# The truthful answer to "contig c from a up to b", as text (MACHINE.bend's
# truth, decoded).
def jtruth.k(m: Maybe<&2, String>, +a: Nat, +b: Nat) -> J.Ans:
  match m:
    case None{}:
      J.Unknown{}
    case Some{+r}:
      J.Known{String.length(r), Nat.min(a, String.length(r)), letters(r, a, b)}

def jtruth(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat) -> J.Ans:
  jtruth.k(B.Fasta.find(fa, c), a, b)

def wp.clen.k(m: Maybe<&2, String>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{+r}:
      String.length(r)

def wp.clen(+fa: List<&2, B.Contig>, +c: String) -> Nat:
  wp.clen.k(B.Fasta.find(fa, c))

# The window the slow path asks for the read a .. e (Norm.Req.of): from
# margin() letters earlier up to ahead() letters on, in one read; if that is
# more than one read holds, a .. e itself.
def wpReq(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +e: Nat) -> WP:
  Bool.pick(WP, Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))), wpOf(fa, c, Nat.sub(a, Norm.margin()), Nat.max(e, Nat.add(a, Norm.ahead()))), wpOf(fa, c, a, e))

# A picture the machine can have: an unknown contig is not in the reference;
# a window read at once has at most 2^31 letters.
def wp_ok(+fa: List<&2, B.Contig>, +wp: WP) -> Bool:
  match wp:
    case WPUnk{+c}:
      Maybe.is_none(&2, String, B.Fasta.find(fa, c))
    case WPKnown{c, +a, +b}:
      P.le31(Nat.sub(b, a))
    case _:
      True{}

# serve's test: the window holds the read (serve's own expression).
def holds(+fa: List<&2, B.Contig>, +wp: WP, +c: String, +a: Nat, +b: Nat) -> Bool:
  match wp:
    case WPNone{}:
      False{}
    case WPUnk{+c0}:
      String.eq(c0, c)
    case WPKnown{+c0, +a0, +b0}:
      Maybe.is_some(&2, String, B.Fasta.find(fa, c0)) && (String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, wp.clen(fa, c0)), Nat.min(b0, wp.clen(fa, c0))))
    case WPStr{+c0, +a0, +b0}:
      Maybe.is_some(&2, String, B.Fasta.find(fa, c0)) && (String.eq(c0, c) && Nat.is_le(a0, a) && Nat.is_le(Nat.min(b, wp.clen(fa, c0)), Nat.min(b0, wp.clen(fa, c0))))

# Every byte is an upper-case A, C, G, T or N (as proof_b_alleles.bend's up).
def up(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      NF.is_base(x) && up(t)

# The bases of upper-case letter bytes (as proof_b_alleles.bend's bases_of).
def lb(+x: U32) -> B.Base:
  Maybe.default(&2, B.Base, B.Base.of_letter(Chr{x}), B.N{})

def bases_of(xs: List<&2, U32>) -> List<&2, B.Base>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      lb(x) <> bases_of(t)

# Every contig's letters are bytes (the FASTA file is, E.texts_ok).
def fa_bytes(fa: List<&2, B.Contig>) -> Bool:
  match fa:
    case Nil{}:
      True{}
    case Con{B.Contig{nm, r}, t}:
      E.is_bytes(r) && fa_bytes(t)
