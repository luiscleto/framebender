import Base
import ./types.bend as B
import ./protocol.bend as P
import ./LAWS.bend as L

# The definitions of the former window laws (LAWS.bend before the two-layer
# spec), now used only by the implementation proof: proof_window.bend proves
# the lemmas window and window_enough about J.judge_in with them, and the
# machine proof uses those lemmas. An answer is a Maybe<&2, P.Ans>: None when
# nothing was read (the former NoAns).

def known.ok(m: Maybe<&2, String>, clen: Nat, +off: Nat, +raw: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+r}:
      Nat.is_eq(clen, String.length(r)) && String.eq(raw, String.take(String.drop(r, off), String.length(raw)))

# An answer that tells the truth about contig chrom: nothing; "unknown" when
# the reference has no such contig; or its real length and some of its real
# letters, as written in the FASTA file.
def truthful(+fa: List<&2, B.Contig>, +chrom: String, a: Maybe<&2, P.Ans>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{P.Unknown{}}:
      Maybe.is_none(&2, String, B.Fasta.find(fa, chrom))
    case Some{P.Known{clen, off, raw}}:
      known.ok(B.Fasta.find(fa, chrom), clen, off, raw)

def chrom_of(body: String) -> String:
  B.Rec.field(B.Rec.fields(body), 0n)

# The answer holds the letters lo .. hi - 1 (0-based), or up to the contig's
# end.
def covers(a: Maybe<&2, P.Ans>, +lo: Nat, +hi: Nat) -> Bool:
  match a:
    case Some{P.Known{+clen, +off, raw}}:
      Nat.is_le(off, lo) && Nat.is_le(Nat.min(hi, clen), Nat.add(off, String.length(raw)))
    case _:
      False{}

def is_known(a: Maybe<&2, P.Ans>) -> Bool:
  match a:
    case Some{P.Known{c, o, b}}:
      True{}
    case _:
      False{}

def is_unknown(a: Maybe<&2, P.Ans>) -> Bool:
  match a:
    case Some{P.Unknown{}}:
      True{}
    case _:
      False{}

def enough.go(r: B.Res, +p: Nat, +rlen: Nat, a: Maybe<&2, P.Ans>) -> Bool:
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      True{}
    case B.Res{B.Skipped{}, k, t, s}:
      True{}
    case B.Res{B.NoContig{}, k, t, s}:
      is_unknown(a)
    case B.Res{B.Problem{B.RefMismatch{}}, k, t, s}:
      covers(a, Nat.sub(p, 1n), Nat.add(Nat.sub(p, 1n), rlen))
    case B.Res{B.Problem{c}, k, t, s}:
      is_known(a)
    case B.Res{B.Normalized{}, +k, t, s}:
      covers(a, Nat.min(Nat.sub(p, 1n), Nat.sub(k, 2n)), Nat.add(Nat.sub(p, 1n), rlen))

# What the code needs to answer, by the line's outcome: MALFORMED and out of
# scope, nothing; UNKNOWN_CHROM, the answer "unknown"; BAD_END, NON_ACGTN,
# BAD_POS and ALT_DUP, that the contig exists; REF_MISMATCH, the input REF's
# letters (up to the contig's end); normalized, every letter from the input
# POS, or from one before the new POS (or the contig's first letter) when that
# is earlier, to the end of the input REF.
def enough(+fa: List<&2, B.Contig>, +body: String, a: Maybe<&2, P.Ans>) -> Bool:
  +fs = B.Rec.fields(body)
  enough.go(L.judge(fa, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), a)
