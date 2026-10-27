import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P

# Proofs: reading the reference through a window (Norm.judge_in, norm_line.bend).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it.

law window:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: B.Ans
  for +r: B.Res
  for +ht: {L.truthful(fa, L.chrom_of(body), a) == True{} : Bool}
  for +hr: {Norm.judge_in(a, body) == Some{r} : Maybe<&2, B.Res>}
  {r == L.judge(fa, body) : B.Res}

law window_enough:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: B.Ans
  for +ht: {L.truthful(fa, L.chrom_of(body), a) == True{} : Bool}
  for +he: {L.enough(fa, body, a) == True{} : Bool}
  {Maybe.is_some(&2, B.Res, Norm.judge_in(a, body)) == True{} : Bool}
