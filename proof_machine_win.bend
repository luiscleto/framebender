import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./proof_window_defs.bend as WS
import ./norm.bend as Norm
import ./LAWS.bend as L
import ./proof_window.bend as PW

# The window lemmas (proof_window.bend), as the machine proof uses them: the
# same statements as PW.window and PW.window_enough.

law window:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +r: B.Res
  for +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool}
  for +hr: {Norm.judge_in(a, body) == Some{r} : Maybe<&2, B.Res>}
  {r == L.judge(fa, body) : B.Res}

def window(fa, body, a, r, ht, hr):
  PW.window(fa, body, a, r, ht, hr)

law window_enough:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool}
  for +he: {WS.enough(fa, body, a) == True{} : Bool}
  {Maybe.is_some(&2, B.Res, Norm.judge_in(a, body)) == True{} : Bool}

def window_enough(fa, body, a, ht, he):
  PW.window_enough(fa, body, a, ht, he)
