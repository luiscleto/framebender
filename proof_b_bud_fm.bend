import Base
import ./types.bend as B
import ./proof_b_budget_need.bend as BN
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# A contig B.Fasta.find returns is no longer than BN.FM, the longest
# contig's length (for the budget, proof_b_budget_need.bend).

def le_max_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      N.le_zero_l(b)
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      le_max_l(p, q)

def le_max_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      N.le_refl(b)
    case 1n+p 0n:
      N.le_zero_l(1n+p)
    case 1n+p 1n+q:
      le_max_r(p, q)

def unsome(+d: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def is_sm(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def fm_put(+b: Bool, +rr: String, +rest: Maybe<&2, String>, +r: String, +m: Nat,
  +h: {B.Fasta.find.put(b, rr, rest) == Some{r} : Maybe<&2, String>},
  ih: @h2: {rest == Some{r} : Maybe<&2, String>} -> {Nat.is_le(String.length(r), m) == True{} : Bool}) ->
  {Nat.is_le(String.length(r), Nat.max(String.length(rr), m)) == True{} : Bool}:
  match b:
    case True{}:
      +e = Equal.cong(Maybe<&2, String>, String, z => unsome("", z), Some{rr}, Some{r}, h)
      AB.subst(String, z => {Nat.is_le(String.length(z), Nat.max(String.length(rr), m)) == True{} : Bool}, rr, r, e, le_max_l(String.length(rr), m))
    case False{}:
      N.le_trans(String.length(r), m, Nat.max(String.length(rr), m), ih(h), le_max_r(String.length(rr), m))

# The lemma.
def find_fm(+fa: List<&2, B.Contig>, +c: String, +r: String,
  +h: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>}) ->
  {Nat.is_le(String.length(r), BN.FM(fa)) == True{} : Bool}:
  match fa:
    case Nil{}:
      Empty.absurd({Nat.is_le(String.length(r), 0n) == True{} : Bool},
        AB.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, z => is_sm(z), None{}, Some{r}, h)))
    case Con{B.Contig{+n, +rr}, +t}:
      fm_put(String.eq(n, c), rr, B.Fasta.find(t, c), r, BN.FM(t), h, h2 => find_fm(t, c, r, h2))
