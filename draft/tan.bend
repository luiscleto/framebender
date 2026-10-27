import Base
import ./types.bend as B

# framebender: the reference normalizer (spec). Tan, Abecasis and Kang 2015,
# Algorithm 1, on all alleles at once: while every allele ends with the same
# base, drop that base (when an allele would become empty, first take the base
# before the variant as a new first base of every allele, moving one position
# left; never before position 1); then, while every allele starts with the same
# base and all have at least two bases, drop that first base (moving one
# position right). An expert need not read it: LAWS.bend's laws same_change,
# stays_valid, standard_form and unique fix its result (the one valid,
# normalized variant making the same change). It reads the contig through a
# window (var_in, with a step budget) only so that implementations can reuse
# its proofs; the spec uses the whole contig (normal).

# ---------------------------------------------------------------------------
# Reading the reference through a window
# ---------------------------------------------------------------------------

def Win.get.if(below: Bool, bases: List<&2, B.Base>, off: Nat, i: Nat) -> Maybe<&2, B.Base>:
  match below:
    case True{}:
      None{}
    case False{}:
      List.get(&2, B.Base, bases, Nat.sub(i, off))

# The base at 0-based contig index i, or None when the window does not hold it.
def Win.get(+off: Nat, bases: List<&2, B.Base>, +i: Nat) -> Maybe<&2, B.Base>:
  Win.get.if(Nat.is_lt(i, off), bases, off, i)

# ---------------------------------------------------------------------------
# Tan et al.'s algorithm on all alleles at once (REF first, then the ALTs):
# trim or shift from the right, then trim the left
# ---------------------------------------------------------------------------

type Act is Data:
  AStop{}
  ATrim{}
  AShift{b: B.Base}
  ANeed{}

# Alleles REF, ALT1, ALT2, ... being normalized, at position pos.
type Cur is Data:
  Cur{pos: Nat, als: List<&2, List<&2, B.Base>>}

def opt_eq(a: Maybe<&2, B.Base>, b: Maybe<&2, B.Base>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      B.Base.is_eq(x, y)
    case _ _:
      False{}

def same_last(+x: Maybe<&2, B.Base>, als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      opt_eq(x, List.last(&2, B.Base, a)) && same_last(x, t)

# Every allele ends with the same base.
def lasts_eq(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      False{}
    case a <> t:
      same_last(List.last(&2, B.Base, a), t)

def same_first(+x: Maybe<&2, B.Base>, als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      opt_eq(x, List.head(&2, B.Base, a)) && same_first(x, t)

# Every allele starts with the same base.
def firsts_eq(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      False{}
    case a <> t:
      same_first(List.head(&2, B.Base, a), t)

# Every allele has at least two bases.
def all_long(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      Nat.is_le(2n, List.length(&2, B.Base, a)) && all_long(t)

def init(+xs: List<&2, B.Base>) -> List<&2, B.Base>:
  List.take(&2, B.Base, xs, Nat.sub(List.length(&2, B.Base, xs), 1n))

def inits(als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      init(a) <> inits(t)

def tails(als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      List.tail(&2, B.Base, a) <> tails(t)

# b put in front of every allele, which loses its last base.
def shifted(+b: B.Base, als: List<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
  match als:
    case Nil{}:
      Nil{}
    case a <> t:
      {b <> init(a) : List<&2, B.Base>} <> shifted(b, t)

def next_act.if(eq: Bool, long: Bool, shift: Bool, b: Maybe<&2, B.Base>) -> Act:
  match eq:
    case False{}:
      AStop{}
    case True{}:
      match long:
        case True{}:
          ATrim{}
        case False{}:
          match shift:
            case False{}:
              AStop{}
            case True{}:
              match b:
                case None{}:
                  ANeed{}
                case Some{x}:
                  AShift{x}

# The next step: when the alleles all end with the same base, trim it if every
# allele is long enough, else move one base left (taking the base before pos
# as the new first base) unless pos is 1. Need: that base is outside the window.
def next_act(+off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Act:
  next_act.if(lasts_eq(als), all_long(als), Nat.is_le(2n, pos), Win.get(off, bases, Nat.sub(pos, 2n)))

def right(fuel: Nat, act: Act, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Maybe<&2, Cur>:
  match fuel:
    case 0n:
      Some{Cur{pos, als}}
    case 1n+f:
      match act:
        case AStop{}:
          Some{Cur{pos, als}}
        case ANeed{}:
          None{}
        case ATrim{}:
          +a = inits(als)
          right(f, next_act(off, bases, pos, a), off, bases, pos, a)
        case AShift{+b}:
          +p = Nat.sub(pos, 1n)
          +a = shifted(b, als)
          right(f, next_act(off, bases, p, a), off, bases, p, a)

def left(fuel: Nat, go: Bool, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> Cur:
  match fuel:
    case 0n:
      Cur{pos, als}
    case 1n+f:
      match go:
        case False{}:
          Cur{pos, als}
        case True{}:
          +a = tails(als)
          left(f, firsts_eq(a) && all_long(a), 1n+pos, a)

def to_var(c: Cur) -> B.Var:
  match c:
    case Cur{p, r <> t}:
      B.Var{p, r, t}
    case Cur{p, Nil{}}:
      B.Var{p, Nil{}, Nil{}}

def total(als: List<&2, List<&2, B.Base>>) -> Nat:
  match als:
    case Nil{}:
      0n
    case a <> t:
      Nat.add(List.length(&2, B.Base, a), total(t))

def left_of(m: Maybe<&2, Cur>) -> Maybe<&2, B.Var>:
  match m:
    case None{}:
      None{}
    case Some{Cur{+p, +a}}:
      Some{to_var(left(Nat.add(p, total(a)), firsts_eq(a) && all_long(a), p, a))}

# The normalized variant, or None when the window is too small to tell.
def var_in(+off: Nat, +bases: List<&2, B.Base>, v: B.Var) -> Maybe<&2, B.Var>:
  match v:
    case B.Var{+pos, ref, alts}:
      +als = {ref <> alts : List<&2, List<&2, B.Base>>}
      fuel = Nat.add(pos, total(als))
      left_of(right(fuel, next_act(off, bases, pos, als), off, bases, pos, als))

# The normal form of v on contig seq.
def normal(+seq: List<&2, B.Base>, +v: B.Var) -> B.Var:
  Maybe.default(&2, B.Var, var_in(0n, seq, v), v)
