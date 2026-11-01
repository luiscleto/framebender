import Base
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_find.bend as FD
import lawful-bytes@0.1.1.0/proof_append.bend as PA
import lawful-bytes@0.1.1.0/proof_fast_append.bend as FA
import lawful-bytes@0.1.1.0/proof_shift.bend as SH
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# List facts for the lines area: a buffer's bytes up to and after its first
# LF (byte 10), as D.first and D.run_len give it.

# A list is its first n then the rest.
def take_drop(+xs: List<&2, U32>, +n: Nat) ->
  {xs == List.append(&2, U32, List.take(&2, U32, xs, n), List.drop(&2, U32, xs, n)) : List<&2, U32>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %Equal.sym(List<&2, U32>, t, List.append(&2, U32, List.take(&2, U32, t, p), List.drop(&2, U32, t, p)), take_drop(t, p)) :
        {Con{x, _} == Con{x, List.append(&2, U32, List.take(&2, U32, t, p), List.drop(&2, U32, t, p))} : List<&2, U32>}
      {==}

# A Some found by is_some is the value itself.
def has_get(+m: Maybe<&2, U32>, +c: U32, +h: {D.is_some(m, c) == True{} : Bool}) ->
  {m == Some{c} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{c} : Maybe<&2, U32>}, AB.false_ne_true(h))
    case Some{+x}:
      %U.is_eq_true(x, c, h) : {Some{x} == Some{_} : Maybe<&2, U32>}
      {==}

# Element k, then the rest after it.
def drop_get(+xs: List<&2, U32>, +k: Nat, +v: U32, +hg: {List.get(&2, U32, xs, k) == Some{v} : Maybe<&2, U32>}) ->
  {List.drop(&2, U32, xs, k) == Con{v, List.drop(&2, U32, xs, Nat.add(k, 1n))} : List<&2, U32>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({Nil{} == Con{v, Nil{}} : List<&2, U32>}, FD.none_ne_some(v, hg))
    case Con{+x, +t} 0n:
      %PA.some_inj(x, v, hg) : {Con{x, t} == Con{_, List.drop(&2, U32, t, 0n)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, FD.drop_zero(t)) : {Con{x, t} == Con{x, _} : List<&2, U32>}
      {==}
    case Con{+x, +t} 1n+p:
      drop_get(t, p, v, hg)

def all_bytes_drop(+xs: List<&2, U32>, +n: Nat, +h: {D.all_bytes(xs) == True{} : Bool}) ->
  {D.all_bytes(List.drop(&2, U32, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      h
    case Con{+x, +t} 1n+p:
      all_bytes_drop(t, p, AB.and_true_r(U32.is_lt(x, 256), D.all_bytes(t), h))

# The bytes before the first LF hold no LF.
def rl_nolf.k(+x: U32, +t: List<&2, U32>, +b: Bool, +eb: {U32.is_eq(x, 10) == b : Bool},
  +ih: {P.nolf(NR.chars(List.take(&2, U32, t, D.run_len(t, 10)))) == True{} : Bool}) ->
  {P.nolf(NR.chars(List.take(&2, U32, Con{x, t}, D.run_len(Con{x, t}, 10)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(x, 10), True{}, eb) :
        {P.nolf(NR.chars(List.take(&2, U32, Con{x, t}, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, 10)))))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(x, 10), False{}, eb) :
        {P.nolf(NR.chars(List.take(&2, U32, Con{x, t}, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, 10)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(x, 10), False{}, eb) :
        {Bool.and(Bool.not(_), P.nolf(NR.chars(List.take(&2, U32, t, D.run_len(t, 10))))) == True{} : Bool}
      ih

def rl_nolf(+w: List<&2, U32>) ->
  {P.nolf(NR.chars(List.take(&2, U32, w, D.run_len(w, 10)))) == True{} : Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      rl_nolf.k(x, t, U32.is_eq(x, 10), {==}, rl_nolf(t))

# D.first over a list of length l, from a: a plus the run before the first
# LF of the list from a.
def first_w(+v: List<&2, U32>, +a: Nat, +l: Nat, +hl: {List.length(&2, U32, v) == l : Nat}) ->
  {D.first(v, a, l, 10) == Nat.add(a, D.run_len(List.drop(&2, U32, v, a), 10)) : Nat}:
  +w = List.drop(&2, U32, v, a)
  %hl : {Nat.add(a, D.run_len(List.take(&2, U32, w, Nat.sub(_, a)), 10)) == Nat.add(a, D.run_len(w, 10)) : Nat}
  %SH.drop_length(v, a) : {Nat.add(a, D.run_len(List.take(&2, U32, w, _), 10)) == Nat.add(a, D.run_len(w, 10)) : Nat}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, w, List.length(&2, U32, w)), w, G.take_all(w)) : {Nat.add(a, D.run_len(_, 10)) == Nat.add(a, D.run_len(w, 10)) : Nat}
  {==}
