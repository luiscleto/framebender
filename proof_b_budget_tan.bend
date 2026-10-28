import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# The normalizer never lengthens a record (for the output-length bound,
# notes/bytes_proofs_budget.md): its end (POS + len(REF)) never moves right,
# its alleles never get more letters, and their number stays.

def Bs() -> Data:
  List<&2, B.Base>

def Als() -> Data:
  List<&2, List<&2, B.Base>>

def lenb(+xs: List<&2, B.Base>) -> Nat:
  List.length(&2, B.Base, xs)

def nals(+xs: List<&2, List<&2, B.Base>>) -> Nat:
  List.length(&2, List<&2, B.Base>, xs)

# The first allele's length.
def hd(als: List<&2, List<&2, B.Base>>) -> Nat:
  match als:
    case Nil{}:
      0n
    case a <> t:
      lenb(a)

# Every allele has a base.
def nz(als: List<&2, List<&2, B.Base>>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case a <> t:
      Nat.is_le(1n, lenb(a)) && nz(t)

# The bound kept by every step: end, letters, number of alleles, no empty allele.
def BND(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>) -> Type:
  {Nat.is_le(Nat.add(p2, hd(a2)), Nat.add(p1, hd(a1))) == True{} : Bool}
  & ({Nat.is_le(V.total(a2), V.total(a1)) == True{} : Bool}
  & ({nals(a2) == nals(a1) : Nat}
  & {nz(a2) == True{} : Bool}))

def bnd_refl(+p: Nat, +a: List<&2, List<&2, B.Base>>, +hz: {nz(a) == True{} : Bool}) -> BND(p, a, p, a):
  (N.le_refl(Nat.add(p, hd(a))), (N.le_refl(V.total(a)), ({==}, hz)))

def bnd_trans(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>, +p3: Nat, +a3: List<&2, List<&2, B.Base>>,
  h1: BND(p1, a1, p2, a2), h2: BND(p2, a2, p3, a3)) -> BND(p1, a1, p3, a3):
  match h1:
    case (e1, r1):
      match r1:
        case (t1, q1):
          match q1:
            case (n1, z1):
              match h2:
                case (e2, r2):
                  match r2:
                    case (t2, q2):
                      match q2:
                        case (n2, z2):
                          (N.le_trans(Nat.add(p3, hd(a3)), Nat.add(p2, hd(a2)), Nat.add(p1, hd(a1)), e2, e1),
                            (N.le_trans(V.total(a3), V.total(a2), V.total(a1), t2, t1),
                              (Equal.trans(Nat, nals(a3), nals(a2), nals(a1), n2, n1), z2)))

# ---------------------------------------------------------------------------
# Lists
# ---------------------------------------------------------------------------

def take_le(+xs: List<&2, B.Base>, +n: Nat) -> {Nat.is_le(lenb(List.take(&2, B.Base, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      N.le_zero_l(n)
    case Con{x, +t} 0n:
      {==}
    case Con{x, +t} 1n+k:
      take_le(t, k)

def take_le2(+xs: List<&2, B.Base>, +n: Nat) -> {Nat.is_le(lenb(List.take(&2, B.Base, xs, n)), lenb(xs)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{x, +t} 0n:
      N.le_zero_l(1n+lenb(t))
    case Con{x, +t} 1n+k:
      take_le2(t, k)

# init(a) has at most len(a) - 1 letters (and at most len(a)).
def init_le1(+a: List<&2, B.Base>) -> {Nat.is_le(lenb(V.init(a)), Nat.sub(lenb(a), 1n)) == True{} : Bool}:
  take_le(a, Nat.sub(lenb(a), 1n))

def init_le(+a: List<&2, B.Base>) -> {Nat.is_le(lenb(V.init(a)), lenb(a)) == True{} : Bool}:
  take_le2(a, Nat.sub(lenb(a), 1n))

def tail_eq(+a: List<&2, B.Base>) -> {lenb(List.tail(&2, B.Base, a)) == Nat.sub(lenb(a), 1n) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +t}:
      Equal.sym(Nat, Nat.sub(lenb(t), 0n), lenb(t), N.sub_zero(lenb(t)))

# 1 + (n - 1) <= n when n >= 1 (and 1 + m <= n from m <= n - 1).
def one_sub(+m: Nat, +n: Nat, +hm: {Nat.is_le(m, Nat.sub(n, 1n)) == True{} : Bool}, +hn: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {Nat.is_le(1n+m, n) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(1n+m, z) == True{} : Bool}, Nat.add(1n, Nat.sub(n, 1n)), n, N.le_sub_add(1n, n, hn), hm)

def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.le_add_l(p, 1n))

def take_eq(+xs: List<&2, B.Base>, +n: Nat, +h: {Nat.is_le(n, lenb(xs)) == True{} : Bool}) -> {lenb(List.take(&2, B.Base, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      Empty.absurd({lenb(List.take(&2, B.Base, Nil{}, 1n+k)) == 1n+k : Nat}, N.false_ne_true(h))
    case Con{x, +t} 0n:
      {==}
    case Con{x, +t} 1n+k:
      Equal.cong(Nat, Nat, z => 1n+z, lenb(List.take(&2, B.Base, t, k)), k, take_eq(t, k, h))

# An allele of 2 or more letters keeps one after init or tail.
def init_pos(+a: List<&2, B.Base>, +h: {Nat.is_le(2n, lenb(a)) == True{} : Bool}) -> {Nat.is_le(1n, lenb(V.init(a))) == True{} : Bool}:
  +h1 = N.le_sub_r(1n, 1n, lenb(a), h)
  AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.sub(lenb(a), 1n), lenb(V.init(a)),
    Equal.sym(Nat, lenb(V.init(a)), Nat.sub(lenb(a), 1n), take_eq(a, Nat.sub(lenb(a), 1n), sub_le(lenb(a), 1n))), h1)

def tail_pos(+a: List<&2, B.Base>, +h: {Nat.is_le(2n, lenb(a)) == True{} : Bool}) -> {Nat.is_le(1n, lenb(List.tail(&2, B.Base, a))) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.sub(lenb(a), 1n), lenb(List.tail(&2, B.Base, a)),
    Equal.sym(Nat, lenb(List.tail(&2, B.Base, a)), Nat.sub(lenb(a), 1n), tail_eq(a)), N.le_sub_r(1n, 1n, lenb(a), h))

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# ---------------------------------------------------------------------------
# One step: trim the last base, shift one base left, drop the first base
# ---------------------------------------------------------------------------

def hd_inits(als: List<&2, List<&2, B.Base>>) -> {Nat.is_le(hd(V.inits(als)), hd(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case a <> t:
      init_le(a)

def tot_inits(als: List<&2, List<&2, B.Base>>) -> {Nat.is_le(V.total(V.inits(als)), V.total(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      P.le_add(lenb(V.init(a)), lenb(a), V.total(V.inits(t)), V.total(t), init_le(a), tot_inits(t))

def n_inits(als: List<&2, List<&2, B.Base>>) -> {nals(V.inits(als)) == nals(als) : Nat}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      Equal.cong(Nat, Nat, z => 1n+z, nals(V.inits(t)), nals(t), n_inits(t))

def nz_inits(als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool}) -> {nz(V.inits(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      and_tt(Nat.is_le(1n, lenb(V.init(a))), nz(V.inits(t)), init_pos(a, N.and_true_l(Nat.is_le(2n, lenb(a)), V.all_long(t), hl)),
        nz_inits(t, N.and_true_r(Nat.is_le(2n, lenb(a)), V.all_long(t), hl)))

def trim_bnd(+pos: Nat, +als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool}) -> BND(pos, als, pos, V.inits(als)):
  (N.le_add_mono_l(pos, hd(V.inits(als)), hd(als), hd_inits(als)), (tot_inits(als), (n_inits(als), nz_inits(als, hl))))

def tot_shift(+x: B.Base, als: List<&2, List<&2, B.Base>>, +hz: {nz(als) == True{} : Bool}) -> {Nat.is_le(V.total(V.shifted(x, als)), V.total(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      P.le_add(1n+lenb(V.init(a)), lenb(a), V.total(V.shifted(x, t)), V.total(t),
        one_sub(lenb(V.init(a)), lenb(a), init_le1(a), N.and_true_l(Nat.is_le(1n, lenb(a)), nz(t), hz)),
        tot_shift(x, t, N.and_true_r(Nat.is_le(1n, lenb(a)), nz(t), hz)))

def n_shift(+x: B.Base, als: List<&2, List<&2, B.Base>>) -> {nals(V.shifted(x, als)) == nals(als) : Nat}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      Equal.cong(Nat, Nat, z => 1n+z, nals(V.shifted(x, t)), nals(t), n_shift(x, t))

def nz_shift(+x: B.Base, als: List<&2, List<&2, B.Base>>) -> {nz(V.shifted(x, als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      and_tt(Nat.is_le(1n, 1n+lenb(V.init(a))), nz(V.shifted(x, t)), N.le_zero_l(lenb(V.init(a))), nz_shift(x, t))

def e_shift(+x: B.Base, +pos: Nat, als: List<&2, List<&2, B.Base>>, +hz: {nz(als) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.sub(pos, 1n), hd(V.shifted(x, als))), Nat.add(pos, hd(als))) == True{} : Bool}:
  match als:
    case Nil{}:
      N.le_add_mono_r(0n, Nat.sub(pos, 1n), pos, sub_le(pos, 1n))
    case +a <> +t:
      P.le_add(Nat.sub(pos, 1n), pos, 1n+lenb(V.init(a)), lenb(a), sub_le(pos, 1n),
        one_sub(lenb(V.init(a)), lenb(a), init_le1(a), N.and_true_l(Nat.is_le(1n, lenb(a)), nz(t), hz)))

def shift_bnd(+x: B.Base, +pos: Nat, +als: List<&2, List<&2, B.Base>>, +hz: {nz(als) == True{} : Bool}) -> BND(pos, als, Nat.sub(pos, 1n), V.shifted(x, als)):
  (e_shift(x, pos, als, hz), (tot_shift(x, als, hz), (n_shift(x, als), nz_shift(x, als))))

def tot_tails(als: List<&2, List<&2, B.Base>>) -> {Nat.is_le(V.total(V.tails(als)), V.total(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      P.le_add(lenb(List.tail(&2, B.Base, a)), lenb(a), V.total(V.tails(t)), V.total(t),
        AB.subst(Nat, z => {Nat.is_le(z, lenb(a)) == True{} : Bool}, Nat.sub(lenb(a), 1n), lenb(List.tail(&2, B.Base, a)),
          Equal.sym(Nat, lenb(List.tail(&2, B.Base, a)), Nat.sub(lenb(a), 1n), tail_eq(a)), sub_le(lenb(a), 1n)),
        tot_tails(t))

def n_tails(als: List<&2, List<&2, B.Base>>) -> {nals(V.tails(als)) == nals(als) : Nat}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      Equal.cong(Nat, Nat, z => 1n+z, nals(V.tails(t)), nals(t), n_tails(t))

def nz_tails(als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool}) -> {nz(V.tails(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +a <> +t:
      and_tt(Nat.is_le(1n, lenb(List.tail(&2, B.Base, a))), nz(V.tails(t)), tail_pos(a, N.and_true_l(Nat.is_le(2n, lenb(a)), V.all_long(t), hl)),
        nz_tails(t, N.and_true_r(Nat.is_le(2n, lenb(a)), V.all_long(t), hl)))

def e_tails(+pos: Nat, als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool}, +hn: {Nat.is_le(1n, nals(als)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(1n+pos, hd(V.tails(als))), Nat.add(pos, hd(als))) == True{} : Bool}:
  match als:
    case Nil{}:
      Empty.absurd({Nat.is_le(Nat.add(1n+pos, 0n), Nat.add(pos, 0n)) == True{} : Bool}, N.false_ne_true(hn))
    case +a <> +t:
      +L = lenb(a)
      +hL = N.le_trans(1n, 2n, L, {==}, N.and_true_l(Nat.is_le(2n, L), V.all_long(t), hl))
      +e1 = Equal.trans(Nat, Nat.add(pos, L), Nat.add(pos, 1n+Nat.sub(L, 1n)), 1n+Nat.add(pos, Nat.sub(L, 1n)),
        Equal.cong(Nat, Nat, z => Nat.add(pos, z), L, 1n+Nat.sub(L, 1n), Equal.sym(Nat, Nat.add(1n, Nat.sub(L, 1n)), L, N.le_sub_add(1n, L, hL))),
        N.add_succ(pos, Nat.sub(L, 1n)))
      +p0 = AB.subst(Nat, z => {Nat.is_le(1n+Nat.add(pos, Nat.sub(L, 1n)), z) == True{} : Bool}, 1n+Nat.add(pos, Nat.sub(L, 1n)), Nat.add(pos, L), Equal.sym(Nat, Nat.add(pos, L), 1n+Nat.add(pos, Nat.sub(L, 1n)), e1),
        N.le_refl(1n+Nat.add(pos, Nat.sub(L, 1n))))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(1n+pos, z), Nat.add(pos, L)) == True{} : Bool}, Nat.sub(L, 1n), lenb(List.tail(&2, B.Base, a)),
        Equal.sym(Nat, lenb(List.tail(&2, B.Base, a)), Nat.sub(L, 1n), tail_eq(a)), p0)

def drop_bnd(+pos: Nat, +als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool}, +hn: {Nat.is_le(1n, nals(als)) == True{} : Bool}) ->
  BND(pos, als, 1n+pos, V.tails(als)):
  (e_tails(pos, als, hl, hn), (tot_tails(als), (n_tails(als), nz_tails(als, hl))))

def bnd_n(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>, h: BND(p1, a1, p2, a2)) -> {nals(a2) == nals(a1) : Nat}:
  match h:
    case (e, r):
      match r:
        case (t, q):
          match q:
            case (n, z):
              n

# ---------------------------------------------------------------------------
# The loops: right (trim and shift), left (drop first bases)
# ---------------------------------------------------------------------------

# What an action needs for its step to keep the bound: a trim needs long alleles.
def AOK(act: V.Act, +als: List<&2, List<&2, B.Base>>) -> Type:
  match act:
    case V.AStop{}:
      Unit
    case V.ATrim{}:
      {V.all_long(als) == True{} : Bool}
    case V.AShift{b}:
      Unit
    case V.ANeed{}:
      Unit

def na_ok.if(eq: Bool, long: Bool, sh: Bool, b: Maybe<&2, B.Base>, +als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == long : Bool}) ->
  AOK(V.next_act.if(eq, long, sh, b), als):
  match eq:
    case False{}:
      Unit{}
    case True{}:
      match long:
        case True{}:
          hl
        case False{}:
          match sh:
            case False{}:
              Unit{}
            case True{}:
              match b:
                case None{}:
                  Unit{}
                case Some{x}:
                  Unit{}

def na_ok(+off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>) -> AOK(V.next_act(off, bases, pos, als), als):
  na_ok.if(V.lasts_eq(als), V.all_long(als), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)), als, {==})

def RB(+pos: Nat, +als: List<&2, List<&2, B.Base>>, m: Maybe<&2, V.Cur>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{V.Cur{p2, a2}}:
      BND(pos, als, p2, a2)

def rb_trans(+p0: Nat, +a0: List<&2, List<&2, B.Base>>, +p1: Nat, +a1: List<&2, List<&2, B.Base>>, m: Maybe<&2, V.Cur>,
  h1: BND(p0, a0, p1, a1), h2: RB(p1, a1, m)) -> RB(p0, a0, m):
  match m:
    case None{}:
      Unit{}
    case Some{V.Cur{+p2, +a2}}:
      bnd_trans(p0, a0, p1, a1, p2, a2, h1, h2)

def RTI(+f: Nat, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +a: List<&2, List<&2, B.Base>>) -> Type:
  AOK(V.next_act(off, bases, pos, a), a) -> {nz(a) == True{} : Bool} -> RB(pos, a, V.right(f, V.next_act(off, bases, pos, a), off, bases, pos, a))

def rt_trim(+f: Nat, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>, +hl: {V.all_long(als) == True{} : Bool},
  ih: RTI(f, off, bases, pos, V.inits(als))) -> RB(pos, als, V.right(f, V.next_act(off, bases, pos, V.inits(als)), off, bases, pos, V.inits(als))):
  +a = V.inits(als)
  rb_trans(pos, als, pos, a, V.right(f, V.next_act(off, bases, pos, a), off, bases, pos, a), trim_bnd(pos, als, hl),
    ih(na_ok(off, bases, pos, a), nz_inits(als, hl)))

def rt(+fuel: Nat, +act: V.Act, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +als: List<&2, List<&2, B.Base>>,
  +hz: {nz(als) == True{} : Bool}, ha: AOK(act, als)) -> RB(pos, als, V.right(fuel, act, off, bases, pos, als)):
  match fuel:
    case 0n:
      bnd_refl(pos, als, hz)
    case 1n+f:
      match act:
        case V.AStop{}:
          bnd_refl(pos, als, hz)
        case V.ANeed{}:
          Unit{}
        case V.ATrim{}:
          rt_trim(f, off, bases, pos, als, ha, ih => ihz => rt(f, V.next_act(off, bases, pos, V.inits(als)), off, bases, pos, V.inits(als), ihz, ih))
        case V.AShift{+b}:
          +p = Nat.sub(pos, 1n)
          +a = V.shifted(b, als)
          rb_trans(pos, als, p, a, V.right(f, V.next_act(off, bases, p, a), off, bases, p, a), shift_bnd(b, pos, als, hz),
            rt(f, V.next_act(off, bases, p, a), off, bases, p, a, nz_shift(b, als), na_ok(off, bases, p, a)))

def fe_n(als: List<&2, List<&2, B.Base>>, +h: {V.firsts_eq(als) == True{} : Bool}) -> {Nat.is_le(1n, nals(als)) == True{} : Bool}:
  match als:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.false_ne_true(h))
    case a <> t:
      N.le_zero_l(nals(t))

def CB(+pos: Nat, +als: List<&2, List<&2, B.Base>>, c: V.Cur) -> Type:
  match c:
    case V.Cur{p2, a2}:
      BND(pos, als, p2, a2)

def cb_trans(+p0: Nat, +a0: List<&2, List<&2, B.Base>>, +p1: Nat, +a1: List<&2, List<&2, B.Base>>, c: V.Cur,
  h1: BND(p0, a0, p1, a1), h2: CB(p1, a1, c)) -> CB(p0, a0, c):
  match c:
    case V.Cur{+p2, +a2}:
      bnd_trans(p0, a0, p1, a1, p2, a2, h1, h2)

def lt(+fuel: Nat, +go: Bool, +pos: Nat, +als: List<&2, List<&2, B.Base>>,
  +hz: {nz(als) == True{} : Bool}, +hg: {Bool.and(V.firsts_eq(als), V.all_long(als)) == go : Bool}) -> CB(pos, als, V.left(fuel, go, pos, als)):
  match fuel:
    case 0n:
      bnd_refl(pos, als, hz)
    case 1n+f:
      match go:
        case False{}:
          bnd_refl(pos, als, hz)
        case True{}:
          +a = V.tails(als)
          +hl = N.and_true_r(V.firsts_eq(als), V.all_long(als), hg)
          +hn = fe_n(als, N.and_true_l(V.firsts_eq(als), V.all_long(als), hg))
          cb_trans(pos, als, 1n+pos, a, V.left(f, Bool.and(V.firsts_eq(a), V.all_long(a)), 1n+pos, a), drop_bnd(pos, als, hl, hn),
            lt(f, Bool.and(V.firsts_eq(a), V.all_long(a)), 1n+pos, a, nz_tails(als, hl), {==}))

def bnd_z(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>, h: BND(p1, a1, p2, a2)) -> {nz(a2) == True{} : Bool}:
  match h:
    case (e, r):
      match r:
        case (t, q):
          match q:
            case (n, z):
              z

# ---------------------------------------------------------------------------
# The normalized variant
# ---------------------------------------------------------------------------

def VB(+pos: Nat, +als: List<&2, List<&2, B.Base>>, w: B.Var) -> Type:
  match w:
    case B.Var{p2, r2, t2}:
      BND(pos, als, p2, r2 <> t2)

def MVB(+pos: Nat, +als: List<&2, List<&2, B.Base>>, m: Maybe<&2, B.Var>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{w}:
      VB(pos, als, w)

def tv(+pos: Nat, +als: List<&2, List<&2, B.Base>>, c: V.Cur, h: CB(pos, als, c), +hn: {Nat.is_le(1n, nals(als)) == True{} : Bool}) -> VB(pos, als, V.to_var(c)):
  match c:
    case V.Cur{+p, Nil{}}:
      +e = bnd_n(pos, als, p, Nil{}, h)
      Empty.absurd(VB(pos, als, V.to_var(V.Cur{p, Nil{}})),
        N.false_ne_true(AB.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, nals(als), 0n, Equal.sym(Nat, 0n, nals(als), e), hn)))
    case V.Cur{+p, r <> t}:
      h

def lo(+pos: Nat, +als: List<&2, List<&2, B.Base>>, m: Maybe<&2, V.Cur>, h1: RB(pos, als, m), h2: RB(pos, als, m),
  +hn: {Nat.is_le(1n, nals(als)) == True{} : Bool}) -> MVB(pos, als, V.left_of(m)):
  match m:
    case None{}:
      Unit{}
    case Some{V.Cur{+p, +a}}:
      +g = Bool.and(V.firsts_eq(a), V.all_long(a))
      +c = V.left(Nat.add(p, V.total(a)), g, p, a)
      tv(pos, als, c, cb_trans(pos, als, p, a, c, h1, lt(Nat.add(p, V.total(a)), g, p, a, bnd_z(pos, als, p, a, h2), {==})), hn)

# var_in's answer (when it has one) keeps the bound.
def var_in_bnd(+off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hz: {nz(ref <> alts) == True{} : Bool}) -> MVB(pos, ref <> alts, V.var_in(off, bases, B.Var{pos, ref, alts})):
  +als = {ref <> alts : List<&2, List<&2, B.Base>>}
  +fuel = Nat.add(pos, V.total(als))
  +act = V.next_act(off, bases, pos, als)
  lo(pos, als, V.right(fuel, act, off, bases, pos, als),
    rt(fuel, act, off, bases, pos, als, hz, na_ok(off, bases, pos, als)),
    rt(fuel, act, off, bases, pos, als, hz, na_ok(off, bases, pos, als)),
    N.le_zero_l(nals(alts)))

def df(+pos: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, +hz: {nz(ref <> alts) == True{} : Bool},
  m: Maybe<&2, B.Var>, h: MVB(pos, ref <> alts, m)) -> VB(pos, ref <> alts, Maybe.default(&2, B.Var, m, B.Var{pos, ref, alts})):
  match m:
    case None{}:
      bnd_refl(pos, ref <> alts, hz)
    case Some{w}:
      h

# The normal form keeps the bound: its end is not right of v's, it has no
# more letters, as many alleles, and none empty.
def normal_bnd(+seq: List<&2, B.Base>, +pos: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hz: {nz(ref <> alts) == True{} : Bool}) -> VB(pos, ref <> alts, V.normal(seq, B.Var{pos, ref, alts})):
  df(pos, ref, alts, hz, V.var_in(0n, seq, B.Var{pos, ref, alts}), var_in_bnd(0n, seq, pos, ref, alts, hz))
