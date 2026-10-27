import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_rep.bend as RP
import ./proof_var_steps.bend as ST
import ./proof_var_spec.bend as SP
import ./proof_var_n1.bend as N

# The normalizer on the whole contig (off = 0, bases = seq): both loops keep
# "valid, same haps h, size <= s"; the right loop stops when the alleles do
# not all end alike, or at pos 1 with a one-base allele; the left loop keeps
# that and stops when they do not all start alike or one is short. The
# result is valid, makes the same change, is no bigger, and is normalized.

def Gd(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, +p: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Bool:
  L.valid(seq, B.Var{p, r, xs}) && B.Alleles.eq(L.haps(seq, B.Var{p, r, xs}), h) && Nat.is_le(L.size(B.Var{p, r, xs}), s)

def gd_valid(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hg: {Gd(seq, h, s, p, r, xs) == True{} : Bool}) ->
  RP.Valid(seq, p, r, xs):
  +v = {B.Var{p, r, xs} : B.Var}
  P.and_true_l(L.valid(seq, v), B.Alleles.eq(L.haps(seq, v), h),
    P.and_true_l(Bool.and(L.valid(seq, v), B.Alleles.eq(L.haps(seq, v), h)), Nat.is_le(L.size(v), s), hg))

def gd_haps(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hg: {Gd(seq, h, s, p, r, xs) == True{} : Bool}) ->
  {L.haps(seq, B.Var{p, r, xs}) == h : Q.Als()}:
  +v = {B.Var{p, r, xs} : B.Var}
  Q.alleles_sound(L.haps(seq, v), h, P.and_true_r(L.valid(seq, v), B.Alleles.eq(L.haps(seq, v), h),
    P.and_true_l(Bool.and(L.valid(seq, v), B.Alleles.eq(L.haps(seq, v), h)), Nat.is_le(L.size(v), s), hg)))

def gd_size(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hg: {Gd(seq, h, s, p, r, xs) == True{} : Bool}) ->
  {Nat.is_le(L.size(B.Var{p, r, xs}), s) == True{} : Bool}:
  +v = {B.Var{p, r, xs} : B.Var}
  P.and_true_r(Bool.and(L.valid(seq, v), B.Alleles.eq(L.haps(seq, v), h)), Nat.is_le(L.size(v), s), hg)

def gd_step(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, +p2: Nat, +r2: Q.Bs(), +xs2: Q.Als(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(),
  +hg: {Gd(seq, h, s, p, r, xs) == True{} : Bool}, +hv2: RP.Valid(seq, p2, r2, xs2),
  +hh: {L.haps(seq, B.Var{p2, r2, xs2}) == L.haps(seq, B.Var{p, r, xs}) : Q.Als()},
  +hz: {Nat.is_le(L.size(B.Var{p2, r2, xs2}), L.size(B.Var{p, r, xs})) == True{} : Bool}) ->
  {Gd(seq, h, s, p2, r2, xs2) == True{} : Bool}:
  +v2 = {B.Var{p2, r2, xs2} : B.Var}
  +e = Equal.trans(Q.Als(), L.haps(seq, v2), L.haps(seq, B.Var{p, r, xs}), h, hh, gd_haps(seq, h, s, p, r, xs, hg))
  Q.and_tt(Bool.and(L.valid(seq, v2), B.Alleles.eq(L.haps(seq, v2), h)), Nat.is_le(L.size(v2), s),
    Q.and_tt(L.valid(seq, v2), B.Alleles.eq(L.haps(seq, v2), h), hv2,
      %Equal.sym(Q.Als(), L.haps(seq, v2), h, e) : {B.Alleles.eq(_, h) == True{} : Bool}; Q.alleles_refl(h)),
    Q.le_trans(L.size(v2), L.size(B.Var{p, r, xs}), s, hz, gd_size(seq, h, s, p, r, xs, hg)))

# Sizes
# =====

def len_tail_le(+x: Q.Bs()) -> {Nat.is_le(Q.len(List.tail(&2, B.Base, x)), Q.len(x)) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case g <> u:
      Q.le_succ(Q.len(u))

def len_init_le(+x: Q.Bs()) -> {Nat.is_le(Q.len(V.init(x)), Q.len(x)) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case +g <> +u:
      %Q.len_init_r(g, u) : {Nat.is_le(_, 1n+Q.len(u)) == True{} : Bool}
      Q.le_succ(Q.len(u))

def total_inits_le(+xs: Q.Als()) -> {Nat.is_le(L.total(V.inits(xs)), L.total(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      P.le_add(Q.len(V.init(x)), Q.len(x), L.total(V.inits(t)), L.total(t), len_init_le(x), total_inits_le(t))

def total_tails_le(+xs: Q.Als()) -> {Nat.is_le(L.total(V.tails(xs)), L.total(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      P.le_add(Q.len(List.tail(&2, B.Base, x)), Q.len(x), L.total(V.tails(t)), L.total(t), len_tail_le(x), total_tails_le(t))

def total_shifted(+c: B.Base, +xs: Q.Als(), +hne: {L.all_nonempty(xs) == True{} : Bool}) ->
  {L.total(V.shifted(c, xs)) == L.total(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({L.total(V.shifted(c, Nil{} <> t)) == L.total(Nil{} <> t) : Nat}, P.false_ne_true(hne))
        case +g <> +u:
          +hne2 = P.and_true_r(Nat.is_le(1n, Q.len(g <> u)), L.all_nonempty(t), hne)
          %Q.len_init_r(g, u) : {Nat.add(1n+_, L.total(V.shifted(c, t))) == Nat.add(1n+Q.len(u), L.total(t)) : Nat}
          %total_shifted(c, t, hne2) : {Nat.add(1n+Q.len(u), L.total(V.shifted(c, t))) == Nat.add(1n+Q.len(u), _) : Nat}
          {==}

def size_trim(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, p, r, xs)) ->
  {Nat.is_le(1n+L.size(B.Var{p, V.init(r), V.inits(xs)}), L.size(B.Var{p, r, xs})) == True{} : Bool}:
  match r:
    case Nil{}:
      SP.no_ref(seq, p, xs, hv, {Nat.is_le(1n+L.size(B.Var{p, V.init(Nil{}), V.inits(xs)}), L.size(B.Var{p, Nil{}, xs})) == True{} : Bool})
    case +g <> +u:
      P.le_add(Q.len(Q.init(g <> u)), Q.len(u), L.total(V.inits(xs)), L.total(xs), Q.le_of_eq(Q.len(Q.init(g <> u)), Q.len(u), Q.len_init(g, u)),
        total_inits_le(xs))

def size_shift(+seq: Q.Bs(), +p: Nat, +p2: Nat, +x: B.Base, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, p, r, xs)) ->
  {L.size(B.Var{p2, x <> V.init(r), V.shifted(x, xs)}) == L.size(B.Var{p, r, xs}) : Nat}:
  match r:
    case Nil{}:
      SP.no_ref(seq, p, xs, hv, {L.size(B.Var{p2, x <> V.init(Nil{}), V.shifted(x, xs)}) == L.size(B.Var{p, Nil{}, xs}) : Nat})
    case +g <> +u:
      %Q.len_init_r(g, u) : {Nat.add(1n+_, L.total(V.shifted(x, xs))) == Nat.add(1n+Q.len(u), L.total(xs)) : Nat}
      %total_shifted(x, xs, RP.vk4(seq, p, g <> u, xs, hv)) : {Nat.add(1n+Q.len(u), L.total(V.shifted(x, xs))) == Nat.add(1n+Q.len(u), _) : Nat}
      {==}

def size_left(+seq: Q.Bs(), +p: Nat, +p2: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, p, r, xs)) ->
  {Nat.is_le(1n+L.size(B.Var{p2, List.tail(&2, B.Base, r), V.tails(xs)}), L.size(B.Var{p, r, xs})) == True{} : Bool}:
  match r:
    case Nil{}:
      SP.no_ref(seq, p, xs, hv,
        {Nat.is_le(1n+L.size(B.Var{p2, List.tail(&2, B.Base, Nil{}), V.tails(xs)}), L.size(B.Var{p, Nil{}, xs})) == True{} : Bool})
    case +g <> +u:
      P.le_add(Q.len(u), Q.len(u), L.total(V.tails(xs)), L.total(xs), P.le_refl(Q.len(u)), total_tails_le(xs))

def size_pos(+seq: Q.Bs(), +p: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, p, r, xs)) ->
  {Nat.is_le(1n, L.size(B.Var{p, r, xs})) == True{} : Bool}:
  Q.le_trans(1n, Q.len(r), Nat.add(Q.len(r), L.total(xs)), RP.vk2(seq, p, r, xs, hv), P.le_of_add(Q.len(r), L.total(xs)))

def le_add_l(+n: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(n, x)) == True{} : Bool}:
  match n:
    case 0n:
      P.le_refl(x)
    case 1n+m:
      Q.le_trans(x, Nat.add(m, x), 1n+Nat.add(m, x), le_add_l(m, x), Q.le_succ(Nat.add(m, x)))

# Fuel
# ====

def add_lt(+n: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(n, a), Nat.add(n, b)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      add_lt(m, a, b, h)

def fuel_trim(+pos: Nat, +s1: Nat, +s0: Nat, +f: Nat, +hz: {Nat.is_le(1n+s1, s0) == True{} : Bool},
  +hf: {Nat.is_le(Nat.add(pos, s0), 1n+f) == True{} : Bool}) -> {Nat.is_le(Nat.add(pos, s1), f) == True{} : Bool}:
  Q.le_trans(1n+Nat.add(pos, s1), Nat.add(pos, s0), 1n+f, add_lt(pos, s1, s0, hz), hf)

def fuel_shift(+pos: Nat, +s1: Nat, +s0: Nat, +f: Nat, +hz: {s1 == s0 : Nat}, +h1: {Nat.is_le(1n, pos) == True{} : Bool},
  +hf: {Nat.is_le(Nat.add(pos, s0), 1n+f) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.sub(pos, 1n), s1), f) == True{} : Bool}:
  {%Equal.sym(Nat, 1n+Nat.sub(pos, 1n), pos, Q.succ_sub_one(pos, h1)) : {Nat.is_le(Nat.add(_, s1), 1n+f) == True{} : Bool};
    {%Equal.sym(Nat, s1, s0, hz) : {Nat.is_le(Nat.add(pos, _), 1n+f) == True{} : Bool};
      hf : {Nat.is_le(Nat.add(pos, s1), 1n+f) == True{} : Bool}}
    : {Nat.is_le(Nat.add(1n+Nat.sub(pos, 1n), s1), 1n+f) == True{} : Bool}}

def fuel0(+pos: Nat, +s: Nat, h1: {Nat.is_le(1n, pos) == True{} : Bool}, hf: {Nat.is_le(Nat.add(pos, s), 0n) == True{} : Bool}) -> Empty:
  match pos:
    case 0n:
      P.false_ne_true(h1)
    case 1n+p:
      P.false_ne_true(hf)

# Wrappers that open REF
# ======================

def shift_v(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +x: B.Base, +hv: RP.Valid(seq, pos, r, xs),
  +he: {V.lasts_eq(r <> xs) == True{} : Bool}, +hs: {Nat.is_le(2n, pos) == True{} : Bool},
  +hx: {V.Win.get(0n, seq, Nat.sub(pos, 2n)) == Some{x} : Maybe<&2, B.Base>}) ->
  RP.Valid(seq, Nat.sub(pos, 1n), x <> V.init(r), V.shifted(x, xs))
    & {L.haps(seq, B.Var{Nat.sub(pos, 1n), x <> V.init(r), V.shifted(x, xs)}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}:
  match r:
    case Nil{}:
      SP.no_ref(seq, pos, xs, hv, RP.Valid(seq, Nat.sub(pos, 1n), x <> V.init(Nil{}), V.shifted(x, xs))
        & {L.haps(seq, B.Var{Nat.sub(pos, 1n), x <> V.init(Nil{}), V.shifted(x, xs)}) == L.haps(seq, B.Var{pos, Nil{}, xs}) : Q.Als()})
    case +g <> +u:
      SP.shift_gen(seq, pos, g, u, xs, x, hv, he, hs, hx, RP.vA(seq, pos), RP.vB(seq, pos, g <> u),
        RP.valid_es(seq, pos, g <> u, xs, hv), RP.valid_el(seq, pos, g <> u, xs, hv), {==})

def get_some_v(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs), +hs: {Nat.is_le(2n, pos) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Base, V.Win.get(0n, seq, Nat.sub(pos, 2n))) == True{} : Bool}:
  match r:
    case Nil{}:
      SP.no_ref(seq, pos, xs, hv, {Maybe.is_some(&2, B.Base, V.Win.get(0n, seq, Nat.sub(pos, 2n))) == True{} : Bool})
    case +g <> +u:
      SP.get_some(seq, pos, g, u, hs, RP.vA(seq, pos), RP.vB(seq, pos, g <> u),
        RP.valid_es(seq, pos, g <> u, xs, hv), RP.valid_el(seq, pos, g <> u, xs, hv))

def pos_one(+pos: Nat, h1: {Nat.is_le(1n, pos) == True{} : Bool}, h2: {False{} == Nat.is_le(2n, pos) : Bool}) -> {Nat.is_eq(pos, 1n) == True{} : Bool}:
  match pos:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 1n) == True{} : Bool}, P.false_ne_true(h1))
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.is_eq(2n+q, 1n) == True{} : Bool},
            P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(2n, 2n+q), True{}, h2, P.le_zero_l(q))))

# The right loop
# ==============

def stopR(+p: Nat, +als: Q.Als()) -> Bool:
  Bool.not(V.lasts_eq(als)) || (Nat.is_eq(p, 1n) && Bool.not(V.all_long(als)))

def good_c(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, c: V.Cur) -> Bool:
  match c:
    case V.Cur{+p, als}:
      match als:
        case Nil{}:
          False{}
        case +r <> +xs:
          Gd(seq, h, s, p, r, xs) && stopR(p, r <> xs)

def good_r(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, V.Cur>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      good_c(seq, h, s, c)

def right_ok(fuel: Nat, eq: Bool, lg: Bool, sh: Bool, b: Maybe<&2, B.Base>, +seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(),
  +h: Q.Als(), +s: Nat, +he: {eq == V.lasts_eq(r <> xs) : Bool}, +hl: {lg == V.all_long(r <> xs) : Bool},
  +hs: {sh == Nat.is_le(2n, pos) : Bool}, +hb: {b == V.Win.get(0n, seq, Nat.sub(pos, 2n)) : Maybe<&2, B.Base>},
  +hg: {Gd(seq, h, s, pos, r, xs) == True{} : Bool}, +hf: {Nat.is_le(Nat.add(pos, L.size(B.Var{pos, r, xs})), fuel) == True{} : Bool}) ->
  {good_r(seq, h, s, V.right(fuel, V.next_act.if(eq, lg, sh, b), 0n, seq, pos, r <> xs)) == True{} : Bool}:
  match fuel:
    case 0n:
      Empty.absurd({good_r(seq, h, s, V.right(0n, V.next_act.if(eq, lg, sh, b), 0n, seq, pos, r <> xs)) == True{} : Bool},
        fuel0(pos, L.size(B.Var{pos, r, xs}), RP.vk1(seq, pos, r, xs, gd_valid(seq, h, s, pos, r, xs, hg)), hf))
    case 1n+(+f):
      match eq:
        case False{}:
          Q.and_tt(Gd(seq, h, s, pos, r, xs), stopR(pos, r <> xs), hg,
            %he : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(pos, 1n), Bool.not(V.all_long(r <> xs)))) == True{} : Bool}; {==})
        case True{}:
          match lg:
            case True{}:
              +hv = gd_valid(seq, h, s, pos, r, xs, hg)
              +he1 = Equal.sym(Bool, True{}, V.lasts_eq(r <> xs), he)
              +hl1 = Equal.sym(Bool, True{}, V.all_long(r <> xs), hl)
              +s1 = L.size(B.Var{pos, V.init(r), V.inits(xs)})
              +hz = size_trim(seq, pos, r, xs, hv)
              +hg2 = gd_step(seq, h, s, pos, V.init(r), V.inits(xs), pos, r, xs, hg, SP.trim_valid(seq, pos, r, xs, hv, he1, hl1),
                SP.trim_haps(seq, pos, r, xs, hv, he1), Q.le_trans(s1, 1n+s1, L.size(B.Var{pos, r, xs}), Q.le_succ(s1), hz))
              right_ok(f, V.lasts_eq(V.init(r) <> V.inits(xs)), V.all_long(V.init(r) <> V.inits(xs)), Nat.is_le(2n, pos),
                V.Win.get(0n, seq, Nat.sub(pos, 2n)), seq, pos, V.init(r), V.inits(xs), h, s, {==}, {==}, {==}, {==}, hg2,
                fuel_trim(pos, s1, L.size(B.Var{pos, r, xs}), f, hz, hf))
            case False{}:
              match sh:
                case False{}:
                  +hv = gd_valid(seq, h, s, pos, r, xs, hg)
                  Q.and_tt(Gd(seq, h, s, pos, r, xs), stopR(pos, r <> xs), hg,
                    {%he : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(pos, 1n), Bool.not(V.all_long(r <> xs)))) == True{} : Bool};
                      %hl : {Bool.or(Bool.not(True{}), Bool.and(Nat.is_eq(pos, 1n), Bool.not(_))) == True{} : Bool};
                      Q.and_tt(Nat.is_eq(pos, 1n), True{}, pos_one(pos, RP.vk1(seq, pos, r, xs, hv), hs), {==})
                      : {stopR(pos, r <> xs) == True{} : Bool}})
                case True{}:
                  match b:
                    case None{}:
                      +hv = gd_valid(seq, h, s, pos, r, xs, hg)
                      +hs1 = Equal.sym(Bool, True{}, Nat.is_le(2n, pos), hs)
                      Empty.absurd({good_r(seq, h, s, V.right(1n+f, V.ANeed{}, 0n, seq, pos, r <> xs)) == True{} : Bool},
                        P.false_ne_true(
                          %Equal.sym(Maybe<&2, B.Base>, None{}, V.Win.get(0n, seq, Nat.sub(pos, 2n)), hb) : {Maybe.is_some(&2, B.Base, _) == True{} : Bool};
                          get_some_v(seq, pos, r, xs, hv, hs1)))
                    case Some{+x}:
                      +hv = gd_valid(seq, h, s, pos, r, xs, hg)
                      +he1 = Equal.sym(Bool, True{}, V.lasts_eq(r <> xs), he)
                      +hs1 = Equal.sym(Bool, True{}, Nat.is_le(2n, pos), hs)
                      +hx = Equal.sym(Maybe<&2, B.Base>, Some{x}, V.Win.get(0n, seq, Nat.sub(pos, 2n)), hb)
                      +p2 = Nat.sub(pos, 1n)
                      +r2 = {x <> V.init(r) : Q.Bs()}
                      +xs2 = V.shifted(x, xs)
                      +hz = size_shift(seq, pos, p2, x, r, xs, hv)
                      +hg2 = gd_step(seq, h, s, p2, r2, xs2, pos, r, xs, hg,
                        Q.fst(RP.Valid(seq, p2, r2, xs2), {L.haps(seq, B.Var{p2, r2, xs2}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}, shift_v(seq, pos, r, xs, x, hv, he1, hs1, hx)),
                        Q.snd(RP.Valid(seq, p2, r2, xs2), {L.haps(seq, B.Var{p2, r2, xs2}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()}, shift_v(seq, pos, r, xs, x, hv, he1, hs1, hx)),
                        Q.le_of_eq(L.size(B.Var{p2, r2, xs2}), L.size(B.Var{pos, r, xs}), hz))
                      right_ok(f, V.lasts_eq(r2 <> xs2), V.all_long(r2 <> xs2), Nat.is_le(2n, p2), V.Win.get(0n, seq, Nat.sub(p2, 2n)),
                        seq, p2, r2, xs2, h, s, {==}, {==}, {==}, {==}, hg2,
                        fuel_shift(pos, L.size(B.Var{p2, r2, xs2}), L.size(B.Var{pos, r, xs}), f, hz, RP.vk1(seq, pos, r, xs, hv), hf))

# The final state is normalized
# =============================

def la_case(lv: Bool, +seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +hl: {lv == V.same_last(Some{ST.lst(g, u)}, xs) : Bool}, +hst: {stopR(pos, (g <> u) <> xs) == True{} : Bool}) ->
  {L.movable(seq, B.Var{pos, g <> u, xs}, Nat.sub(pos, 1n)) == False{} : Bool}:
  match lv:
    case False{}:
      N.not_movable(Nat.sub(pos, 1n), seq, pos, g, u, xs, hv, Equal.sym(Bool, False{}, V.same_last(Some{ST.lst(g, u)}, xs), hl),
        P.le_refl(Nat.sub(pos, 1n)))
    case True{}:
      +al = V.all_long((g <> u) <> xs)
      +h2 = {%Equal.sym(Bool, True{}, V.same_last(Some{ST.lst(g, u)}, xs), hl) :
          {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(pos, 1n), Bool.not(al))) == True{} : Bool};
        hst : {Bool.and(Nat.is_eq(pos, 1n), Bool.not(al)) == True{} : Bool}}
      +ep = P.eq_sound(pos, 1n, P.and_true_l(Nat.is_eq(pos, 1n), Bool.not(al), h2))
      %Equal.sym(Nat, pos, 1n, ep) : {L.movable(seq, B.Var{_, g <> u, xs}, Nat.sub(_, 1n)) == False{} : Bool}
      {==}

def pa_case(av: Bool, +seq: Q.Bs(), +pos: Nat, +g: B.Base, +u: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, g <> u, xs),
  +ha: {av == V.all_long((g <> u) <> xs) : Bool}, +hst: {stopR(pos, (g <> u) <> xs) == True{} : Bool},
  +hgo: {False{} == Bool.and(V.firsts_eq((g <> u) <> xs), V.all_long((g <> u) <> xs)) : Bool}) ->
  {L.parsimonious(seq, B.Var{pos, g <> u, xs}) == True{} : Bool}:
  match av:
    case False{}:
      +v = {B.Var{pos, g <> u, xs} : B.Var}
      +x = Bool.or(L.same(seq, L.drop_first(v), v), L.same(seq, L.drop_last(v), v))
      +lb = {%ST.long_eq(xs) : {Bool.and(Nat.is_le(2n, Q.len(g <> u)), _) == Bool.and(Nat.is_le(2n, Q.len(g <> u)), V.all_long(xs)) : Bool};
        {==} : {L.all_long(v) == V.all_long((g <> u) <> xs) : Bool}}
      %Equal.sym(Bool, L.all_long(v), V.all_long((g <> u) <> xs), lb) : {Bool.not(Bool.and(_, x)) == True{} : Bool}
      %ha : {Bool.not(Bool.and(_, x)) == True{} : Bool}
      {==}
    case True{}:
      +v = {B.Var{pos, g <> u, xs} : B.Var}
      +al = V.all_long((g <> u) <> xs)
      +fe = V.firsts_eq((g <> u) <> xs)
      +sl = V.same_last(Some{ST.lst(g, u)}, xs)
      +ha1 = Equal.sym(Bool, True{}, al, ha)
      +hf = Q.and_l_false(fe, al, Equal.sym(Bool, False{}, Bool.and(fe, al), hgo), ha1)
      +hln = Q.false_of(sl, ht => P.true_ne_false(Equal.trans(Bool, True{}, al, False{}, ha,
        P.not_true(al, P.and_true_r(Nat.is_eq(pos, 1n), Bool.not(al),
          {%ht : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(pos, 1n), Bool.not(al))) == True{} : Bool};
            hst : {Bool.and(Nat.is_eq(pos, 1n), Bool.not(al)) == True{} : Bool}})))))
      +hdf = Q.false_of(L.same(seq, L.drop_first(v), v), h => P.true_ne_false(Equal.trans(Bool, True{}, fe, False{},
        Equal.sym(Bool, fe, True{}, SP.firsts_of_drop_first(seq, pos, g <> u, xs, hv, h)), hf)))
      +hdl = Q.false_of(L.same(seq, L.drop_last(v), v), h => P.true_ne_false(Equal.trans(Bool, True{}, sl, False{},
        Equal.sym(Bool, sl, True{}, SP.lasts_of_drop_last(seq, pos, g <> u, xs, hv, h)), hln)))
      %Equal.sym(Bool, L.same(seq, L.drop_first(v), v), False{}, hdf) :
        {Bool.not(Bool.and(L.all_long(v), Bool.or(_, L.same(seq, L.drop_last(v), v)))) == True{} : Bool}
      %Equal.sym(Bool, L.same(seq, L.drop_last(v), v), False{}, hdl) : {Bool.not(Bool.and(L.all_long(v), Bool.or(False{}, _))) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(L.all_long(v), False{}), False{}, P.and_false_r(L.all_long(v))) : {Bool.not(_) == True{} : Bool}
      {==}

def final_norm(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: RP.Valid(seq, pos, r, xs),
  +hst: {stopR(pos, r <> xs) == True{} : Bool}, +hgo: {False{} == Bool.and(V.firsts_eq(r <> xs), V.all_long(r <> xs)) : Bool}) ->
  {L.normalized(seq, B.Var{pos, r, xs}) == True{} : Bool}:
  match r:
    case Nil{}:
      SP.no_ref(seq, pos, xs, hv, {L.normalized(seq, B.Var{pos, Nil{}, xs}) == True{} : Bool})
    case +g <> +u:
      +v = {B.Var{pos, g <> u, xs} : B.Var}
      Q.and_tt(L.left_aligned(seq, v), L.parsimonious(seq, v),
        %Equal.sym(Bool, L.movable(seq, v, Nat.sub(pos, 1n)), False{},
            la_case(V.same_last(Some{ST.lst(g, u)}, xs), seq, pos, g, u, xs, hv, {==}, hst)) :
          {Bool.not(_) == True{} : Bool};
          {==},
        pa_case(V.all_long((g <> u) <> xs), seq, pos, g, u, xs, hv, {==}, hst, hgo))

# The left loop
# =============

def same_last_tails(+l: B.Base, +xs: Q.Als(), +h: {V.all_long(xs) == True{} : Bool}) ->
  {V.same_last(Some{l}, V.tails(xs)) == V.same_last(Some{l}, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match x:
        case Nil{}:
          Empty.absurd({V.same_last(Some{l}, V.tails(Nil{} <> t)) == V.same_last(Some{l}, Nil{} <> t) : Bool}, P.false_ne_true(h))
        case +g <> +u:
          match u:
            case Nil{}:
              Empty.absurd({V.same_last(Some{l}, V.tails([g] <> t)) == V.same_last(Some{l}, [g] <> t) : Bool}, P.false_ne_true(h))
            case +g2 <> +u2:
              +h2 = P.and_true_r(Nat.is_le(2n, Q.len(g <> g2 <> u2)), V.all_long(t), h)
              +o = V.opt_eq(Some{l}, List.last(&2, B.Base, g2 <> u2))
              %same_last_tails(l, t, h2) : {Bool.and(o, V.same_last(Some{l}, V.tails(t))) == Bool.and(o, _) : Bool}
              {==}

def lasts_tails(+r: Q.Bs(), +xs: Q.Als(), +hl: {V.all_long(r <> xs) == True{} : Bool}) ->
  {V.lasts_eq(List.tail(&2, B.Base, r) <> V.tails(xs)) == V.lasts_eq(r <> xs) : Bool}:
  match r:
    case Nil{}:
      Empty.absurd({V.lasts_eq(List.tail(&2, B.Base, Nil{}) <> V.tails(xs)) == V.lasts_eq(Nil{} <> xs) : Bool}, P.false_ne_true(hl))
    case +g <> +u:
      match u:
        case Nil{}:
          Empty.absurd({V.lasts_eq(List.tail(&2, B.Base, [g]) <> V.tails(xs)) == V.lasts_eq([g] <> xs) : Bool}, P.false_ne_true(hl))
        case +g2 <> +u2:
          same_last_tails(ST.lst(g2, u2), xs, P.and_true_r(Nat.is_le(2n, Q.len(g <> g2 <> u2)), V.all_long(xs), hl))

def stop_tails(+pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hst: {stopR(pos, r <> xs) == True{} : Bool}, +hl: {V.all_long(r <> xs) == True{} : Bool}) ->
  {stopR(1n+pos, List.tail(&2, B.Base, r) <> V.tails(xs)) == True{} : Bool}:
  +al = V.all_long(r <> xs)
  +le = V.lasts_eq(r <> xs)
  +hln = Q.false_of(le, ht => P.true_ne_false(Equal.trans(Bool, True{}, al, False{}, Equal.sym(Bool, al, True{}, hl),
    P.not_true(al, P.and_true_r(Nat.is_eq(pos, 1n), Bool.not(al),
      {%ht : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(pos, 1n), Bool.not(al))) == True{} : Bool};
        hst : {Bool.and(Nat.is_eq(pos, 1n), Bool.not(al)) == True{} : Bool}})))))
  +a2 = {List.tail(&2, B.Base, r) <> V.tails(xs) : Q.Als()}
  %Equal.sym(Bool, V.lasts_eq(a2), le, lasts_tails(r, xs, hl)) :
    {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(1n+pos, 1n), Bool.not(V.all_long(a2)))) == True{} : Bool}
  %Equal.sym(Bool, le, False{}, hln) : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(1n+pos, 1n), Bool.not(V.all_long(a2)))) == True{} : Bool}
  {==}

def good_l(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, c: V.Cur) -> Bool:
  match c:
    case V.Cur{+p, als}:
      match als:
        case Nil{}:
          False{}
        case +r <> +xs:
          Gd(seq, h, s, p, r, xs) && L.normalized(seq, B.Var{p, r, xs})

def left_ok(fuel: Nat, go: Bool, +seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +h: Q.Als(), +s: Nat,
  +hgo: {go == Bool.and(V.firsts_eq(r <> xs), V.all_long(r <> xs)) : Bool}, +hg: {Gd(seq, h, s, pos, r, xs) == True{} : Bool},
  +hst: {stopR(pos, r <> xs) == True{} : Bool}, +hf: {Nat.is_le(L.size(B.Var{pos, r, xs}), fuel) == True{} : Bool}) ->
  {good_l(seq, h, s, V.left(fuel, go, pos, r <> xs)) == True{} : Bool}:
  match fuel:
    case 0n:
      Empty.absurd({good_l(seq, h, s, V.left(0n, go, pos, r <> xs)) == True{} : Bool},
        P.false_ne_true(Q.le_trans(1n, L.size(B.Var{pos, r, xs}), 0n,
          size_pos(seq, pos, r, xs, gd_valid(seq, h, s, pos, r, xs, hg)), hf)))
    case 1n+(+f):
      match go:
        case False{}:
          Q.and_tt(Gd(seq, h, s, pos, r, xs), L.normalized(seq, B.Var{pos, r, xs}), hg,
            final_norm(seq, pos, r, xs, gd_valid(seq, h, s, pos, r, xs, hg), hst, hgo))
        case True{}:
          +hv = gd_valid(seq, h, s, pos, r, xs, hg)
          +hgo1 = Equal.sym(Bool, True{}, Bool.and(V.firsts_eq(r <> xs), V.all_long(r <> xs)), hgo)
          +hl = P.and_true_r(V.firsts_eq(r <> xs), V.all_long(r <> xs), hgo1)
          +r2 = List.tail(&2, B.Base, r)
          +xs2 = V.tails(xs)
          +p2 = {1n+pos : Nat}
          +s2 = L.size(B.Var{p2, r2, xs2})
          +hz = size_left(seq, pos, p2, r, xs, hv)
          +hg2 = gd_step(seq, h, s, p2, r2, xs2, pos, r, xs, hg,
            Q.fst(RP.Valid(seq, p2, r2, xs2), {L.haps(seq, B.Var{p2, r2, xs2}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()},
              SP.left_step(seq, pos, r, xs, hv, hgo1)),
            Q.snd(RP.Valid(seq, p2, r2, xs2), {L.haps(seq, B.Var{p2, r2, xs2}) == L.haps(seq, B.Var{pos, r, xs}) : Q.Als()},
              SP.left_step(seq, pos, r, xs, hv, hgo1)),
            Q.le_trans(s2, 1n+s2, L.size(B.Var{pos, r, xs}), Q.le_succ(s2), hz))
          left_ok(f, Bool.and(V.firsts_eq(r2 <> xs2), V.all_long(r2 <> xs2)), seq, p2, r2, xs2, h, s, {==}, hg2,
            stop_tails(pos, r, xs, hst, hl), Q.le_trans(1n+s2, L.size(B.Var{pos, r, xs}), 1n+f, hz, hf))

# The whole normalizer
# ====================

def good_f(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      match w:
        case B.Var{+p, +r, +xs}:
          Gd(seq, h, s, p, r, xs) && L.normalized(seq, B.Var{p, r, xs})

def lf(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, c: V.Cur, +e: {good_l(seq, h, s, c) == True{} : Bool}) ->
  {good_f(seq, h, s, Some{V.to_var(c)}) == True{} : Bool}:
  match c:
    case V.Cur{+p, als}:
      match als:
        case Nil{}:
          Empty.absurd({good_f(seq, h, s, Some{V.to_var(V.Cur{p, Nil{}})}) == True{} : Bool}, P.false_ne_true(e))
        case +r <> +xs:
          e

def main_r(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, V.Cur>, +e: {good_r(seq, h, s, m) == True{} : Bool}) ->
  {good_f(seq, h, s, V.left_of(m)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({good_f(seq, h, s, V.left_of(None{})) == True{} : Bool}, P.false_ne_true(e))
    case Some{c}:
      match c:
        case V.Cur{+p, als}:
          match als:
            case Nil{}:
              Empty.absurd({good_f(seq, h, s, V.left_of(Some{V.Cur{p, Nil{}}})) == True{} : Bool}, P.false_ne_true(e))
            case +r <> +xs:
              +hg = P.and_true_l(Gd(seq, h, s, p, r, xs), stopR(p, r <> xs), e)
              +hst = P.and_true_r(Gd(seq, h, s, p, r, xs), stopR(p, r <> xs), e)
              +fu = Nat.add(p, V.total(r <> xs))
              +go = Bool.and(V.firsts_eq(r <> xs), V.all_long(r <> xs))
              +hf = {%Equal.sym(Nat, V.total(xs), L.total(xs), ST.total_eq(xs)) :
                  {Nat.is_le(Nat.add(Q.len(r), L.total(xs)), Nat.add(p, Nat.add(Q.len(r), _))) == True{} : Bool};
                le_add_l(p, Nat.add(Q.len(r), L.total(xs))) : {Nat.is_le(L.size(B.Var{p, r, xs}), fu) == True{} : Bool}}
              lf(seq, h, s, V.left(fu, go, p, r <> xs), left_ok(fu, go, seq, p, r, xs, h, s, {==}, hg, hst, hf))

# For a valid v, the normalizer gives a valid, normalized variant making the
# same change, no bigger than v.
def main(+seq: Q.Bs(), +v: B.Var, +hv: {L.valid(seq, v) == True{} : Bool}) ->
  {good_f(seq, L.haps(seq, v), L.size(v), V.var_in(0n, seq, v)) == True{} : Bool}:
  match v:
    case B.Var{+pos, +ref, +alts}:
      +w = {B.Var{pos, ref, alts} : B.Var}
      +hh = L.haps(seq, w)
      +ss = L.size(w)
      +als = {ref <> alts : Q.Als()}
      +fu = Nat.add(pos, V.total(als))
      +hg0 = Q.and_tt(Bool.and(L.valid(seq, w), B.Alleles.eq(hh, hh)), Nat.is_le(ss, ss),
        Q.and_tt(L.valid(seq, w), B.Alleles.eq(hh, hh), hv, Q.alleles_refl(hh)), P.le_refl(ss))
      +hf0 = {%Equal.sym(Nat, V.total(alts), L.total(alts), ST.total_eq(alts)) :
          {Nat.is_le(Nat.add(pos, ss), Nat.add(pos, Nat.add(Q.len(ref), _))) == True{} : Bool};
        P.le_refl(Nat.add(pos, ss)) : {Nat.is_le(Nat.add(pos, ss), fu) == True{} : Bool}}
      main_r(seq, hh, ss, V.right(fu, V.next_act(0n, seq, pos, als), 0n, seq, pos, als),
        right_ok(fu, V.lasts_eq(als), V.all_long(als), Nat.is_le(2n, pos), V.Win.get(0n, seq, Nat.sub(pos, 2n)), seq, pos, ref, alts,
          hh, ss, {==}, {==}, {==}, {==}, hg0, hf0))
