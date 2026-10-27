import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q
import ./proof_var_code.bend as C

# The normalizer reading a window of the contig (bases = the len(bases)
# letters from off) against the whole contig. The window's answer, when it
# has one, agrees with the whole contig's (every base it reads is a base of
# the contig); and when the window holds every base the whole-contig run
# reads (indexes from pos_r - 1, pos_r the position after the right loop, up
# to before the input REF's end), it has one.

def Hb(+seq: Q.Bs(), +off: Nat, +bases: Q.Bs()) -> Data:
  {bases == L.slice(seq, off, L.len(bases)) : Q.Bs()}

# A base the window holds is the contig's base.
def win_agree.if(lt: Bool, +off: Nat, +bases: Q.Bs(), +seq: Q.Bs(), +i: Nat, +x: B.Base, +hb: Hb(seq, off, bases),
  +hl: {lt == Nat.is_lt(i, off) : Bool}, +h: {V.Win.get.if(lt, bases, off, i) == Some{x} : Maybe<&2, B.Base>}) ->
  {V.Win.get(0n, seq, i) == Some{x} : Maybe<&2, B.Base>}:
  match lt:
    case True{}:
      Empty.absurd({V.Win.get(0n, seq, i) == Some{x} : Maybe<&2, B.Base>}, Q.none_ne_some2(x, h))
    case False{}:
      +j = Nat.sub(i, off)
      +hle = Q.not_lt_le(i, off, Equal.sym(Bool, False{}, Nat.is_lt(i, off), hl))
      +h2 = {%hb : {List.get(&2, B.Base, _, j) == Some{x} : Maybe<&2, B.Base>}; h : {List.get(&2, B.Base, L.slice(seq, off, L.len(bases)), j) == Some{x} : Maybe<&2, B.Base>}}
      +h3 = Q.get_take_some(Q.drop(seq, off), L.len(bases), j, x, h2)
      +h4 = {%Q.get_drop(seq, off, j) : {_ == Some{x} : Maybe<&2, B.Base>}; h3 : {List.get(&2, B.Base, seq, Nat.add(off, j)) == Some{x} : Maybe<&2, B.Base>}}
      %Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)) : {V.Win.get.if(_, seq, 0n, i) == Some{x} : Maybe<&2, B.Base>}
      %Equal.sym(Nat, Nat.sub(i, 0n), i, P.sub_zero(i)) : {List.get(&2, B.Base, seq, _) == Some{x} : Maybe<&2, B.Base>}
      %Q.add_sub(off, i, hle) : {List.get(&2, B.Base, seq, _) == Some{x} : Maybe<&2, B.Base>}
      h4

def win_agree(+off: Nat, +bases: Q.Bs(), +seq: Q.Bs(), +i: Nat, +x: B.Base, +hb: Hb(seq, off, bases),
  +h: {V.Win.get(off, bases, i) == Some{x} : Maybe<&2, B.Base>}) -> {V.Win.get(0n, seq, i) == Some{x} : Maybe<&2, B.Base>}:
  win_agree.if(Nat.is_lt(i, off), off, bases, seq, i, x, hb, {==}, h)

# Inside the window, it reads like the contig.
def win_eq(+off: Nat, +bases: Q.Bs(), +seq: Q.Bs(), +i: Nat, +hb: Hb(seq, off, bases),
  +h1: {Nat.is_le(off, i) == True{} : Bool}, +h2: {Nat.is_le(1n+i, Nat.add(off, L.len(bases))) == True{} : Bool}) ->
  {V.Win.get(off, bases, i) == V.Win.get(0n, seq, i) : Maybe<&2, B.Base>}:
  +j = Nat.sub(i, off)
  +jb = Q.jbound(off, i, L.len(bases), h1, h2)
  %Equal.sym(Bool, Nat.is_lt(i, off), False{}, Q.le_not_lt(off, i, h1)) : {V.Win.get.if(_, bases, off, i) == V.Win.get(0n, seq, i) : Maybe<&2, B.Base>}
  %Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, P.lt_zero(i)) : {List.get(&2, B.Base, bases, j) == V.Win.get.if(_, seq, 0n, i) : Maybe<&2, B.Base>}
  %Equal.sym(Nat, Nat.sub(i, 0n), i, P.sub_zero(i)) : {List.get(&2, B.Base, bases, j) == List.get(&2, B.Base, seq, _) : Maybe<&2, B.Base>}
  %Equal.sym(Q.Bs(), bases, L.slice(seq, off, L.len(bases)), hb) : {List.get(&2, B.Base, _, j) == List.get(&2, B.Base, seq, i) : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, B.Base>, List.get(&2, B.Base, L.slice(seq, off, L.len(bases)), j), List.get(&2, B.Base, Q.drop(seq, off), j),
      Q.get_take(Q.drop(seq, off), L.len(bases), j, jb)) :
    {_ == List.get(&2, B.Base, seq, i) : Maybe<&2, B.Base>}
  %Equal.sym(Maybe<&2, B.Base>, List.get(&2, B.Base, Q.drop(seq, off), j), List.get(&2, B.Base, seq, Nat.add(off, j)), Q.get_drop(seq, off, j)) :
    {_ == List.get(&2, B.Base, seq, i) : Maybe<&2, B.Base>}
  %Q.add_sub(off, i, h1) : {List.get(&2, B.Base, seq, Nat.add(off, j)) == List.get(&2, B.Base, seq, _) : Maybe<&2, B.Base>}
  {==}

# Soundness: a window answer is the whole contig's answer
# =======================================================

def sim_sound(fuel: Nat, eq: Bool, lg: Bool, sh: Bool, b1: Maybe<&2, B.Base>, b2: Maybe<&2, B.Base>,
  +off: Nat, +bases: Q.Bs(), +seq: Q.Bs(), +pos: Nat, +als: Q.Als(), +c: V.Cur, +hb: Hb(seq, off, bases),
  +hb1: {b1 == V.Win.get(off, bases, Nat.sub(pos, 2n)) : Maybe<&2, B.Base>}, +hb2: {b2 == V.Win.get(0n, seq, Nat.sub(pos, 2n)) : Maybe<&2, B.Base>},
  +h: {V.right(fuel, V.next_act.if(eq, lg, sh, b1), off, bases, pos, als) == Some{c} : Maybe<&2, V.Cur>}) ->
  {V.right(fuel, V.next_act.if(eq, lg, sh, b2), 0n, seq, pos, als) == Some{c} : Maybe<&2, V.Cur>}:
  match fuel:
    case 0n:
      h
    case 1n+f:
      match eq:
        case False{}:
          h
        case True{}:
          match lg:
            case True{}:
              +a = V.inits(als)
              sim_sound(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)),
                V.Win.get(0n, seq, Nat.sub(pos, 2n)), off, bases, seq, pos, a, c, hb, {==}, {==}, h)
            case False{}:
              match sh:
                case False{}:
                  h
                case True{}:
                  match b1 b2:
                    case None{} _:
                      Empty.absurd({V.right(1n+f, V.next_act.if(True{}, False{}, True{}, b2), 0n, seq, pos, als) == Some{c} : Maybe<&2, V.Cur>},
                        Q.none_ne_some_c(V.Cur, c, h))
                    case Some{+x} None{}:
                      Empty.absurd({V.right(1n+f, V.ANeed{}, 0n, seq, pos, als) == Some{c} : Maybe<&2, V.Cur>},
                        Q.none_ne_some2(x, Equal.trans(Maybe<&2, B.Base>, None{}, V.Win.get(0n, seq, Nat.sub(pos, 2n)), Some{x}, hb2,
                          win_agree(off, bases, seq, Nat.sub(pos, 2n), x, hb, Equal.sym(Maybe<&2, B.Base>, Some{x}, V.Win.get(off, bases, Nat.sub(pos, 2n)), hb1)))))
                    case Some{+x} Some{+y}:
                      +exy = Q.some_inj(y, x, Equal.trans(Maybe<&2, B.Base>, Some{y}, V.Win.get(0n, seq, Nat.sub(pos, 2n)), Some{x}, hb2,
                        win_agree(off, bases, seq, Nat.sub(pos, 2n), x, hb, Equal.sym(Maybe<&2, B.Base>, Some{x}, V.Win.get(off, bases, Nat.sub(pos, 2n)), hb1))))
                      +p2 = Nat.sub(pos, 1n)
                      %Equal.sym(B.Base, y, x, exy) : {V.right(f, V.next_act(0n, seq, p2, V.shifted(_, als)), 0n, seq, p2, V.shifted(_, als)) == Some{c} : Maybe<&2, V.Cur>}
                      +a = V.shifted(x, als)
                      sim_sound(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(off, bases, Nat.sub(p2, 2n)),
                        V.Win.get(0n, seq, Nat.sub(p2, 2n)), off, bases, seq, p2, a, c, hb, {==}, {==}, h)

def lo(m1: Maybe<&2, V.Cur>, +m2: Maybe<&2, V.Cur>, +w: B.Var,
  rel: @c: V.Cur -> {m1 == Some{c} : Maybe<&2, V.Cur>} -> {m2 == Some{c} : Maybe<&2, V.Cur>},
  +h: {V.left_of(m1) == Some{w} : Maybe<&2, B.Var>}) -> {V.left_of(m2) == Some{w} : Maybe<&2, B.Var>}:
  match m1:
    case None{}:
      Empty.absurd({V.left_of(m2) == Some{w} : Maybe<&2, B.Var>}, Q.none_ne_some_c(B.Var, w, h))
    case Some{+c}:
      %Equal.sym(Maybe<&2, V.Cur>, m2, Some{c}, rel(c, {==})) : {V.left_of(_) == Some{w} : Maybe<&2, B.Var>}
      h

# Enough: the window run is the whole-contig run
# ==============================================

def cpos(m: Maybe<&2, V.Cur>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{c}:
      match c:
        case V.Cur{p, a}:
          p

# The position only moves left during the right loop.
def mono_r(fuel: Nat, eq: Bool, lg: Bool, sh: Bool, b: Maybe<&2, B.Base>, +off: Nat, +bases: Q.Bs(), +pos: Nat, +als: Q.Als()) ->
  {Nat.is_le(cpos(V.right(fuel, V.next_act.if(eq, lg, sh, b), off, bases, pos, als)), pos) == True{} : Bool}:
  match fuel:
    case 0n:
      P.le_refl(pos)
    case 1n+(+f):
      match eq:
        case False{}:
          P.le_refl(pos)
        case True{}:
          match lg:
            case True{}:
              +a = V.inits(als)
              mono_r(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)), off, bases, pos, a)
            case False{}:
              match sh:
                case False{}:
                  P.le_refl(pos)
                case True{}:
                  match b:
                    case None{}:
                      P.le_zero_l(pos)
                    case Some{+x}:
                      +p2 = Nat.sub(pos, 1n)
                      +a = V.shifted(x, als)
                      Q.le_trans(cpos(V.right(f, V.next_act(off, bases, p2, a), off, bases, p2, a)), p2, pos,
                        mono_r(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(off, bases, Nat.sub(p2, 2n)), off, bases, p2, a),
                        Q.sub1_le(pos))

def sim_eq(fuel: Nat, eq: Bool, lg: Bool, sh: Bool, b1: Maybe<&2, B.Base>, b2: Maybe<&2, B.Base>,
  +off: Nat, +bases: Q.Bs(), +seq: Q.Bs(), +pos: Nat, +als: Q.Als(), +hb: Hb(seq, off, bases),
  +hs: {sh == Nat.is_le(2n, pos) : Bool},
  +hb1: {b1 == V.Win.get(off, bases, Nat.sub(pos, 2n)) : Maybe<&2, B.Base>}, +hb2: {b2 == V.Win.get(0n, seq, Nat.sub(pos, 2n)) : Maybe<&2, B.Base>},
  +hlo: {Nat.is_le(off, Nat.sub(cpos(V.right(fuel, V.next_act.if(eq, lg, sh, b2), 0n, seq, pos, als)), 1n)) == True{} : Bool},
  +hup: {Nat.is_le(pos, Nat.add(off, L.len(bases))) == True{} : Bool}) ->
  {V.right(fuel, V.next_act.if(eq, lg, sh, b1), off, bases, pos, als) == V.right(fuel, V.next_act.if(eq, lg, sh, b2), 0n, seq, pos, als) : Maybe<&2, V.Cur>}:
  match fuel:
    case 0n:
      {==}
    case 1n+(+f):
      match eq:
        case False{}:
          {==}
        case True{}:
          match lg:
            case True{}:
              +a = V.inits(als)
              sim_eq(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)),
                V.Win.get(0n, seq, Nat.sub(pos, 2n)), off, bases, seq, pos, a, hb, {==}, {==}, {==}, hlo, hup)
            case False{}:
              match sh:
                case False{}:
                  {==}
                case True{}:
                  match b1 b2:
                    case None{} None{}:
                      {==}
                    case None{} Some{+y}:
                      +i = Nat.sub(pos, 2n)
                      +p2 = Nat.sub(pos, 1n)
                      +a = V.shifted(y, als)
                      +hs1 = Equal.sym(Bool, True{}, Nat.is_le(2n, pos), hs)
                      +hm = mono_r(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(0n, seq, Nat.sub(p2, 2n)), 0n, seq, p2, a)
                      +hi = Q.le_trans(off, Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), i, hlo,
                        {%Q.sub_sub_one(pos) : {Nat.is_le(Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), _) == True{} : Bool};
                          Q.sub1_mono(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), p2, hm)
                          : {Nat.is_le(Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), i) == True{} : Bool}})
                      +hi2 = Q.le_trans(1n+i, pos, Nat.add(off, L.len(bases)), Q.sub2_lt(pos, hs1), hup)
                      Empty.absurd({V.right(1n+f, V.ANeed{}, off, bases, pos, als) == V.right(1n+f, V.AShift{y}, 0n, seq, pos, als) : Maybe<&2, V.Cur>},
                        Q.none_ne_some_c(B.Base, y, Equal.trans(Maybe<&2, B.Base>, None{}, V.Win.get(off, bases, i), Some{y}, hb1,
                          Equal.trans(Maybe<&2, B.Base>, V.Win.get(off, bases, i), V.Win.get(0n, seq, i), Some{y}, win_eq(off, bases, seq, i, hb, hi, hi2),
                            Equal.sym(Maybe<&2, B.Base>, Some{y}, V.Win.get(0n, seq, i), hb2)))))
                    case Some{+x} None{}:
                      +i = Nat.sub(pos, 2n)
                      +hs1 = Equal.sym(Bool, True{}, Nat.is_le(2n, pos), hs)
                      +hi = Q.le_trans(off, 0n, i, hlo, P.le_zero_l(i))
                      +hi2 = Q.le_trans(1n+i, pos, Nat.add(off, L.len(bases)), Q.sub2_lt(pos, hs1), hup)
                      Empty.absurd({V.right(1n+f, V.AShift{x}, off, bases, pos, als) == V.right(1n+f, V.ANeed{}, 0n, seq, pos, als) : Maybe<&2, V.Cur>},
                        Q.none_ne_some_c(B.Base, x, Equal.trans(Maybe<&2, B.Base>, None{}, V.Win.get(0n, seq, i), Some{x}, hb2,
                          Equal.trans(Maybe<&2, B.Base>, V.Win.get(0n, seq, i), V.Win.get(off, bases, i), Some{x},
                            Equal.sym(Maybe<&2, B.Base>, V.Win.get(off, bases, i), V.Win.get(0n, seq, i), win_eq(off, bases, seq, i, hb, hi, hi2)),
                            Equal.sym(Maybe<&2, B.Base>, Some{x}, V.Win.get(off, bases, i), hb1)))))
                    case Some{+x} Some{+y}:
                      +i = Nat.sub(pos, 2n)
                      +p2 = Nat.sub(pos, 1n)
                      +a = V.shifted(y, als)
                      +hs1 = Equal.sym(Bool, True{}, Nat.is_le(2n, pos), hs)
                      +hm = mono_r(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(0n, seq, Nat.sub(p2, 2n)), 0n, seq, p2, a)
                      +hi = Q.le_trans(off, Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), i, hlo,
                        {%Q.sub_sub_one(pos) : {Nat.is_le(Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), _) == True{} : Bool};
                          Q.sub1_mono(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), p2, hm)
                          : {Nat.is_le(Nat.sub(cpos(V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a)), 1n), i) == True{} : Bool}})
                      +hi2 = Q.le_trans(1n+i, pos, Nat.add(off, L.len(bases)), Q.sub2_lt(pos, hs1), hup)
                      +exy = Q.some_inj(x, y, Equal.trans(Maybe<&2, B.Base>, Some{x}, V.Win.get(off, bases, i), Some{y}, hb1,
                        Equal.trans(Maybe<&2, B.Base>, V.Win.get(off, bases, i), V.Win.get(0n, seq, i), Some{y}, win_eq(off, bases, seq, i, hb, hi, hi2),
                          Equal.sym(Maybe<&2, B.Base>, Some{y}, V.Win.get(0n, seq, i), hb2))))
                      %Equal.sym(B.Base, x, y, exy) :
                        {V.right(f, V.next_act(off, bases, p2, V.shifted(_, als)), off, bases, p2, V.shifted(_, als)) == V.right(f, V.next_act(0n, seq, p2, a), 0n, seq, p2, a) : Maybe<&2, V.Cur>}
                      sim_eq(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(off, bases, Nat.sub(p2, 2n)),
                        V.Win.get(0n, seq, Nat.sub(p2, 2n)), off, bases, seq, p2, a, hb, {==}, {==}, {==}, hlo,
                        Q.le_trans(p2, pos, Nat.add(off, L.len(bases)), Q.sub1_le(pos), hup))

# After a shift the right loop never trims again, so the left loop does not
# move: the position after the right loop is the input POS, or some allele
# is short.

def short_one(+x: B.Base, +a: Q.Bs(), +h: {Nat.is_le(2n, Q.len(a)) == False{} : Bool}) ->
  {Nat.is_le(2n, Q.len(x <> V.init(a))) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +g <> +u:
      %Q.len_init_r(g, u) : {Nat.is_le(2n, 1n+_) == False{} : Bool}
      h

def short_cons(bv: Bool, +x: B.Base, +a: Q.Bs(), +t: Q.Als(), +hbv: {bv == Nat.is_le(2n, Q.len(a)) : Bool},
  +h: {Bool.and(Nat.is_le(2n, Q.len(a)), V.all_long(t)) == False{} : Bool},
  ih: {V.all_long(t) == False{} : Bool} -> {V.all_long(V.shifted(x, t)) == False{} : Bool}) ->
  {Bool.and(Nat.is_le(2n, Q.len(x <> V.init(a))), V.all_long(V.shifted(x, t))) == False{} : Bool}:
  match bv:
    case False{}:
      %Equal.sym(Bool, Nat.is_le(2n, Q.len(x <> V.init(a))), False{}, short_one(x, a, Equal.sym(Bool, False{}, Nat.is_le(2n, Q.len(a)), hbv))) :
        {Bool.and(_, V.all_long(V.shifted(x, t))) == False{} : Bool}
      {==}
    case True{}:
      +ht = {%Equal.sym(Bool, True{}, Nat.is_le(2n, Q.len(a)), hbv) : {Bool.and(_, V.all_long(t)) == False{} : Bool};
        h : {V.all_long(t) == False{} : Bool}}
      %Equal.sym(Bool, V.all_long(V.shifted(x, t)), False{}, ih(ht)) : {Bool.and(Nat.is_le(2n, Q.len(x <> V.init(a))), _) == False{} : Bool}
      P.and_false_r(Nat.is_le(2n, Q.len(x <> V.init(a))))

def short_shifted(+x: B.Base, +als: Q.Als(), +h: {V.all_long(als) == False{} : Bool}) -> {V.all_long(V.shifted(x, als)) == False{} : Bool}:
  match als:
    case Nil{}:
      Empty.absurd({V.all_long(V.shifted(x, Nil{})) == False{} : Bool}, P.true_ne_false(h))
    case +a <> +t:
      short_cons(Nat.is_le(2n, Q.len(a)), x, a, t, {==}, h, e => short_shifted(x, t, e))

def shape(m: Maybe<&2, V.Cur>, +pos0: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      match c:
        case V.Cur{+p, +a}:
          Nat.is_eq(p, pos0) || Bool.not(V.all_long(a))

def right_shape(fuel: Nat, eq: Bool, lg: Bool, sh: Bool, b: Maybe<&2, B.Base>, +off: Nat, +bases: Q.Bs(), +pos: Nat, +als: Q.Als(),
  +pos0: Nat, +hl: {lg == V.all_long(als) : Bool}, +hinv: {Bool.or(Nat.is_eq(pos, pos0), Bool.not(V.all_long(als))) == True{} : Bool}) ->
  {shape(V.right(fuel, V.next_act.if(eq, lg, sh, b), off, bases, pos, als), pos0) == True{} : Bool}:
  match fuel:
    case 0n:
      hinv
    case 1n+f:
      match eq:
        case False{}:
          hinv
        case True{}:
          match lg:
            case True{}:
              +a = V.inits(als)
              +h1 = {%Equal.sym(Bool, True{}, V.all_long(als), hl) : {Bool.or(Nat.is_eq(pos, pos0), Bool.not(_)) == True{} : Bool};
                hinv : {Bool.or(Nat.is_eq(pos, pos0), False{}) == True{} : Bool}}
              +h2 = {%P.or_false_r(Nat.is_eq(pos, pos0)) : {_ == True{} : Bool}; h1 : {Nat.is_eq(pos, pos0) == True{} : Bool}}
              right_shape(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, pos), V.Win.get(off, bases, Nat.sub(pos, 2n)), off, bases, pos, a, pos0,
                {==}, Q.or_tt_l(Nat.is_eq(pos, pos0), Bool.not(V.all_long(a)), h2))
            case False{}:
              match sh:
                case False{}:
                  hinv
                case True{}:
                  match b:
                    case None{}:
                      {==}
                    case Some{+x}:
                      +p2 = Nat.sub(pos, 1n)
                      +a = V.shifted(x, als)
                      +ns = {%Equal.sym(Bool, V.all_long(a), False{}, short_shifted(x, als, Equal.sym(Bool, False{}, V.all_long(als), hl))) :
                          {Bool.not(_) == True{} : Bool};
                        {==} : {Bool.not(V.all_long(a)) == True{} : Bool}}
                      right_shape(f, V.lasts_eq(a), V.all_long(a), Nat.is_le(2n, p2), V.Win.get(off, bases, Nat.sub(p2, 2n)), off, bases, p2, a, pos0,
                        {==}, Q.or_tt_r(Nat.is_eq(p2, pos0), Bool.not(V.all_long(a)), ns))

def left_false(fuel: Nat, +p: Nat, +a: Q.Als()) -> {V.left(fuel, False{}, p, a) == V.Cur{p, a} : V.Cur}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

def pos_to_var(+p: Nat, +a: Q.Als()) -> {L.pos_of(V.to_var(V.Cur{p, a})) == p : Nat}:
  match a:
    case Nil{}:
      {==}
    case r <> t:
      {==}

# off <= pos_r - 1, from "covers" and the shape of the right loop's result.
def hlo_case(e: Bool, +off: Nat, +pos: Nat, +p: Nat, +a: Q.Als(), +v: B.Var, +he: {e == Nat.is_eq(p, pos) : Bool},
  +hsh: {Bool.or(Nat.is_eq(p, pos), Bool.not(V.all_long(a))) == True{} : Bool},
  +hc: {Nat.is_le(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(L.pos_of(Maybe.default(&2, B.Var, V.left_of(Some{V.Cur{p, a}}), v)), 2n))) == True{} : Bool}) ->
  {Nat.is_le(off, Nat.sub(p, 1n)) == True{} : Bool}:
  match e:
    case True{}:
      +ep = P.eq_sound(p, pos, Equal.sym(Bool, True{}, Nat.is_eq(p, pos), he))
      %Equal.sym(Nat, p, pos, ep) : {Nat.is_le(off, Nat.sub(_, 1n)) == True{} : Bool}
      Q.le_trans(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(L.pos_of(Maybe.default(&2, B.Var, V.left_of(Some{V.Cur{p, a}}), v)), 2n)), Nat.sub(pos, 1n), hc,
        Q.min_le_l(Nat.sub(pos, 1n), Nat.sub(L.pos_of(Maybe.default(&2, B.Var, V.left_of(Some{V.Cur{p, a}}), v)), 2n)))
    case False{}:
      +al = V.all_long(a)
      +fu = Nat.add(p, V.total(a))
      +hal = P.not_true(al, {%Equal.sym(Bool, False{}, Nat.is_eq(p, pos), he) : {Bool.or(_, Bool.not(al)) == True{} : Bool};
        hsh : {Bool.not(al) == True{} : Bool}})
      +hpf = {
        %Equal.sym(Bool, al, False{}, hal) : {L.pos_of(V.to_var(V.left(fu, Bool.and(V.firsts_eq(a), _), p, a))) == p : Nat}
        %Equal.sym(Bool, Bool.and(V.firsts_eq(a), False{}), False{}, P.and_false_r(V.firsts_eq(a))) : {L.pos_of(V.to_var(V.left(fu, _, p, a))) == p : Nat}
        %Equal.sym(V.Cur, V.left(fu, False{}, p, a), V.Cur{p, a}, left_false(fu, p, a)) : {L.pos_of(V.to_var(_)) == p : Nat}
        pos_to_var(p, a) : {L.pos_of(Maybe.default(&2, B.Var, V.left_of(Some{V.Cur{p, a}}), v)) == p : Nat}}
      +hc2 = {%hpf : {Nat.is_le(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(_, 2n))) == True{} : Bool};
        hc : {Nat.is_le(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(p, 2n))) == True{} : Bool}}
      Q.le_trans(off, Nat.sub(p, 2n), Nat.sub(p, 1n),
        Q.le_trans(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(p, 2n)), Nat.sub(p, 2n), hc2, Q.min_le_r(Nat.sub(pos, 1n), Nat.sub(p, 2n))),
        Q.sub2_le_sub1(p))

def hlo_of(m: Maybe<&2, V.Cur>, +off: Nat, +pos: Nat, +v: B.Var, +hsm: {Maybe.is_some(&2, V.Cur, m) == True{} : Bool},
  +hsh: {shape(m, pos) == True{} : Bool},
  +hc: {Nat.is_le(off, Nat.min(Nat.sub(pos, 1n), Nat.sub(L.pos_of(Maybe.default(&2, B.Var, V.left_of(m), v)), 2n))) == True{} : Bool}) ->
  {Nat.is_le(off, Nat.sub(cpos(m), 1n)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_le(off, Nat.sub(0n, 1n)) == True{} : Bool}, P.false_ne_true(hsm))
    case Some{c}:
      match c:
        case V.Cur{+p, +a}:
          hlo_case(Nat.is_eq(p, pos), off, pos, p, a, v, {==}, hsh, hc)

def gf_some(+seq: Q.Bs(), +h: Q.Als(), +s: Nat, m: Maybe<&2, B.Var>, +e: {C.good_f(seq, h, s, m) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Var, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&2, B.Var, None{}) == True{} : Bool}, P.false_ne_true(e))
    case Some{w}:
      {==}

def lo_some(m: Maybe<&2, V.Cur>, +e: {Maybe.is_some(&2, B.Var, V.left_of(m)) == True{} : Bool}) -> {Maybe.is_some(&2, V.Cur, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&2, V.Cur, None{}) == True{} : Bool}, P.false_ne_true(e))
    case Some{c}:
      {==}

# pos <= off + n, from "covers" (pos - 1 + len(REF) <= off + n, REF non-empty).
def hup_of(+pos: Nat, +rl: Nat, +k: Nat, +h1: {Nat.is_le(1n, pos) == True{} : Bool}, +h2: {Nat.is_le(1n, rl) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(Nat.sub(pos, 1n), rl), k) == True{} : Bool}) -> {Nat.is_le(pos, k) == True{} : Bool}:
  +x = Nat.sub(pos, 1n)
  %Q.succ_sub_one(pos, h1) : {Nat.is_le(_, k) == True{} : Bool}
  Q.le_trans(1n+x, Nat.add(x, rl), k,
    {%P.add_one(x) : {Nat.is_le(_, Nat.add(x, rl)) == True{} : Bool};
      P.le_add(x, x, 1n, rl, P.le_refl(x), h2) : {Nat.is_le(1n+x, Nat.add(x, rl)) == True{} : Bool}},
    hc)
