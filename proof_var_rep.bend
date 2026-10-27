import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var_lists.bend as Q

# A valid variant as a cut of the contig: seq = A ++ REF ++ B, with A the
# pos - 1 bases before it; each alternative's contig is then A ++ alt ++ B.
# Cut equations are oriented for rewriting: es : {A ++ (REF ++ B) == seq},
# el : {len(A) == pos - 1}.

def hmap(+a: Q.Bs(), +b: Q.Bs(), xs: Q.Als()) -> Q.Als():
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      Q.app(a, Q.app(x, b)) <> hmap(a, b, t)

def len_hmap(+a: Q.Bs(), +b: Q.Bs(), +xs: Q.Als()) ->
  {List.length(&2, List<&2, B.Base>, hmap(a, b, xs)) == List.length(&2, List<&2, B.Base>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %len_hmap(a, b, t) : {1n+List.length(&2, List<&2, B.Base>, hmap(a, b, t)) == 1n+_ : Nat}
      {==}

def apply_rep(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +x: Q.Bs(), +a: Q.Bs(), +b: Q.Bs(),
  +es: {Q.app(a, Q.app(r, b)) == seq : Q.Bs()}, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}) ->
  {L.apply(seq, pos, r, x) == Q.app(a, Q.app(x, b)) : Q.Bs()}:
  %el : {Q.app(Q.take(seq, _), Q.app(x, Q.drop(seq, Nat.add(_, Q.len(r))))) == Q.app(a, Q.app(x, b)) : Q.Bs()}
  %es : {Q.app(Q.take(_, Q.len(a)), Q.app(x, Q.drop(_, Nat.add(Q.len(a), Q.len(r))))) == Q.app(a, Q.app(x, b)) : Q.Bs()}
  %Q.take_app0_r(a, Q.app(r, b)) : {Q.app(_, Q.app(x, Q.drop(Q.app(a, Q.app(r, b)), Nat.add(Q.len(a), Q.len(r))))) == Q.app(a, Q.app(x, b)) : Q.Bs()}
  %Q.drop_app_r(a, Q.app(r, b), Q.len(r)) : {Q.app(a, Q.app(x, _)) == Q.app(a, Q.app(x, b)) : Q.Bs()}
  %Q.drop_app0_r(r, b) : {Q.app(a, Q.app(x, _)) == Q.app(a, Q.app(x, b)) : Q.Bs()}
  {==}

def haps_rep(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +a: Q.Bs(), +b: Q.Bs(),
  +es: {Q.app(a, Q.app(r, b)) == seq : Q.Bs()}, +el: {Q.len(a) == Nat.sub(pos, 1n) : Nat}, +xs: Q.Als()) ->
  {L.haps.go(seq, pos, r, xs) == hmap(a, b, xs) : Q.Als()}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Q.acons_eq(L.apply(seq, pos, r, x), L.haps.go(seq, pos, r, t), Q.app(a, Q.app(x, b)), hmap(a, b, t),
        apply_rep(seq, pos, r, x, a, b, es, el), haps_rep(seq, pos, r, a, b, es, el, t))

# Validity, piece by piece
# ========================

def k1(+pos: Nat) -> Bool:
  Nat.is_le(1n, pos)

def k2(+r: Q.Bs()) -> Bool:
  Nat.is_le(1n, L.len(r))

def k3(+xs: Q.Als()) -> Bool:
  Nat.is_le(1n, List.length(&2, List<&2, B.Base>, xs))

def k4(+xs: Q.Als()) -> Bool:
  L.all_nonempty(xs)

def k5(+r: Q.Bs(), +xs: Q.Als()) -> Bool:
  B.Alleles.distinct(r <> xs)

def k6(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs()) -> Bool:
  B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(r)), r)

def u2(+pos: Nat, +r: Q.Bs()) -> Bool:
  k1(pos) && k2(r)

def u3(+pos: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Bool:
  u2(pos, r) && k3(xs)

def u4(+pos: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Bool:
  u3(pos, r, xs) && k4(xs)

def u5(+pos: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Bool:
  u4(pos, r, xs) && k5(r, xs)

def Valid(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als()) -> Data:
  {L.valid(seq, B.Var{pos, r, xs}) == True{} : Bool}

def vu5(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {u5(pos, r, xs) == True{} : Bool}:
  P.and_true_l(u5(pos, r, xs), k6(seq, pos, r), hv)

def vk6(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k6(seq, pos, r) == True{} : Bool}:
  P.and_true_r(u5(pos, r, xs), k6(seq, pos, r), hv)

def vu4(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {u4(pos, r, xs) == True{} : Bool}:
  P.and_true_l(u4(pos, r, xs), k5(r, xs), vu5(seq, pos, r, xs, hv))

def vk5(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k5(r, xs) == True{} : Bool}:
  P.and_true_r(u4(pos, r, xs), k5(r, xs), vu5(seq, pos, r, xs, hv))

def vu3(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {u3(pos, r, xs) == True{} : Bool}:
  P.and_true_l(u3(pos, r, xs), k4(xs), vu4(seq, pos, r, xs, hv))

def vk4(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k4(xs) == True{} : Bool}:
  P.and_true_r(u3(pos, r, xs), k4(xs), vu4(seq, pos, r, xs, hv))

def vu2(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {u2(pos, r) == True{} : Bool}:
  P.and_true_l(u2(pos, r), k3(xs), vu3(seq, pos, r, xs, hv))

def vk3(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k3(xs) == True{} : Bool}:
  P.and_true_r(u2(pos, r), k3(xs), vu3(seq, pos, r, xs, hv))

def vk2(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k2(r) == True{} : Bool}:
  P.and_true_r(k1(pos), k2(r), vu2(seq, pos, r, xs, hv))

def vk1(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) -> {k1(pos) == True{} : Bool}:
  P.and_true_l(k1(pos), k2(r), vu2(seq, pos, r, xs, hv))

def mk_valid(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(),
  e1: {k1(pos) == True{} : Bool}, e2: {k2(r) == True{} : Bool}, e3: {k3(xs) == True{} : Bool},
  e4: {k4(xs) == True{} : Bool}, e5: {k5(r, xs) == True{} : Bool}, e6: {k6(seq, pos, r) == True{} : Bool}) ->
  Valid(seq, pos, r, xs):
  Q.and_tt(u5(pos, r, xs), k6(seq, pos, r),
    Q.and_tt(u4(pos, r, xs), k5(r, xs),
      Q.and_tt(u3(pos, r, xs), k4(xs),
        Q.and_tt(u2(pos, r), k3(xs), Q.and_tt(k1(pos), k2(r), e1, e2), e3), e4), e5), e6)

# The cut of a valid variant
# ==========================

def vA(+seq: Q.Bs(), +pos: Nat) -> Q.Bs():
  Q.take(seq, Nat.sub(pos, 1n))

def vB(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs()) -> Q.Bs():
  Q.drop(seq, Nat.add(Nat.sub(pos, 1n), Q.len(r)))

def valid_drop(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) ->
  {Q.drop(seq, Nat.sub(pos, 1n)) == Q.app(r, vB(seq, pos, r)) : Q.Bs()}:
  +x = Nat.sub(pos, 1n)
  +hs = Q.bases_sound(L.slice(seq, x, L.len(r)), r, vk6(seq, pos, r, xs, hv))
  %hs : {Q.drop(seq, x) == Q.app(_, Q.drop(seq, Nat.add(x, Q.len(r)))) : Q.Bs()}
  %Q.drop_drop(seq, x, Q.len(r)) : {Q.drop(seq, x) == Q.app(Q.take(Q.drop(seq, x), Q.len(r)), _) : Q.Bs()}
  Q.take_drop_r(Q.drop(seq, x), Q.len(r))

def valid_es(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), hv: Valid(seq, pos, r, xs)) ->
  {Q.app(vA(seq, pos), Q.app(r, vB(seq, pos, r))) == seq : Q.Bs()}:
  %valid_drop(seq, pos, r, xs, hv) : {Q.app(vA(seq, pos), _) == seq : Q.Bs()}
  Q.take_drop(seq, Nat.sub(pos, 1n))

def valid_el(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: Valid(seq, pos, r, xs)) ->
  {Q.len(vA(seq, pos)) == Nat.sub(pos, 1n) : Nat}:
  match r:
    case Nil{}:
      Empty.absurd({Q.len(vA(seq, pos)) == Nat.sub(pos, 1n) : Nat}, P.false_ne_true(vk2(seq, pos, Nil{}, xs, hv)))
    case +g <> +u:
      Q.len_take_of(seq, Nat.sub(pos, 1n), g, Q.app(u, vB(seq, pos, g <> u)), valid_drop(seq, pos, g <> u, xs, hv))

def valid_haps(+seq: Q.Bs(), +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: Valid(seq, pos, r, xs)) ->
  {L.haps(seq, B.Var{pos, r, xs}) == hmap(vA(seq, pos), vB(seq, pos, r), xs) : Q.Als()}:
  haps_rep(seq, pos, r, vA(seq, pos), vB(seq, pos, r), valid_es(seq, pos, r, xs, hv), valid_el(seq, pos, r, xs, hv), xs)

# Distinct alleles, through a cut
# ===============================

def frame_eq(+a: Q.Bs(), +b: Q.Bs(), +x: Q.Bs(), +y: Q.Bs()) ->
  {B.Bases.eq(Q.app(a, Q.app(x, b)), Q.app(a, Q.app(y, b))) == B.Bases.eq(x, y) : Bool}:
  Q.bool_ext(B.Bases.eq(Q.app(a, Q.app(x, b)), Q.app(a, Q.app(y, b))), B.Bases.eq(x, y),
    e => %Q.cancel_r(x, y, b, Q.cancel_l(a, Q.app(x, b), Q.app(y, b),
           Q.bases_sound(Q.app(a, Q.app(x, b)), Q.app(a, Q.app(y, b)), e))) : {B.Bases.eq(x, _) == True{} : Bool};
         Q.bases_refl(x),
    e => %Q.bases_sound(x, y, e) : {B.Bases.eq(Q.app(a, Q.app(x, b)), Q.app(a, Q.app(_, b))) == True{} : Bool};
         Q.bases_refl(Q.app(a, Q.app(x, b))))

def member_frame(+a: Q.Bs(), +b: Q.Bs(), +x: Q.Bs(), +ys: Q.Als()) ->
  {B.Alleles.member(Q.app(a, Q.app(x, b)), hmap(a, b, ys)) == B.Alleles.member(x, ys) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(Bool, B.Bases.eq(Q.app(a, Q.app(x, b)), Q.app(a, Q.app(y, b))), B.Bases.eq(x, y), frame_eq(a, b, x, y)) :
        {Bool.or(_, B.Alleles.member(Q.app(a, Q.app(x, b)), hmap(a, b, t))) == B.Alleles.member(x, y <> t) : Bool}
      %Equal.sym(Bool, B.Alleles.member(Q.app(a, Q.app(x, b)), hmap(a, b, t)), B.Alleles.member(x, t), member_frame(a, b, x, t)) :
        {Bool.or(B.Bases.eq(x, y), _) == B.Alleles.member(x, y <> t) : Bool}
      {==}

def distinct_frame(+a: Q.Bs(), +b: Q.Bs(), +xs: Q.Als()) ->
  {B.Alleles.distinct(hmap(a, b, xs)) == B.Alleles.distinct(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Bool, B.Alleles.member(Q.app(a, Q.app(x, b)), hmap(a, b, t)), B.Alleles.member(x, t), member_frame(a, b, x, t)) :
        {Bool.and(Bool.not(_), B.Alleles.distinct(hmap(a, b, t))) == B.Alleles.distinct(x <> t) : Bool}
      %Equal.sym(Bool, B.Alleles.distinct(hmap(a, b, t)), B.Alleles.distinct(t), distinct_frame(a, b, t)) :
        {Bool.and(Bool.not(B.Alleles.member(x, t)), _) == B.Alleles.distinct(x <> t) : Bool}
      {==}

def dist_of_rep(+seq: Q.Bs(), +a: Q.Bs(), +r: Q.Bs(), +b: Q.Bs(), +xs: Q.Als(), +es: {Q.app(a, Q.app(r, b)) == seq : Q.Bs()}) ->
  {B.Alleles.distinct(r <> xs) == B.Alleles.distinct(seq <> hmap(a, b, xs)) : Bool}:
  %es : {B.Alleles.distinct(r <> xs) == B.Alleles.distinct(_ <> hmap(a, b, xs)) : Bool}
  Equal.sym(Bool, B.Alleles.distinct(hmap(a, b, r <> xs)), B.Alleles.distinct(r <> xs), distinct_frame(a, b, r <> xs))

# A cut of the contig making the same changes as a valid variant is valid.
def valid_of_rep(+seq: Q.Bs(), +pos2: Nat, +r2: Q.Bs(), +xs2: Q.Als(), +a2: Q.Bs(), +b2: Q.Bs(),
  +es2: {Q.app(a2, Q.app(r2, b2)) == seq : Q.Bs()}, +el2: {Q.len(a2) == Nat.sub(pos2, 1n) : Nat},
  h1: {k1(pos2) == True{} : Bool}, h2: {k2(r2) == True{} : Bool}, h4: {k4(xs2) == True{} : Bool},
  +pos: Nat, +r: Q.Bs(), +xs: Q.Als(), +hv: Valid(seq, pos, r, xs),
  +hh: {hmap(a2, b2, xs2) == hmap(vA(seq, pos), vB(seq, pos, r), xs) : Q.Als()}) ->
  Valid(seq, pos2, r2, xs2):
  +hh_r = Equal.sym(Q.Als(), hmap(a2, b2, xs2), hmap(vA(seq, pos), vB(seq, pos, r), xs), hh)
  +e3 = {
    %len_hmap(a2, b2, xs2) : {Nat.is_le(1n, _) == True{} : Bool}
    %hh_r : {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, _)) == True{} : Bool}
    %Equal.sym(Nat, List.length(&2, List<&2, B.Base>, hmap(vA(seq, pos), vB(seq, pos, r), xs)), List.length(&2, List<&2, B.Base>, xs),
      len_hmap(vA(seq, pos), vB(seq, pos, r), xs)) : {Nat.is_le(1n, _) == True{} : Bool}
    vk3(seq, pos, r, xs, hv) : {k3(xs2) == True{} : Bool}}
  +e5 = {
    %Equal.sym(Bool, B.Alleles.distinct(r2 <> xs2), B.Alleles.distinct(seq <> hmap(a2, b2, xs2)), dist_of_rep(seq, a2, r2, b2, xs2, es2)) :
      {_ == True{} : Bool}
    %hh_r : {B.Alleles.distinct(seq <> _) == True{} : Bool}
    %dist_of_rep(seq, vA(seq, pos), r, vB(seq, pos, r), xs, valid_es(seq, pos, r, xs, hv)) : {_ == True{} : Bool}
    vk5(seq, pos, r, xs, hv) : {k5(r2, xs2) == True{} : Bool}}
  +e6 = {
    %el2 : {B.Bases.eq(L.slice(seq, _, L.len(r2)), r2) == True{} : Bool}
    %es2 : {B.Bases.eq(L.slice(_, Q.len(a2), L.len(r2)), r2) == True{} : Bool}
    %Q.drop_app0_r(a2, Q.app(r2, b2)) : {B.Bases.eq(List.take(&2, B.Base, _, L.len(r2)), r2) == True{} : Bool}
    %Q.take_app0_r(r2, b2) : {B.Bases.eq(_, r2) == True{} : Bool}
    Q.bases_refl(r2) : {k6(seq, pos2, r2) == True{} : Bool}}
  mk_valid(seq, pos2, r2, xs2, h1, h2, e3, h4, e5, e6)
