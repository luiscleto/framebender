import Base
import ./bytes_enc.bend as E
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-words@0.1.0.0/proof_bytes.bend as Y
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_seq.bend as SQ
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Helpers for proof_b_enc.bend: list facts about codes, words and padding,
# and the bounds on E.depth. Every variable is reusable.

# Text and codes
# ==============

law length_codes:
  for +s: String
  {String.length(s) == List.length(&2, U32, E.codes(s)) : Nat}

def length_codes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %length_codes(t) : {1n+String.length(t) == 1n+_ : Nat}
      {==}

law bytes_codes:
  for +s: String
  {D.all_bytes(E.codes(s)) == E.is_bytes(s) : Bool}

def bytes_codes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          %bytes_codes(t) : {Bool.and(U32.is_lt(x, 256), D.all_bytes(E.codes(t))) == Bool.and(U32.is_lt(x, 256), _) : Bool}
          {==}

law chars_codes1:
  for +s: String
  {E.chars(E.codes(s)) == s : String}

def chars_codes1(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          %chars_codes1(t) : {SCon{Chr{x}, E.chars(E.codes(t))} == SCon{Chr{x}, _} : String}
          {==}

# Lists
# =====

law append_assoc:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}

def append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %append_assoc(t, ys, zs) :
        {x <> List.append(&2, U32, List.append(&2, U32, t, ys), zs) == x <> _ : List<&2, U32>}
      {==}

law take_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.take(&2, U32, List.append(&2, U32, xs, ys), List.length(&2, U32, xs)) == xs : List<&2, U32>}

def take_app(xs, ys):
  match xs:
    case Nil{}:
      SQ.take_zero(ys)
    case Con{x, t}:
      %take_app(t, ys) : {x <> List.take(&2, U32, List.append(&2, U32, t, ys), List.length(&2, U32, t)) == x <> _ : List<&2, U32>}
      {==}

# The first k words of ws, zero-padded to k.
def pad(+k: Nat, ws: List<&2, U32>) -> List<&2, U32>:
  match k ws:
    case 0n _:
      Nil{}
    case 1n+j Nil{}:
      Con{0, pad(j, Nil{})}
    case 1n+j Con{w, t}:
      Con{w, pad(j, t)}

law pad_take:
  for +k: Nat
  for +ws: List<&2, U32>
  {pad(k, List.take(&2, U32, ws, k)) == pad(k, ws) : List<&2, U32>}

def pad_take(k, ws):
  match k ws:
    case 0n Nil{}:
      {==}
    case 0n Con{w, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{w, t}:
      %pad_take(j, t) : {w <> pad(j, List.take(&2, U32, t, j)) == w <> _ : List<&2, U32>}
      {==}

law pad_add:
  for +a: Nat
  for +b: Nat
  for +ws: List<&2, U32>
  {pad(Nat.add(a, b), ws) == List.append(&2, U32, pad(a, ws), pad(b, List.drop(&2, U32, ws, a))) : List<&2, U32>}

def pad_add(a, b, ws):
  match a ws:
    case 0n Nil{}:
      {==}
    case 0n Con{w, t}:
      {==}
    case 1n+j Nil{}:
      %pad_add(j, b, Nil{}) : {0 <> pad(Nat.add(j, b), Nil{}) == 0 <> _ : List<&2, U32>}
      {==}
    case 1n+j Con{w, t}:
      %pad_add(j, b, t) : {w <> pad(Nat.add(j, b), t) == w <> _ : List<&2, U32>}
      {==}

# A list no longer than k, padded to k, is the list followed by zeros.
law pad_app:
  for +k: Nat
  for +ws: List<&2, U32>
  for +h: {Nat.is_le(List.length(&2, U32, ws), k) == True{} : Bool}
  {pad(k, ws) == List.append(&2, U32, ws, pad(Nat.sub(k, List.length(&2, U32, ws)), Nil{})) : List<&2, U32>}

def pad_app(k, ws, h):
  match k ws:
    case 0n Nil{}:
      {==}
    case 0n Con{w, t}:
      Empty.absurd({Nil{} == List.append(&2, U32, w <> t, pad(0n, Nil{})) : List<&2, U32>}, AB.false_ne_true(h))
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{w, t}:
      %pad_app(j, t, h) : {w <> pad(j, t) == w <> _ : List<&2, U32>}
      {==}

# Words
# =====

# The zero bytes that pad the last word of words(xs).
def wz(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b0, Nil{}}:
      [0, 0, 0]
    case Con{b0, Con{b1, Nil{}}}:
      [0, 0]
    case Con{b0, Con{b1, Con{b2, Nil{}}}}:
      [0]
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      wz(t)

law ab_h:
  for +x: U32
  for +t: List<&2, U32>
  for +h: {D.all_bytes(x <> t) == True{} : Bool}
  {U32.is_lt(x, 256) == True{} : Bool}

def ab_h(x, t, h):
  AB.and_true_l(U32.is_lt(x, 256), D.all_bytes(t), h)

law ab_t:
  for +x: U32
  for +t: List<&2, U32>
  for +h: {D.all_bytes(x <> t) == True{} : Bool}
  {D.all_bytes(t) == True{} : Bool}

def ab_t(x, t, h):
  AB.and_true_r(U32.is_lt(x, 256), D.all_bytes(t), h)

# The bytes of a packed word.
law l4p:
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +h0: {U32.is_lt(b0, 256) == True{} : Bool}
  for +h1: {U32.is_lt(b1, 256) == True{} : Bool}
  for +h2: {U32.is_lt(b2, 256) == True{} : Bool}
  for +h3: {U32.is_lt(b3, 256) == True{} : Bool}
  {[W.byte(W.pack4(b0, b1, b2, b3), 0n), W.byte(W.pack4(b0, b1, b2, b3), 1n), W.byte(W.pack4(b0, b1, b2, b3), 2n), W.byte(W.pack4(b0, b1, b2, b3), 3n)] == [b0, b1, b2, b3] : List<&2, U32>}

def l4p(b0, b1, b2, b3, h0, h1, h2, h3):
  +P = W.pack4(b0, b1, b2, b3)
  %Equal.sym(U32, W.byte(P, 0n), W.nth4(0n, b0, b1, b2, b3), Y.byte_pack4(b0, b1, b2, b3, 0n, h0, h1, h2, h3, {==})) :
    {[_, W.byte(P, 1n), W.byte(P, 2n), W.byte(P, 3n)] == [b0, b1, b2, b3] : List<&2, U32>}
  %Equal.sym(U32, W.byte(P, 1n), W.nth4(1n, b0, b1, b2, b3), Y.byte_pack4(b0, b1, b2, b3, 1n, h0, h1, h2, h3, {==})) :
    {[b0, _, W.byte(P, 2n), W.byte(P, 3n)] == [b0, b1, b2, b3] : List<&2, U32>}
  %Equal.sym(U32, W.byte(P, 2n), W.nth4(2n, b0, b1, b2, b3), Y.byte_pack4(b0, b1, b2, b3, 2n, h0, h1, h2, h3, {==})) :
    {[b0, b1, _, W.byte(P, 3n)] == [b0, b1, b2, b3] : List<&2, U32>}
  %Equal.sym(U32, W.byte(P, 3n), W.nth4(3n, b0, b1, b2, b3), Y.byte_pack4(b0, b1, b2, b3, 3n, h0, h1, h2, h3, {==})) :
    {[b0, b1, b2, _] == [b0, b1, b2, b3] : List<&2, U32>}
  {==}

# Unpacking the words of a list of bytes gives the list back, zero-padded.
law words_unpack:
  for +xs: List<&2, U32>
  for +h: {D.all_bytes(xs) == True{} : Bool}
  {D.unpack(E.words(xs)) == List.append(&2, U32, xs, wz(xs)) : List<&2, U32>}

def words_unpack(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{b0, t0}:
      match t0:
        case Nil{}:
          %Equal.sym(List<&2, U32>, C.L4(W.pack4(b0, 0, 0, 0)), [b0, 0, 0, 0],
            l4p(b0, 0, 0, 0, ab_h(b0, Nil{}, h), {==}, {==}, {==})) :
            {List.append(&2, U32, _, Nil{}) == [b0, 0, 0, 0] : List<&2, U32>}
          {==}
        case Con{b1, t1}:
          match t1:
            case Nil{}:
              +h1t = ab_t(b0, [b1], h)
              %Equal.sym(List<&2, U32>, C.L4(W.pack4(b0, b1, 0, 0)), [b0, b1, 0, 0],
                l4p(b0, b1, 0, 0, ab_h(b0, [b1], h), ab_h(b1, Nil{}, h1t), {==}, {==})) :
                {List.append(&2, U32, _, Nil{}) == [b0, b1, 0, 0] : List<&2, U32>}
              {==}
            case Con{b2, t2}:
              match t2:
                case Nil{}:
                  +h1t = ab_t(b0, [b1, b2], h)
                  +h2t = ab_t(b1, [b2], h1t)
                  %Equal.sym(List<&2, U32>, C.L4(W.pack4(b0, b1, b2, 0)), [b0, b1, b2, 0],
                    l4p(b0, b1, b2, 0, ab_h(b0, [b1, b2], h), ab_h(b1, [b2], h1t), ab_h(b2, Nil{}, h2t), {==})) :
                    {List.append(&2, U32, _, Nil{}) == [b0, b1, b2, 0] : List<&2, U32>}
                  {==}
                case Con{b3, t}:
                  +h1t = ab_t(b0, b1 <> b2 <> b3 <> t, h)
                  +h2t = ab_t(b1, b2 <> b3 <> t, h1t)
                  +h3t = ab_t(b2, b3 <> t, h2t)
                  +h4t = ab_t(b3, t, h3t)
                  %Equal.sym(List<&2, U32>, C.L4(W.pack4(b0, b1, b2, b3)), [b0, b1, b2, b3],
                    l4p(b0, b1, b2, b3, ab_h(b0, b1 <> b2 <> b3 <> t, h), ab_h(b1, b2 <> b3 <> t, h1t), ab_h(b2, b3 <> t, h2t), ab_h(b3, t, h3t))) :
                    {List.append(&2, U32, _, D.unpack(E.words(t))) == List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> t, wz(t)) : List<&2, U32>}
                  %Equal.sym(List<&2, U32>, D.unpack(E.words(t)), List.append(&2, U32, t, wz(t)), words_unpack(t, h4t)) :
                    {List.append(&2, U32, [b0, b1, b2, b3], _) == List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> t, wz(t)) : List<&2, U32>}
                  {==}

# At most 4k bytes make at most k words.
law words_len:
  for +xs: List<&2, U32>
  for +k: Nat
  for +h: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(k, 4n)) == True{} : Bool}
  {Nat.is_le(List.length(&2, U32, E.words(xs)), k) == True{} : Bool}

def words_len(xs, k, h):
  match xs:
    case Nil{}:
      N.le_zero_l(k)
    case Con{b0, t0}:
      match t0:
        case Nil{}:
          match k:
            case 0n:
              Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.false_ne_true(h))
            case 1n+q:
              N.le_zero_l(q)
        case Con{b1, t1}:
          match t1:
            case Nil{}:
              match k:
                case 0n:
                  Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.false_ne_true(h))
                case 1n+q:
                  N.le_zero_l(q)
            case Con{b2, t2}:
              match t2:
                case Nil{}:
                  match k:
                    case 0n:
                      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AB.false_ne_true(h))
                    case 1n+q:
                      N.le_zero_l(q)
                case Con{b3, t}:
                  match k:
                    case 0n:
                      Empty.absurd({Nat.is_le(1n+List.length(&2, U32, E.words(t)), 0n) == True{} : Bool}, AB.false_ne_true(h))
                    case 1n+q:
                      words_len(t, q, h)

# Bounds
# ======

law lt_pow:
  for +d: Nat
  {Nat.is_lt(d, Nat.pow(2n, d)) == True{} : Bool}

def lt_pow(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      N.le_lt_trans(1n+p, Nat.pow(2n, p), Nat.pow(2n, 1n+p),
        Equal.trans(Bool, Nat.is_le(1n+p, Nat.pow(2n, p)), Nat.is_lt(p, Nat.pow(2n, p)), True{}, N.le_succ_lt(p, Nat.pow(2n, p)), lt_pow(p)),
        AB.pow_lt(p, 1n+p, Equal.trans(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), True{}, N.lt_succ_iff(p, p), N.le_refl(p))))

law le_four:
  for +d: Nat
  {Nat.is_le(d, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def le_four(d):
  N.le_trans(d, Nat.pow(2n, d), Nat.mul(4n, Nat.pow(2n, d)), N.lt_to_le(d, Nat.pow(2n, d), lt_pow(d)),
    N.le_add_r(Nat.pow(2n, d), Nat.mul(3n, Nat.pow(2n, d))))

law pick_le:
  for +c: Bool
  for +d: Nat
  for +r: Nat
  for +n: Nat
  for +hc: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))) == c : Bool}
  for +hr: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, r))) == True{} : Bool}
  {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, Bool.pick(Nat, c, d, r)))) == True{} : Bool}

def pick_le(c, d, r, n, hc, hr):
  match c:
    case True{}:
      hc
    case False{}:
      hr

# depth.go ends at a block that holds n bytes, given enough fuel.
law go_fits:
  for +f: Nat
  for +d: Nat
  for +n: Nat
  for +h: {Nat.is_le(n, Nat.add(d, f)) == True{} : Bool}
  {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, E.depth.go(f, d, n)))) == True{} : Bool}

def go_fits(f, d, n, h):
  match f:
    case 0n:
      N.le_trans(n, d, Nat.mul(4n, Nat.pow(2n, d)), %AB.add_zero(d) : {Nat.is_le(n, _) == True{} : Bool}; h, le_four(d))
    case 1n+g:
      pick_le(Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))), d, E.depth.go(g, Nat.add(d, 1n), n), n, {==},
        go_fits(g, Nat.add(d, 1n), n,
          %Equal.sym(Nat, Nat.add(Nat.add(d, 1n), g), Nat.add(d, 1n+g), N.add_assoc(d, 1n, g)) : {Nat.is_le(n, _) == True{} : Bool}; h))

# A block that does not hold n bytes is below B when the block of depth B does.
law next_lt:
  for +c: Bool
  for +d: Nat
  for +n: Nat
  for +B: Nat
  for +hc2: {Nat.is_lt(d, B) == c : Bool}
  for +hc: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))) == False{} : Bool}
  for +hn: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}
  {Nat.is_lt(d, B) == True{} : Bool}

def next_lt(c, d, n, B, hc2, hc, hn):
  match c:
    case True{}:
      hc2
    case False{}:
      +hbd = N.not_lt_le(d, B, hc2)
      +hm = N.le_mul_l(4n, Nat.pow(2n, B), Nat.pow(2n, d), N.pow_le(B, d, hbd))
      +hnd = N.le_trans(n, Nat.mul(4n, Nat.pow(2n, B)), Nat.mul(4n, Nat.pow(2n, d)), hn, hm)
      Empty.absurd({Nat.is_lt(d, B) == True{} : Bool},
        AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))), True{},
          Equal.sym(Bool, Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))), False{}, hc), hnd)))

law next_le:
  for +d: Nat
  for +n: Nat
  for +B: Nat
  for +hc: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))) == False{} : Bool}
  for +hn: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}
  {Nat.is_le(Nat.add(d, 1n), B) == True{} : Bool}

def next_le(d, n, B, hc, hn):
  %Equal.sym(Nat, Nat.add(d, 1n), 1n+d, N.add_one(d)) : {Nat.is_le(_, B) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(1n+d, B), Nat.is_lt(d, B), True{}, N.le_succ_lt(d, B),
    next_lt(Nat.is_lt(d, B), d, n, B, {==}, hc, hn))

law go_le_s:
  for +c: Bool
  for +d: Nat
  for +n: Nat
  for +B: Nat
  for +r: Nat
  for +hc: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))) == c : Bool}
  for +hd: {Nat.is_le(d, B) == True{} : Bool}
  for +hn: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}
  for ih: {Nat.is_le(Nat.add(d, 1n), B) == True{} : Bool} -> {Nat.is_le(r, B) == True{} : Bool}
  {Nat.is_le(Bool.pick(Nat, c, d, r), B) == True{} : Bool}

def go_le_s(c, d, n, B, r, hc, hd, hn, ih):
  match c:
    case True{}:
      hd
    case False{}:
      ih(next_le(d, n, B, hc, hn))

# depth.go stops by depth B when the block of depth B holds n bytes.
law go_le:
  for +f: Nat
  for +d: Nat
  for +n: Nat
  for +B: Nat
  for +hd: {Nat.is_le(d, B) == True{} : Bool}
  for +hn: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}
  {Nat.is_le(E.depth.go(f, d, n), B) == True{} : Bool}

def go_le(f, d, n, B, hd, hn):
  match f:
    case 0n:
      hd
    case 1n+g:
      go_le_s(Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, d))), d, n, B, E.depth.go(g, Nat.add(d, 1n), n), {==}, hd, hn,
        h1 => go_le(g, Nat.add(d, 1n), n, B, h1, hn))

# n <= 2^e gives n <= 4 * 2^B for e = 2 + B (B and e stay variables: the
# callers instantiate them only in the final types).
law pow_four:
  for +n: Nat
  for +B: Nat
  for +e: Nat
  for +he: {Nat.add(2n, B) == e : Nat}
  for +h: {Nat.is_le(n, Nat.pow(2n, e)) == True{} : Bool}
  {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, B))) == True{} : Bool}

def pow_four(n, B, e, he, h):
  +P = Nat.pow(2n, B)
  %Equal.sym(Nat, Nat.mul(Nat.mul(2n, 2n), P), Nat.mul(2n, Nat.mul(2n, P)), N.mul_assoc(2n, 2n, P)) :
    {Nat.is_le(n, _) == True{} : Bool}
  AB.subst(Nat, x => {Nat.is_le(n, Nat.pow(2n, x)) == True{} : Bool}, e, Nat.add(2n, B), Equal.sym(Nat, Nat.add(2n, B), e, he), h)

# A length that fits a block of depth at most 29 is unchanged by a U32.
law to_nat_fits:
  for +n: Nat
  for +h: {Nat.is_le(n, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}
  {U32.to_nat(U32.from_nat(n)) == n : Nat}

def to_nat_fits(n, h):
  Equal.trans(Nat, U32.to_nat(U32.from_nat(n)), Nat.mod(n, Nat.pow(2n, 32n)), n, U.to_nat_from_nat_p(n),
    U.wrap_small_p(n, C.fits_e(n, 29n, 32n, {==}, h)))
