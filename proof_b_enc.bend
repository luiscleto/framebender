import Base
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_seq.bend as SQ
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/defs.bend as A
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ./proof_b_enc_lem.bend as X
import ./proof_b_lit.bend as LIT

# bytes_enc.bend's encoding and decoding (the contract's view of a buffer):
# enc(s) is a well-formed buffer that holds s's bytes, as a lawful-bytes
# mirror; text and out read a well-formed buffer back as text.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# E.tree's block as a Tree (the mirror of E.enc's block).
def ttree(+d: Nat, +ws: List<&2, U32>) -> AT.Tree<U32>:
  match d:
    case 0n:
      AT.TLeaf{Maybe.default(&2, U32, List.get(&2, U32, ws, 0n), 0)}
    case 1n+p:
      AT.TNode{ttree(p, List.take(&2, U32, ws, Nat.pow(2n, p))), ttree(p, List.drop(&2, U32, ws, Nat.pow(2n, p)))}

def enc_t(+s: String) -> AT.Tree<U32>:
  ttree(E.depth(String.length(s)), E.words(E.codes(s)))


# Lemmas about the mirror
# =======================

law tree_eq:
  for +d: Nat
  for +ws: List<&2, U32>
  {AT.fromT(U32, ttree(d, ws)) == E.tree(d, ws) : Array<U32>}

def tree_eq(d, ws):
  match d:
    case 0n:
      {==}
    case 1n+p:
      +L = List.take(&2, U32, ws, Nat.pow(2n, p))
      +R = List.drop(&2, U32, ws, Nat.pow(2n, p))
      AT.anode_eq(U32, AT.fromT(U32, ttree(p, L)), AT.fromT(U32, ttree(p, R)), E.tree(p, L), E.tree(p, R),
        tree_eq(p, L), tree_eq(p, R))

law full_ttree:
  for +d: Nat
  for +ws: List<&2, U32>
  {A.full(U32, AT.fromT(U32, ttree(d, ws)), d) == True{} : Bool}

def full_ttree(d, ws):
  match d:
    case 0n:
      {==}
    case 1n+p:
      +L = List.take(&2, U32, ws, Nat.pow(2n, p))
      +R = List.drop(&2, U32, ws, Nat.pow(2n, p))
      %Equal.sym(Bool, A.full(U32, AT.fromT(U32, ttree(p, L)), p), True{}, full_ttree(p, L)) :
        {Bool.and(_, A.full(U32, AT.fromT(U32, ttree(p, R)), p)) == True{} : Bool}
      %Equal.sym(Bool, A.full(U32, AT.fromT(U32, ttree(p, R)), p), True{}, full_ttree(p, R)) :
        {Bool.and(True{}, _) == True{} : Bool}
      {==}

# The words of ttree(d, ws): ws padded to 2^d.
law view_ttree:
  for +d: Nat
  for +ws: List<&2, U32>
  {A.view(U32, AT.fromT(U32, ttree(d, ws))) == X.pad(Nat.pow(2n, d), ws) : List<&2, U32>}

def view_ttree(d, ws):
  match d:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case Con{w, t}:
          {==}
    case 1n+p:
      +P = Nat.pow(2n, p)
      +L = List.take(&2, U32, ws, P)
      +R = List.drop(&2, U32, ws, P)
      %Equal.sym(List<&2, U32>, A.view(U32, AT.fromT(U32, ttree(p, L))), X.pad(P, L), view_ttree(p, L)) :
        {List.append(&2, U32, _, A.view(U32, AT.fromT(U32, ttree(p, R)))) == X.pad(Nat.pow(2n, 1n+p), ws) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, A.view(U32, AT.fromT(U32, ttree(p, R))), X.pad(P, R), view_ttree(p, R)) :
        {List.append(&2, U32, X.pad(P, L), _) == X.pad(Nat.pow(2n, 1n+p), ws) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, X.pad(P, L), X.pad(P, ws), X.pad_take(P, ws)) :
        {List.append(&2, U32, _, X.pad(P, R)) == X.pad(Nat.pow(2n, 1n+p), ws) : List<&2, U32>}
      %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.add(P, P), AB.pow_succ(p)) :
        {List.append(&2, U32, X.pad(P, ws), X.pad(P, R)) == X.pad(_, ws) : List<&2, U32>}
      Equal.sym(List<&2, U32>, X.pad(Nat.add(P, P), ws), List.append(&2, U32, X.pad(P, ws), X.pad(P, R)), X.pad_add(P, P, ws))

# The first length(xs) bytes of the block built from xs's words are xs.
law view_words:
  for +xs: List<&2, U32>
  for +d: Nat
  for +hb: {D.all_bytes(xs) == True{} : Bool}
  for +hl: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {List.take(&2, U32, D.unpack(A.view(U32, AT.fromT(U32, ttree(d, E.words(xs))))), List.length(&2, U32, xs)) == xs : List<&2, U32>}

def view_words(xs, d, hb, hl):
  +K = Nat.pow(2n, d)
  +n = List.length(&2, U32, xs)
  +WS = E.words(xs)
  +Z = X.pad(Nat.sub(K, List.length(&2, U32, WS)), Nil{})
  +hw = X.words_len(xs, K, %N.mul_comm(4n, K) : {Nat.is_le(n, _) == True{} : Bool}; hl)
  %Equal.sym(List<&2, U32>, A.view(U32, AT.fromT(U32, ttree(d, WS))), X.pad(K, WS), view_ttree(d, WS)) :
    {List.take(&2, U32, D.unpack(_), n) == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, X.pad(K, WS), List.append(&2, U32, WS, Z), X.pad_app(K, WS, hw)) :
    {List.take(&2, U32, D.unpack(_), n) == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.unpack(List.append(&2, U32, WS, Z)), List.append(&2, U32, D.unpack(WS), D.unpack(Z)), SQ.unpack_append(WS, Z)) :
    {List.take(&2, U32, _, n) == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.unpack(WS), List.append(&2, U32, xs, X.wz(xs)), X.words_unpack(xs, hb)) :
    {List.take(&2, U32, List.append(&2, U32, _, D.unpack(Z)), n) == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, xs, X.wz(xs)), D.unpack(Z)),
    List.append(&2, U32, xs, List.append(&2, U32, X.wz(xs), D.unpack(Z))), X.append_assoc(xs, X.wz(xs), D.unpack(Z))) :
    {List.take(&2, U32, _, n) == xs : List<&2, U32>}
  X.take_app(xs, List.append(&2, U32, X.wz(xs), D.unpack(Z)))

# A perfect tree of depth d: shape gives d and its words.
law shape_full:
  for +d: Nat
  for +t: AT.Tree<U32>
  for +hf: {A.full(U32, AT.fromT(U32, t), d) == True{} : Bool}
  {E.shape(AT.fromT(U32, t)) == (Some{d}, A.view(U32, AT.fromT(U32, t))) : Maybe<&2, Nat> & List<&2, U32>}

def shape_full(d, t, hf):
  match d t:
    case 0n AT.TLeaf{x}:
      {==}
    case 0n AT.TNode{l, r}:
      Empty.absurd({E.shape(AT.fromT(U32, AT.TNode{l, r})) == (Some{0n}, A.view(U32, AT.fromT(U32, AT.TNode{l, r}))) : Maybe<&2, Nat> & List<&2, U32>},
        AB.false_ne_true(hf))
    case 1n+p AT.TLeaf{x}:
      Empty.absurd({E.shape(ALeaf{x}) == (Some{1n+p}, [x]) : Maybe<&2, Nat> & List<&2, U32>}, AB.false_ne_true(hf))
    case 1n+p AT.TNode{l, r}:
      +VL = A.view(U32, AT.fromT(U32, l))
      +VR = A.view(U32, AT.fromT(U32, r))
      +hl = AB.and_true_l(A.full(U32, AT.fromT(U32, l), p), A.full(U32, AT.fromT(U32, r), p), hf)
      +hr = AB.and_true_r(A.full(U32, AT.fromT(U32, l), p), A.full(U32, AT.fromT(U32, r), p), hf)
      %Equal.sym(Maybe<&2, Nat> & List<&2, U32>, E.shape(AT.fromT(U32, l)), (Some{p}, VL), shape_full(p, l, hl)) :
        {E.shape.join(_, E.shape(AT.fromT(U32, r))) == (Some{1n+p}, List.append(&2, U32, VL, VR)) : Maybe<&2, Nat> & List<&2, U32>}
      %Equal.sym(Maybe<&2, Nat> & List<&2, U32>, E.shape(AT.fromT(U32, r)), (Some{p}, VR), shape_full(p, r, hr)) :
        {E.shape.join((Some{p}, VL), _) == (Some{1n+p}, List.append(&2, U32, VL, VR)) : Maybe<&2, Nat> & List<&2, U32>}
      %Equal.sym(Bool, Nat.is_eq(p, p), True{}, N.eq_refl(p)) :
        {(Bool.pick(Maybe<&2, Nat>, _, Some{Nat.add(p, 1n)}, None{}), List.append(&2, U32, VL, VR)) == (Some{1n+p}, List.append(&2, U32, VL, VR)) : Maybe<&2, Nat> & List<&2, U32>}
      %N.add_one(p) :
        {(Some{Nat.add(p, 1n)}, List.append(&2, U32, VL, VR)) == (Some{_}, List.append(&2, U32, VL, VR)) : Maybe<&2, Nat> & List<&2, U32>}
      {==}


# The view of enc(s)'s mirror, from the length facts.
law enc_view:
  for +s: String
  for +hnat: {U32.to_nat(U32.from_nat(String.length(s))) == String.length(s) : Nat}
  for +hv: {List.take(&2, U32, D.unpack(A.view(U32, AT.fromT(U32, enc_t(s)))), List.length(&2, U32, E.codes(s))) == E.codes(s) : List<&2, U32>}
  {D.view(C.BT(U32.from_nat(String.length(s)), enc_t(s))) == E.codes(s) : List<&2, U32>}

def enc_view(s, hnat, hv):
  +V = D.unpack(A.view(U32, AT.fromT(U32, enc_t(s))))
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(s))), String.length(s), hnat) :
    {List.take(&2, U32, V, _) == E.codes(s) : List<&2, U32>}
  %Equal.sym(Nat, String.length(s), List.length(&2, U32, E.codes(s)), X.length_codes(s)) :
    {List.take(&2, U32, V, _) == E.codes(s) : List<&2, U32>}
  hv


law norm_chars:
  for +xs: List<&2, U32>
  {Norm.chars(xs) == E.chars(xs) : String}

def norm_chars(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %norm_chars(t) : {SCon{Chr{x}, Norm.chars(t)} == SCon{Chr{x}, _} : String}
      {==}


law out_go:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {E.out(C.BT(len, t)) == Some{E.chars(D.view(C.BT(len, t)))} : Maybe<&2, String>}

def out_go(len, t, d, hok, hd):
  +V = A.view(U32, AT.fromT(U32, t))
  +M = Nat.mul(4n, Nat.pow(2n, d))
  %Equal.sym(Maybe<&2, Nat> & List<&2, U32>, E.shape(AT.fromT(U32, t)), (Some{d}, V), shape_full(d, t, C.ok_full(len, t, d, hok))) :
    {E.out.of(len, _) == Some{E.chars(D.view(C.BT(len, t)))} : Maybe<&2, String>}
  %Equal.sym(Bool, Nat.is_le(d, 29n), True{}, hd) :
    {E.out.if(Bool.and(_, Nat.is_le(U32.to_nat(len), M)), List.take(&2, U32, D.unpack(V), U32.to_nat(len))) == Some{E.chars(D.view(C.BT(len, t)))} : Maybe<&2, String>}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(len), M), True{}, C.ok_len(len, t, d, hok)) :
    {E.out.if(Bool.and(True{}, _), List.take(&2, U32, D.unpack(V), U32.to_nat(len))) == Some{E.chars(D.view(C.BT(len, t)))} : Maybe<&2, String>}
  {==}

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# enc(s) is the mirror of enc_t(s).
def enc_bt(+s: String) ->
  {E.enc(s) == C.BT(U32.from_nat(String.length(s)), enc_t(s)) : D.Bytes}:
  +ln = String.length(s)
  +WS = E.words(E.codes(s))
  %Equal.sym(Array<U32>, AT.fromT(U32, ttree(E.depth(ln), WS)), E.tree(E.depth(ln), WS), tree_eq(E.depth(ln), WS)) :
    {E.enc(s) == D.Bytes{U32.from_nat(ln), _} : D.Bytes}
  {==}

# For a text of bytes that fits a buffer (at most 2^31 bytes), enc(s) is well
# formed with depth E.depth(length) and holds s's bytes.
def enc_ok(+s: String,
  hb: {E.is_bytes(s) == True{} : Bool},
  hn: {P.le31(String.length(s)) == True{} : Bool}) ->
  {D.ok(C.BT(U32.from_nat(String.length(s)), enc_t(s)), E.depth(String.length(s))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(s)), enc_t(s))) == E.codes(s) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(s)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(s))) == String.length(s) : Nat})):
  +ln = String.length(s)
  +hn29 = X.pow_four(ln, 29n, 31n, {==}, LIT.le31_le(ln, hn))
  +hnat = X.to_nat_fits(ln, hn29)
  +hd = X.go_le(Nat.add(ln, 1n), 0n, ln, 29n, N.le_zero_l(29n), hn29)
  +cs = E.codes(s)
  +dd = E.depth(ln)
  +t = enc_t(s)
  +M = Nat.mul(4n, Nat.pow(2n, dd))
  +hfit = X.go_fits(Nat.add(ln, 1n), 0n, ln, N.le_add_r(ln, 1n))
  +hl = AB.subst(Nat, x => {Nat.is_le(x, M) == True{} : Bool}, ln, U32.to_nat(U32.from_nat(ln)), Equal.sym(Nat, U32.to_nat(U32.from_nat(ln)), ln, hnat), hfit)
  +hok = C.ok_mk(U32.from_nat(ln), t, dd, full_ttree(dd, E.words(cs)), hd, hl)
  +hbc = Equal.trans(Bool, D.all_bytes(cs), E.is_bytes(s), True{}, X.bytes_codes(s), hb)
  +hlc = AB.subst(Nat, x => {Nat.is_le(x, M) == True{} : Bool}, ln, List.length(&2, U32, cs), X.length_codes(s), hfit)
  +hv = view_words(cs, dd, hbc, hlc)
  (hok, (enc_view(s, hnat, hv), (hd, hnat)))

# Decoding the bytes of a text gives the text back (Norm.chars is E.chars).
def chars_codes(+s: String) ->
  {E.chars(E.codes(s)) == s : String}
  & {Norm.chars(E.codes(s)) == s : String}:
  (X.chars_codes1(s),
    Equal.trans(String, Norm.chars(E.codes(s)), E.chars(E.codes(s)), s, norm_chars(E.codes(s)), X.chars_codes1(s)))

def chars_eq(+xs: List<&2, U32>) ->
  {Norm.chars(xs) == E.chars(xs) : String}:
  norm_chars(xs)

# A well-formed buffer of depth at most 29 is what out accepts, and it reads
# as its text.
def out_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hd: {Nat.is_le(d, 29n) == True{} : Bool}) ->
  {E.out(C.BT(len, t)) == Some{E.chars(D.view(C.BT(len, t)))} : Maybe<&2, String>}:
  out_go(len, t, d, hok, hd)
