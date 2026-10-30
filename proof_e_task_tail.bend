import Base
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_run_buf.bend as BF
import ./proof_e_task_piece.bend as PI
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_find.bend as FD
import lawful-bytes@0.1.0.0/proof_shift.bend as SH
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_num.bend as NM
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import ./proof_b_run_lem.bend as LM
import lawful-bytes@0.1.0.0/proof_grow.bend as G
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Phase F (memory): a task runs on its piece itself and takes it back from
# Q's input before Q reaches the piece's last partial line. Two facts about
# the piece's bytes:
#   - nolf_at: while the piece's byte el is an LF, with at <= el < len, the
#     piece's text from at holds an LF (so Q keeps the piece: S.Kept);
#   - tail_put, tail_text: the copy of the piece's bytes from at (put_bytes
#     into an empty block) is a good buffer with the piece's text from at.

def unsome(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{+x}:
      x

def is_some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def and_f(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# A list whose element i is 10: its text holds an LF.
def nolf_get(+xs: List<&2, U32>, +i: Nat, +h: {List.get(&2, U32, xs, i) == Some{10} : Maybe<&2, U32>}) ->
  {P.nolf(NR.chars(xs)) == False{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({P.nolf(NR.chars(Nil{})) == False{} : Bool},
        N.false_ne_true(Equal.cong(Maybe<&2, U32>, Bool, z => is_some(z), List.get(&2, U32, Nil{}, i), Some{10}, h)))
    case Con{+x, +t} 0n:
      +hx = Equal.cong(Maybe<&2, U32>, U32, z => unsome(z), Some{x}, Some{10}, h)
      %Equal.sym(U32, x, 10, hx) : {P.nolf(NR.chars(Con{_, t})) == False{} : Bool}
      {==}
    case Con{+x, +t} 1n+j:
      +ih = nolf_get(t, j, h)
      %Equal.sym(Bool, P.nolf(NR.chars(t)), False{}, ih) : {Bool.and(Bool.not(Char.is_eq(Chr{x}, '\n')), _) == False{} : Bool}
      and_f(Bool.not(Char.is_eq(Chr{x}, '\n')))

def add_sub_le(+a: Nat, +e: Nat, +h: {Nat.is_le(a, e) == True{} : Bool}) -> {Nat.add(a, Nat.sub(e, a)) == e : Nat}:
  match a e:
    case 0n 0n:
      {==}
    case 0n 1n+e2:
      {==}
    case 1n+a2 0n:
      Empty.absurd({Nat.add(1n+a2, Nat.sub(0n, 1n+a2)) == 0n : Nat}, N.false_ne_true(h))
    case 1n+a2 1n+e2:
      +ih = add_sub_le(a2, e2, h)
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(a2, Nat.sub(e2, a2)), e2, ih)

# The piece's byte el is an LF, at <= el < len: its text from at holds one.
def nolf_at(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +el: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hle: {U32.is_le(at, el) == True{} : Bool},
  +hlt: {U32.is_lt(el, len) == True{} : Bool},
  +hx: {U32.is_eq(C.AT(len, tr, el), 10) == True{} : Bool}) ->
  {P.nolf(P.srctext(P.SBP{len, tr, d, at})) == False{} : Bool}:
  +V = D.view(C.BT(len, tr))
  +a = U32.to_nat(at)
  +e = U32.to_nat(el)
  +h1 = C.at_view_t(len, tr, d, el, C.ok_full(len, tr, d, hok), C.ok_d(len, tr, d, hok), C.ok_len(len, tr, d, hok), PI.ult_nat(el, len, hlt))
  +hA = U.is_eq_true(C.AT(len, tr, el), 10, hx)
  +h2 = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, V, e), Some{C.AT(len, tr, el)}, Some{10}, Equal.sym(Maybe<&2, U32>, Some{C.AT(len, tr, el)}, List.get(&2, U32, V, e), h1),
    Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, C.AT(len, tr, el), 10, hA))
  +hae = Equal.trans(Bool, Nat.is_le(a, e), U32.is_le(at, el), True{}, Equal.sym(Bool, U32.is_le(at, el), Nat.is_le(a, e), U.is_le_to_nat(at, el)), hle)
  +h3 = {%add_sub_le(a, e, hae) : {List.get(&2, U32, List.drop(&2, U32, V, a), Nat.sub(e, a)) == List.get(&2, U32, V, _) : Maybe<&2, U32>};
    SH.get_drop(V, a, Nat.sub(e, a)) : {List.get(&2, U32, List.drop(&2, U32, V, a), Nat.sub(e, a)) == List.get(&2, U32, V, e) : Maybe<&2, U32>}}
  nolf_get(List.drop(&2, U32, V, a), Nat.sub(e, a), Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, V, a), Nat.sub(e, a)), List.get(&2, U32, V, e), Some{10}, h3, h2))

def len_drop(+xs: List<&2, U32>, +a: Nat) -> {List.length(&2, U32, List.drop(&2, U32, xs, a)) == Nat.sub(List.length(&2, U32, xs), a) : Nat}:
  match xs a:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+b:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+b:
      len_drop(t, b)

def take_all(+xs: List<&2, U32>) -> {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, List.length(&2, U32, t)), t, take_all(t)) : {Con{x, _} == Con{x, t} : List<&2, U32>}
      {==}

# The copy of the piece's bytes from at (put_bytes into an empty block) has
# the piece's text from at.
def tail_text(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32, +L2: U32, +T2: AT.Tree<U32>, +d2: Nat, +te: AT.Tree<U32>,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hle: {U32.is_le(at, len) == True{} : Bool},
  +hv2: {D.view(C.BT(L2, T2)) == List.append(&2, U32, D.view(C.BT(0, te)), D.slice(D.view(C.BT(len, tr)), U32.to_nat(at), U32.to_nat((len - at : U32)))) : List<&2, U32>}) ->
  {P.srctext(P.SBP{L2, T2, d2, 0}) == P.srctext(P.SBP{len, tr, d, at}) : String}:
  +V = D.view(C.BT(len, tr))
  +a = U32.to_nat(at)
  +R = List.drop(&2, U32, V, a)
  %Equal.sym(List<&2, U32>, D.view(C.BT(L2, T2)), List.append(&2, U32, D.view(C.BT(0, te)), D.slice(V, a, U32.to_nat((len - at : U32)))), hv2) :
    {NR.chars(List.drop(&2, U32, _, U32.to_nat(0))) == NR.chars(R) : String}
  %Equal.sym(List<&2, U32>, D.view(C.BT(0, te)), Nil{}, BF.view0(te)) :
    {NR.chars(List.drop(&2, U32, List.append(&2, U32, _, D.slice(V, a, U32.to_nat((len - at : U32)))), 0n)) == NR.chars(R) : String}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.take(&2, U32, R, U32.to_nat((len - at : U32))), 0n), List.take(&2, U32, R, U32.to_nat((len - at : U32))), FD.drop_zero(List.take(&2, U32, R, U32.to_nat((len - at : U32))))) :
    {NR.chars(_) == NR.chars(R) : String}
  %Equal.sym(Nat, U32.to_nat((len - at : U32)), Nat.sub(U32.to_nat(len), a), U.to_nat_sub_le(len, at, hle)) :
    {NR.chars(List.take(&2, U32, R, _)) == NR.chars(R) : String}
  %O.view_size_t(len, tr, d, hok) :
    {NR.chars(List.take(&2, U32, R, Nat.sub(_, a))) == NR.chars(R) : String}
  %len_drop(V, a) :
    {NR.chars(List.take(&2, U32, R, _)) == NR.chars(R) : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, R, List.length(&2, U32, R)), R, take_all(R)) :
    {NR.chars(_) == NR.chars(R) : String}
  {==}

# Bounds (as proof_e_task_one.bend's, which imports this file's users).
def le_w(+L: U32, +w: U32, +k: Nat, +hw: {U32.shln(1, k) == w : U32}, +hk: {Nat.is_lt(k, 32n) == True{} : Bool},
  +h: {U32.is_lt(L, w) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(L), Nat.pow(2n, k)) == True{} : Bool}:
  +h1 = AB.subst(Nat, y => {Nat.is_lt(U32.to_nat(L), y) == True{} : Bool}, U32.to_nat(w), Nat.pow(2n, k), PL.lit_pow(k, w, hw, hk),
    PI.ult_nat(L, w, h))
  N.lt_to_le(U32.to_nat(L), Nat.pow(2n, k), h1)

def le30(+L: U32, +h: {U32.is_lt(L, 1073741824) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(L), Nat.pow(2n, 30n)) == True{} : Bool}:
  le_w(L, 1073741824, 30n, {==}, {==}, h)

def ok_empty(+e: Nat, +hd: {Nat.is_le(e, 29n) == True{} : Bool}) -> {D.ok(C.BT(0, G.tnew(e, 0)), RD.tdepth(G.tnew(e, 0))) == True{} : Bool}:
  LM.ok_td(0, G.tnew(e, 0), e, AB.subst(D.Bytes, z => {D.ok(z, e) == True{} : Bool}, BY.empty(e), C.BT(0, G.tnew(e, 0)), G.empty_eq(e), G.empty_ok(e, hd)))

# The depth of the block the task copies the piece's bytes from at into.
def TE(+len: U32, +at: U32) -> Nat:
  NR.depth((len - at + 8 : U32))

# The copy of the piece's bytes from at, for a piece of less than 2^30 bytes.
def tail_put(+len: U32, +tr: AT.Tree<U32>, +d: Nat, +at: U32,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hle: {U32.is_le(at, len) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool}) ->
  &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(0, G.tnew(TE(len, at), 0), len, tr, at, (len - at : U32), l2, t2):
  +n = U32.to_nat((len - at : U32))
  +L = U32.to_nat(len)
  +a = U32.to_nat(at)
  +hn = U.to_nat_sub_le(len, at, hle)
  +hae = Equal.trans(Bool, Nat.is_le(a, L), U32.is_le(at, len), True{}, Equal.sym(Bool, U32.is_le(at, len), Nat.is_le(a, L), U.is_le_to_nat(at, len)), hle)
  +hs = {%Equal.sym(Nat, n, Nat.sub(L, a), hn) : {Nat.is_le(Nat.add(a, _), L) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(a, Nat.sub(L, a)), L, add_sub_le(a, L, hae)) : {Nat.is_le(_, L) == True{} : Bool};
    N.le_refl(L) : {Nat.is_le(Nat.add(a, n), L) == True{} : Bool}}
  +hnL = {%Equal.sym(Nat, n, Nat.sub(L, a), hn) : {Nat.is_le(_, L) == True{} : Bool};
    U.sub_le(L, a) : {Nat.is_le(n, L) == True{} : Bool}}
  BF.put_bytes_t(0, G.tnew(TE(len, at), 0), len, tr, d, at, (len - at : U32), ok_empty(TE(len, at), NM.depth_le((len - at + 8 : U32))), hok, hs,
    NM.lt_c0(n, Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(n, N.le_trans(n, L, Nat.pow(2n, 30n), hnL, le30(len, hL)))))
