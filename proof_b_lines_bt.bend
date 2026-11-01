import Base
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_fasteq.bend as FE
import ./proof_b_lines_str.bend as S
import ./proof_b_lines_lst.bend as T
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/fast.bend as F
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_find.bend as FD
import lawful-bytes@0.1.1.0/proof_list.bend as Q
import lawful-bytes@0.1.1.0/proof_seq.bend as SQ
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-bytes@0.1.1.0/proof_fast_append.bend as FA
import lawful-bytes@0.1.1.0/proof_shift.bend as SH
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A source's bytes up to its first LF (the deliverables lf_ok, src_line and
# src_nolf of proof_b_lines.bend, with every argument reusable).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

def lf_ok.go(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool}) ->
  &j: U32 -> ({NF.lf(C.BT(len, t), s) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
  & {n(j) == D.first(xs(len, t), n(s), n(len), 10) : Nat}):
  +j = Pair.snd(D.Bytes, U32, BY.find(C.BT(len, t), s, len, 10))
  +e1 = Equal.trans(D.Bytes & U32, F.find(C.BT(len, t), s, len, 10), BY.find(C.BT(len, t), s, len, 10), (C.BT(len, t), j),
    FE.find_eq(C.BT(len, t), d, s, len, 10, hok, hs, N.le_refl(n(len)), {==}), FD.find_pair_t(len, t, s, len, 10))
  +e2 = {
    %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, len, 10), (C.BT(len, t), j), e1) :
      {NF.lf.k(len, _) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
    {==} : {NF.lf(C.BT(len, t), s) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}}
  (j, (e2, FD.find_view_t(len, t, d, s, len, 10, hok, hs, N.le_refl(n(len)), {==})))

# The facts about a source of bytes from at, with L its length and A = at.
def hlen(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {List.length(&2, U32, xs(len, t)) == n(len) : Nat}:
  O.view_size_t(len, t, d, hok)

# The rest from at has length L - A.
def hlw(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}) ->
  {List.length(&2, U32, List.drop(&2, U32, xs(len, t), n(at))) == Nat.sub(n(len), n(at)) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, List.drop(&2, U32, xs(len, t), n(at))), Nat.sub(List.length(&2, U32, xs(len, t)), n(at)), Nat.sub(n(len), n(at)),
    SH.drop_length(xs(len, t), n(at)),
    Equal.cong(Nat, Nat, x => Nat.sub(x, n(at)), List.length(&2, U32, xs(len, t)), n(len), hlen(len, t, d, hok)))

def src_line.go(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hf: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  +hl: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  {P.srctext(P.SBP{len, t, d, at}) == String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (lf + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}
  & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool}
  & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool})):
  +V = xs(len, t)
  +A = n(at)
  +L = n(len)
  +FF = n(lf)
  +W = List.drop(&2, U32, V, A)
  +r = D.run_len(W, 10)
  +M = Nat.mul(4n, Nat.pow(2n, d))
  +hF = Equal.trans(Nat, Nat.add(A, r), D.first(V, A, L, 10), FF,
    Equal.sym(Nat, D.first(V, A, L, 10), Nat.add(A, r), T.first_w(V, A, L, hlen(len, t, d, hok))), hf)
  +hle = Equal.trans(Bool, U32.is_le(at, lf), Nat.is_le(A, FF), True{}, U.is_le_to_nat(at, lf),
    AB.subst(Nat, x => {Nat.is_le(A, x) == True{} : Bool}, Nat.add(A, r), FF, hF, N.le_add_r(A, r)))
  +hr = Equal.trans(Nat, n((lf - at : U32)), Nat.sub(FF, A), r, U.to_nat_sub_le(lf, at, hle),
    AB.subst(Nat, x => {Nat.sub(x, A) == r : Nat}, Nat.add(A, r), FF, hF, N.sub_add_l(A, r)))
  +hFM = N.lt_le_trans(FF, L, M, hl, C.ok_len(len, t, d, hok))
  +hF1 = C.inc_fits(lf, d, C.ok_d(len, t, d, hok), hFM)
  +hft = Equal.trans(Bool, Nat.is_le(A, L), U32.is_le(at, len), True{}, Equal.sym(Bool, U32.is_le(at, len), Nat.is_le(A, L), U.is_le_to_nat(at, len)), hs)
  +ht = AB.subst(Nat, x => {Nat.is_le(L, x) == True{} : Bool}, L, List.length(&2, U32, V), Equal.sym(Nat, List.length(&2, U32, V), L, hlen(len, t, d, hok)), N.le_refl(L))
  +hlt = AB.subst(Nat, x => {Nat.is_lt(x, L) == True{} : Bool}, FF, D.first(V, A, L, 10), Equal.sym(Nat, D.first(V, A, L, 10), FF, hf), hl)
  +hhit = AB.subst(Nat, x => {D.has(V, x, 10) == True{} : Bool}, D.first(V, A, L, 10), FF, hf, Q.first_hit(V, A, L, 10, hft, ht, hlt))
  +hd = T.drop_get(V, FF, 10, T.has_get(List.get(&2, U32, V, FF), 10, hhit))
  +R1 = NR.chars(List.take(&2, U32, W, r))
  +D1 = List.drop(&2, U32, V, Nat.add(FF, 1n))
  +RHS = String.append(R1, String.append("\n", NR.chars(D1)))
  +g1 = {
    %Equal.sym(Nat, n((lf - at : U32)), r, hr) :
      {NR.chars(W) == String.append(NR.chars(List.take(&2, U32, W, _)), String.append("\n", NR.chars(List.drop(&2, U32, V, n((lf + 1 : U32)))))) : String}
    %Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(FF, 1n), hF1) :
      {NR.chars(W) == String.append(R1, String.append("\n", NR.chars(List.drop(&2, U32, V, _)))) : String}
    %Equal.sym(List<&2, U32>, W, List.append(&2, U32, List.take(&2, U32, W, r), List.drop(&2, U32, W, r)), T.take_drop(W, r)) :
      {NR.chars(_) == RHS : String}
    %Equal.sym(List<&2, U32>, List.drop(&2, U32, W, r), List.drop(&2, U32, V, Nat.add(A, r)), FA.drop_drop(V, A, r)) :
      {NR.chars(List.append(&2, U32, List.take(&2, U32, W, r), _)) == RHS : String}
    %Equal.sym(Nat, Nat.add(A, r), FF, hF) :
      {NR.chars(List.append(&2, U32, List.take(&2, U32, W, r), List.drop(&2, U32, V, _))) == RHS : String}
    %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, FF), Con{10, D1}, hd) :
      {NR.chars(List.append(&2, U32, List.take(&2, U32, W, r), _)) == RHS : String}
    %Equal.sym(String, NR.chars(List.append(&2, U32, List.take(&2, U32, W, r), Con{10, D1})), String.append(R1, NR.chars(Con{10, D1})),
      S.chars_app(List.take(&2, U32, W, r), Con{10, D1})) :
      {_ == RHS : String}
    {==} : {P.srctext(P.SBP{len, t, d, at}) == String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (lf + 1 : U32)}))) : String}}
  +g2 = AB.subst(Nat, x => {P.nolf(NR.chars(List.take(&2, U32, W, x))) == True{} : Bool}, r, n((lf - at : U32)), Equal.sym(Nat, n((lf - at : U32)), r, hr), T.rl_nolf(W))
  +g3 = Equal.trans(Bool, U32.is_le((lf + 1 : U32), len), Nat.is_le(n((lf + 1 : U32)), L), True{}, U.is_le_to_nat((lf + 1 : U32), len),
    AB.subst(Nat, x => {Nat.is_le(x, L) == True{} : Bool}, Nat.add(FF, 1n), n((lf + 1 : U32)), Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(FF, 1n), hF1), C.succ_le(FF, L, hl)))
  +sl = List.take(&2, U32, W, n((lf - at : U32)))
  +g4 = Equal.trans(Bool, E.is_bytes(NR.chars(sl)), D.all_bytes(sl), True{}, S.bytes_chars(sl),
    SQ.all_bytes_take(W, n((lf - at : U32)), T.all_bytes_drop(V, A, O.view_bytes_t(len, t))))
  (g1, (g2, (g3, g4)))

def src_nolf.go(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hf: {D.first(xs(len, t), n(at), n(len), 10) == n(len) : Nat}) ->
  {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}
  & {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String}:
  +V = xs(len, t)
  +A = n(at)
  +L = n(len)
  +W = List.drop(&2, U32, V, A)
  +r = D.run_len(W, 10)
  +lw = List.length(&2, U32, W)
  +hF = Equal.trans(Nat, Nat.add(A, r), D.first(V, A, L, 10), L,
    Equal.sym(Nat, D.first(V, A, L, 10), Nat.add(A, r), T.first_w(V, A, L, hlen(len, t, d, hok))), hf)
  +hrL = Equal.trans(Nat, r, Nat.sub(Nat.add(A, r), A), Nat.sub(L, A), Equal.sym(Nat, Nat.sub(Nat.add(A, r), A), r, N.sub_add_l(A, r)),
    Equal.cong(Nat, Nat, x => Nat.sub(x, A), Nat.add(A, r), L, hF))
  +hrw = Equal.trans(Nat, r, Nat.sub(L, A), lw, hrL, Equal.sym(Nat, lw, Nat.sub(L, A), hlw(len, t, d, at, hok)))
  +htw = Equal.trans(List<&2, U32>, List.take(&2, U32, W, r), List.take(&2, U32, W, lw), W,
    Equal.cong(Nat, List<&2, U32>, x => List.take(&2, U32, W, x), r, lw, hrw), G.take_all(W))
  +g1 = AB.subst(List<&2, U32>, x => {P.nolf(NR.chars(x)) == True{} : Bool}, List.take(&2, U32, W, r), W, htw, T.rl_nolf(W))
  +hk = Equal.trans(Nat, n((len - at : U32)), Nat.sub(L, A), lw, U.to_nat_sub_le(len, at, hs), Equal.sym(Nat, lw, Nat.sub(L, A), hlw(len, t, d, at, hok)))
  +htk = Equal.trans(List<&2, U32>, List.take(&2, U32, W, n((len - at : U32))), List.take(&2, U32, W, lw), W,
    Equal.cong(Nat, List<&2, U32>, x => List.take(&2, U32, W, x), n((len - at : U32)), lw, hk), G.take_all(W))
  +g2 = Equal.cong(List<&2, U32>, String, x => NR.chars(x), W, List.take(&2, U32, W, n((len - at : U32))), Equal.sym(List<&2, U32>, List.take(&2, U32, W, n((len - at : U32))), W, htk))
  (g1, g2)
