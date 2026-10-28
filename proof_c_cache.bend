import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm.bend as Norm
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./proof_window_defs.bend as WS
import ./proof_b_defs.bend as P
import ./proof_b_fasteq.bend as FE
import ./norm_fast.bend as NF
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ./proof_b_cache_lem.bend as X
import ./proof_b_cache_te.bend as TE
import ./proof_b_cache_hit.bend as H
import ./proof_b_enc_lem.bend as EL
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-words/proof_u32.bend as U
import ./proof_b_enc.bend as PE
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-arrays/proof_base.bend as AB
import ./proof_window_lists.bend as WL
import ./proof_b_cachedefs.bend as CD
import ./proof_b_cache.bend as CA
import ./proof_c_defs.bend as Q
import ./norm_fix.bend as NX

# Phase C: proof_b_cache.bend's against_hit for a REF in either case (the
# rewrite path's alleles): the fast path's REF test passed means the String
# path's REF check passes, with REF's bases as Q.BF reads them. The chain is
# proof_b_cache.bend's (f3.f .. against_hit), copied with CD.up -> Q.lets,
# CD.bases_of -> Q.BF and H.bq -> bq_l; its other helpers are CA's.

# One byte: a letter A, C, G, T, N (either case) and a byte equal to it up to
# case read as the same base (checked by computation for each letter and
# every byte below 256, as proof_b_cache_hit.bend's pb).
def okb(+x: U32, +y: U32) -> Bool:
  Bool.or(Bool.not(H.zq(x, y)), B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)))

def chk(k: Nat, +x: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+(+p):
      okb(x, U32.from_nat(p)) && chk(p, x)

def chk.k(+q: Nat, +x: U32, +p: Nat, +e: Bool, +he: {Nat.is_eq(p, q) == e : Bool},
  +h: {Bool.and(okb(x, U32.from_nat(q)), chk(q, x)) == True{} : Bool},
  +hp: {Nat.is_lt(p, 1n+q) == True{} : Bool},
  ih: {Nat.is_lt(p, q) == True{} : Bool} -> {okb(x, U32.from_nat(p)) == True{} : Bool}) ->
  {okb(x, U32.from_nat(p)) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, p, q, N.eq_sound(p, q, he)) : {okb(x, U32.from_nat(_)) == True{} : Bool}
      N.and_true_l(okb(x, U32.from_nat(q)), chk(q, x), h)
    case False{}:
      +hle = Equal.trans(Bool, Nat.is_le(p, q), Nat.is_lt(p, 1n+q), True{}, Equal.sym(Bool, Nat.is_lt(p, 1n+q), Nat.is_le(p, q), N.lt_succ_iff(p, q)), hp)
      ih(Equal.trans(Bool, Nat.is_lt(p, q), Nat.is_le(1n+p, q), True{}, Equal.sym(Bool, Nat.is_le(1n+p, q), Nat.is_lt(p, q), N.le_succ_lt(p, q)), N.le_ne(p, q, hle, he)))

def chk_ok(+k: Nat, +x: U32, +h: {chk(k, x) == True{} : Bool}, +p: Nat, +hp: {Nat.is_lt(p, k) == True{} : Bool}) ->
  {okb(x, U32.from_nat(p)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({okb(x, U32.from_nat(p)) == True{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, N.lt_zero(p)), hp)))
    case 1n+q:
      chk.k(q, x, p, Nat.is_eq(p, q), {==}, h, hp, hl => chk_ok(q, x, N.and_true_r(okb(x, U32.from_nat(q)), chk(q, x), h), p, hl))

def okb_y(+x: U32, +y: U32, +hc: {chk(256n, x) == True{} : Bool}, +hy: {U32.is_lt(y, 256) == True{} : Bool}) ->
  {okb(x, y) == True{} : Bool}:
  +hp = Equal.trans(Bool, Nat.is_lt(U32.to_nat(y), 256n), U32.is_lt(y, 256), True{}, Equal.sym(Bool, U32.is_lt(y, 256), Nat.is_lt(U32.to_nat(y), 256n), U.is_lt_to_nat(y, 256)), hy)
  AB.subst(U32, z => {okb(x, z) == True{} : Bool}, U32.from_nat(U32.to_nat(y)), y, U.from_nat_to_nat(y), chk_ok(256n, x, hc, U32.to_nat(y), hp))

def okb_eq(+x: U32, +y: U32, +h: {okb(x, y) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  AB.subst(Bool, z => {Bool.or(Bool.not(z), B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x))) == True{} : Bool}, H.zq(x, y), True{}, hz, h)

def pb.w(+x: U32, +w: U32, +y: U32, +hw: {x == w : U32}, +hc: {chk(256n, w) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  %Equal.sym(U32, x, w, hw) : {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(_)) == True{} : Bool}
  okb_eq(w, y, okb_y(w, y, hc, hy), AB.subst(U32, z => {H.zq(z, y) == True{} : Bool}, x, w, hw, hz))

# The letters NX.isl accepts: x is the k-th or a later one (e: it is the
# k-th), one level per letter.
def pb10(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 110) == e : Bool}, +h: {e == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 110, y, U.is_eq_true(x, 110, he), {==}, hy, hz)
    case False{}:
      Empty.absurd({B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}, N.false_ne_true(h))

def pb9(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 116) == e : Bool}, +h: {Bool.or(e, U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 116, y, U.is_eq_true(x, 116, he), {==}, hy, hz)
    case False{}:
      pb10(x, y, U32.is_eq(x, 110), {==}, h, hy, hz)

def pb8(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 103) == e : Bool}, +h: {Bool.or(Bool.or(e, U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 103, y, U.is_eq_true(x, 103, he), {==}, hy, hz)
    case False{}:
      pb9(x, y, U32.is_eq(x, 116), {==}, h, hy, hz)

def pb7(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 99) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 99, y, U.is_eq_true(x, 99, he), {==}, hy, hz)
    case False{}:
      pb8(x, y, U32.is_eq(x, 103), {==}, h, hy, hz)

def pb6(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 97) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 97, y, U.is_eq_true(x, 97, he), {==}, hy, hz)
    case False{}:
      pb7(x, y, U32.is_eq(x, 99), {==}, h, hy, hz)

def pb5(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 78) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 78, y, U.is_eq_true(x, 78, he), {==}, hy, hz)
    case False{}:
      pb6(x, y, U32.is_eq(x, 97), {==}, h, hy, hz)

def pb4(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 84) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 84, y, U.is_eq_true(x, 84, he), {==}, hy, hz)
    case False{}:
      pb5(x, y, U32.is_eq(x, 78), {==}, h, hy, hz)

def pb3(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 71) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 71, y, U.is_eq_true(x, 71, he), {==}, hy, hz)
    case False{}:
      pb4(x, y, U32.is_eq(x, 84), {==}, h, hy, hz)

def pb2(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 67) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 67, y, U.is_eq_true(x, 67, he), {==}, hy, hz)
    case False{}:
      pb3(x, y, U32.is_eq(x, 71), {==}, h, hy, hz)

def pb1(+x: U32, +y: U32, +e: Bool, +he: {U32.is_eq(x, 65) == e : Bool}, +h: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(e, U32.is_eq(x, 67)), U32.is_eq(x, 71)), U32.is_eq(x, 84)), U32.is_eq(x, 78)), U32.is_eq(x, 97)), U32.is_eq(x, 99)), U32.is_eq(x, 103)), U32.is_eq(x, 116)), U32.is_eq(x, 110)) == True{} : Bool},
  +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  match e:
    case True{}:
      pb.w(x, 65, y, U.is_eq_true(x, 65, he), {==}, hy, hz)
    case False{}:
      pb2(x, y, U32.is_eq(x, 67), {==}, h, hy, hz)

# A letter A, C, G, T, N (either case) and a byte below 256 equal to it up to
# case: the same base.
def pb_l(+x: U32, +y: U32, +hx: {NX.isl(x) == True{} : Bool}, +hy: {U32.is_lt(y, 256) == True{} : Bool}, +hz: {H.zq(x, y) == True{} : Bool}) ->
  {B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)) == True{} : Bool}:
  pb1(x, y, U32.is_eq(x, 65), {==}, hx, hy, hz)

# REF bytes (letters, either case) equal up to case to letter bytes: their
# bases are the letters' bases (proof_b_cache_hit.bend's bq).
def bq_l(+xs: List<&2, U32>, +ys: List<&2, U32>,
  +hr: {H.rql(xs, ys) == True{} : Bool},
  +hu: {Q.lets(xs) == True{} : Bool},
  +hb: {D.all_bytes(ys) == True{} : Bool},
  +hl: {List.length(&2, U32, xs) == List.length(&2, U32, ys) : Nat}) ->
  {B.Bases.eq(B.Bases.of_fasta(Norm.chars(ys)), Q.BF(xs)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({B.Bases.eq(B.Bases.of_fasta(Norm.chars(Con{y, yt})), Q.BF(Nil{})) == True{} : Bool}, N.zero_ne_succ(List.length(&2, U32, yt), hl))
    case Con{x, xt} Nil{}:
      Empty.absurd({B.Bases.eq(B.Bases.of_fasta(Norm.chars(Nil{})), Q.BF(Con{x, xt})) == True{} : Bool}, N.succ_ne_zero(List.length(&2, U32, xt), hl))
    case Con{x, xt} Con{y, yt}:
      +hz = N.and_true_l(H.zq(x, y), H.rql(xt, yt), hr)
      +hx = N.and_true_l(NX.isl(x), Q.lets(xt), hu)
      +hy = N.and_true_l(U32.is_lt(y, 256), D.all_bytes(yt), hb)
      %Equal.sym(Bool, B.Base.is_eq(B.Base.of_fasta(Chr{y}), Q.bf(x)), True{}, pb_l(x, y, hx, hy, hz)) :
        {Bool.and(_, B.Bases.eq(B.Bases.of_fasta(Norm.chars(yt)), Q.BF(xt))) == True{} : Bool}
      bq_l(xt, yt, N.and_true_r(H.zq(x, y), H.rql(xt, yt), hr), N.and_true_r(NX.isl(x), Q.lets(xt), hu), N.and_true_r(U32.is_lt(y, 256), D.all_bytes(yt), hb), N.succ_inj(List.length(&2, U32, xt), List.length(&2, U32, yt), hl))

def len_BF(+xs: List<&2, U32>) -> {List.length(&2, B.Base, Q.BF(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Base, Q.BF(t)), List.length(&2, U32, t), len_BF(t))

def f3_f_lc(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hoff31: {Norm.fits31(Nat.min(a, String.length(r))) == True{} : Bool},
  +hL31: {Norm.fits31(String.length(r)) == True{} : Bool},
  +hfit1: {U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(String.length(r))) == True{} : Bool},
  +okrw: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool},
  +viewrw: {D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  +lt = CD.letters(r, a, b)
  +off = Nat.min(a, String.length(r))
  +l = String.length(r)
  +nr = U32.to_nat(rl)
  +st = Nat.sub(U32.to_nat(pos), 1n)
  +W31 = Nat.pow(2n, 31n)
  +toff = H.f31_eq(off, hoff31)
  +tLL = H.f31_eq(l, hL31)
  +ep = H.tpp(pos, hp)
  +tend = H.tend(pos, rl, bl, bt, bd, rs, hok, hr, hp, hps)
  +hlL = N.le_trans(String.length(lt), Nat.min(b, l), l,
    AB.subst(Nat, z => {Nat.is_le(z, Nat.min(b, l)) == True{} : Bool}, Nat.sub(Nat.min(b, l), Nat.min(a, l)), String.length(lt), Equal.sym(Nat, String.length(lt), Nat.sub(Nat.min(b, l), Nat.min(a, l)), CA.len_letters(r, a, b)), X.sub_le(Nat.min(b, l), Nat.min(a, l))),
    H.min_le_r(b, l))
  +hl31 = X.le31_mono(String.length(lt), l, hlL, H.fits_le31(l, hL31))
  +tlen = X.le31_fit(String.length(lt), hl31)
  +hc1u = N.and_true_l(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), hcov)
  +hc2u = N.and_true_r(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), hcov)
  +c1a = Equal.trans(Bool, Nat.is_le(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat((pos - 1 : U32))), U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), True{}, Equal.sym(Bool, U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), Nat.is_le(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat((pos - 1 : U32))), U.is_le_to_nat(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32))), hc1u)
  +c1b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat((pos - 1 : U32))) == True{} : Bool}, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff, c1a)
  +c1 = AB.subst(Nat, z => {Nat.is_le(off, z) == True{} : Bool}, U32.to_nat((pos - 1 : U32)), st, ep, c1b)
  +hOl = AB.subst(Nat, z => {Nat.is_lt(z, W31) == True{} : Bool}, off, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff), H.f31_lt(off, hoff31))
  +hRl = AB.subst(Nat, z => {Nat.is_le(z, W31) == True{} : Bool}, String.length(lt), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen),
    N.lt_to_le(String.length(lt), W31, N.le_lt_trans(String.length(lt), l, W31, hlL, H.f31_lt(l, hL31))))
  +tsum0 = U.to_nat_add_fits_p(U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), H.sum32(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), hOl, hRl))
  +c2a = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), hc2u)
  +c2b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(st, nr), tend, c2a)
  +c2c = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), z) == True{} : Bool}, U32.to_nat((U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32)), Nat.add(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b))))), tsum0, c2b)
  +c2d = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(z, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))))) == True{} : Bool}, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff, c2c)
  +c2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(off, z)) == True{} : Bool}, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen, c2d)
  +c3a = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(U32.from_nat(l))), U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(l)), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(l)), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(U32.from_nat(l))), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), U32.from_nat(l))), hfit1)
  +c3b = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(U32.from_nat(l))) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(st, nr), tend, c3a)
  +c3 = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), z) == True{} : Bool}, U32.to_nat(U32.from_nat(l)), l, tLL, c3b)
  +K0 = Nat.sub(st, off)
  +tq = Equal.trans(Nat, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), Nat.sub(U32.to_nat((pos - 1 : U32)), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), K0, U.to_nat_sub_le((pos - 1 : U32), U32.from_nat(Nat.min(a, String.length(r))), hc1u),
    Equal.trans(Nat, Nat.sub(U32.to_nat((pos - 1 : U32)), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), Nat.sub(st, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), K0,
      Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r))))), U32.to_nat((pos - 1 : U32)), st, ep),
      Equal.cong(Nat, Nat, z => Nat.sub(st, z), U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), off, toff)))
  +hj = H.sub_lin(st, off, nr, String.length(lt), c2, c1)
  +hj2 = AB.subst(Nat, z => {Nat.is_le(Nat.add(z, nr), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b))))) == True{} : Bool}, K0, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), Equal.sym(Nat, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), K0, tq),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(K0, nr), z) == True{} : Bool}, String.length(lt), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(lt), tlen), hj))
  +hrql = H.rq_val(nr, bl, bt, bd, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), E.depth(String.length(lt)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}, hok, okrw, hr, hj2, hrq)
  +Y = D.slice(E.codes(lt), K0, nr)
  +hrql2 = AB.subst(Nat, z => {H.rql(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), D.slice(E.codes(lt), z, nr)) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), K0, tq,
    AB.subst(List<&2, U32>, z => {H.rql(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), D.slice(z, U32.to_nat(((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32)), nr)) == True{} : Bool}, D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))), E.codes(lt), viewrw, hrql))
  +hvs = Equal.trans(Nat, List.length(&2, U32, D.view(C.BT(bl, bt))), D.size(C.BT(bl, bt)), U32.to_nat(bl), O.view_size_t(bl, bt, bd, hok), {==})
  +hlX = H.sl_len(D.view(C.BT(bl, bt)), U32.to_nat(rs), nr, AB.subst(Nat, z => {Nat.is_le(Nat.add(U32.to_nat(rs), nr), z) == True{} : Bool}, U32.to_nat(bl), List.length(&2, U32, D.view(C.BT(bl, bt))), Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(bl, bt))), U32.to_nat(bl), hvs), hr))
  +hlY = H.sl_len(E.codes(lt), K0, nr, AB.subst(Nat, z => {Nat.is_le(Nat.add(K0, nr), z) == True{} : Bool}, String.length(lt), List.length(&2, U32, E.codes(lt)), EL.length_codes(lt), hj))
  +hbc = Equal.trans(Bool, D.all_bytes(E.codes(lt)), E.is_bytes(lt), True{}, EL.bytes_codes(lt), CA.letters_bytes(r, a, b, hbr))
  +hbq = bq_l(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)), Y, hrql2, hu, H.ab_slice(E.codes(lt), K0, nr, hbc), Equal.trans(Nat, List.length(&2, U32, D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, List.length(&2, U32, Y), hlX, Equal.sym(Nat, List.length(&2, U32, Y), nr, hlY)))
  +S2 = String.take(String.drop(lt, K0), nr)
  +eY = Equal.sym(List<&2, U32>, E.codes(S2), Y, Equal.trans(List<&2, U32>, E.codes(S2), List.take(&2, U32, E.codes(String.drop(lt, K0)), nr), Y,
    X.codes_take(String.drop(lt, K0), nr), Equal.cong(List<&2, U32>, List<&2, U32>, z => List.take(&2, U32, z, nr), E.codes(String.drop(lt, K0)), List.drop(&2, U32, E.codes(lt), K0), X.codes_drop(lt, K0))))
  +eC = Equal.trans(String, Norm.chars(Y), Norm.chars(E.codes(S2)), S2, Equal.cong(List<&2, U32>, String, z => Norm.chars(z), Y, E.codes(S2), eY),
    Pair.snd({E.chars(E.codes(S2)) == S2 : String}, {Norm.chars(E.codes(S2)) == S2 : String}, PE.chars_codes(S2)))
  +eF = Equal.trans(List<&2, B.Base>, B.Bases.of_fasta(S2), List.take(&2, B.Base, B.Bases.of_fasta(String.drop(lt, K0)), nr), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr),
    WL.of_fasta_take(String.drop(lt, K0), nr), Equal.cong(List<&2, B.Base>, List<&2, B.Base>, z => List.take(&2, B.Base, z, nr), B.Bases.of_fasta(String.drop(lt, K0)), List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), WL.of_fasta_drop(lt, K0)))
  +heq = AB.subst(List<&2, B.Base>, z => {B.Bases.eq(z, Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == True{} : Bool}, B.Bases.of_fasta(Norm.chars(Y)), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr),
    Equal.trans(List<&2, B.Base>, B.Bases.of_fasta(Norm.chars(Y)), B.Bases.of_fasta(S2), List.take(&2, B.Base, List.drop(&2, B.Base, B.Bases.of_fasta(lt), K0), nr), Equal.cong(String, List<&2, B.Base>, z => B.Bases.of_fasta(z), Norm.chars(Y), S2, eC), eF), hbq)
  +hnb = Equal.trans(Nat, List.length(&2, B.Base, Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), List.length(&2, U32, D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, len_BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), hlX)
  +c2f = AB.subst(Nat, z => {Nat.is_le(Nat.add(st, nr), Nat.add(off, z)) == True{} : Bool}, String.length(lt), List.length(&2, B.Base, B.Bases.of_fasta(lt)), Equal.sym(Nat, List.length(&2, B.Base, B.Bases.of_fasta(lt)), String.length(lt), WL.of_fasta_len(lt)), c2)
  H.rc(l, off, B.Bases.of_fasta(lt), st, Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))), nr, hnb, c3, c1, c2f, heq)

def f3_e_lc(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hoff31: {Norm.fits31(Nat.min(a, String.length(r))) == True{} : Bool},
  +hL31: {Norm.fits31(String.length(r)) == True{} : Bool},
  +hfit1: {U32.is_le(((pos - 1 : U32) + rl : U32), U32.from_nat(String.length(r))) == True{} : Bool},
  h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}))) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  (h1, h234) = h
  (h2, h34) = h234
  f3_f_lc(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, hoff31, hL31, hfit1, h1, h2)

def f3_k_lc(+fb: Bool, +r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hfb: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == fb : Bool},
  +hfit: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  match fb:
    case True{}:
      +hfit1 = AB.subst(Bool, z => {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, z, U32.from_nat(String.length(r)), 0)) == True{} : Bool}, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}, hfb, hfit)
      +hl31 = X.le31_mono(String.length(CD.letters(r, a, b)), String.length(r), N.le_trans(String.length(CD.letters(r, a, b)), Nat.min(b, String.length(r)), String.length(r),
        AB.subst(Nat, z => {Nat.is_le(z, Nat.min(b, String.length(r))) == True{} : Bool}, Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), String.length(CD.letters(r, a, b)), Equal.sym(Nat, String.length(CD.letters(r, a, b)), Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), CA.len_letters(r, a, b)), X.sub_le(Nat.min(b, String.length(r)), Nat.min(a, String.length(r)))),
        H.min_le_r(b, String.length(r))), H.fits_le31(String.length(r), N.and_true_r(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb)))
      f3_e_lc(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, N.and_true_l(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb), N.and_true_r(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfb), hfit1,
        PE.enc_ok(CD.letters(r, a, b), CA.letters_bytes(r, a, b, hbr), hl31))
    case False{}:
      +nr = U32.to_nat(rl)
      +hfit0 = AB.subst(Bool, z => {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, z, U32.from_nat(String.length(r)), 0)) == True{} : Bool}, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), False{}, hfb, hfit)
      +n0 = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U32.is_le(((pos - 1 : U32) + rl : U32), 0), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), 0), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), 0)), hfit0)
      +n1 = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(0)) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), H.tend(pos, rl, bl, bt, bd, rs, hok, hr, hp, hps), n0)
      +ez = N.add_eq_zero_r(Nat.sub(U32.to_nat(pos), 1n), nr, X.le_zero_eq(Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), n1))
      +hlt = Equal.trans(Bool, Nat.is_lt(U32.to_nat(0), nr), U32.is_lt(0, rl), True{}, Equal.sym(Bool, U32.is_lt(0, rl), Nat.is_lt(U32.to_nat(0), nr), U.is_lt_to_nat(0, rl)), hrl)
      Empty.absurd({J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}, N.false_ne_true(AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(0), z) == True{} : Bool}, nr, 0n, ez, hlt)))

def f3_lc(+r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hcov: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hrq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == True{} : Bool},
  +hfit: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool}) ->
  {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))) == Some{True{}} : Maybe<&2, Bool>}:
  f3_k_lc(Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hcov, hrq, {==}, hfit)


# A hit's window offset and contig length fit 31 bits (else the cached
# window's clenu is 0 and no REF fits it).
def fits_k(+fb: Bool, +r: String, +a: Nat, +b: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +pos: U32, +rs: U32, +rl: U32,
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hfb: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == fb : Bool},
  +hfit: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool}) ->
  {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}:
  match fb:
    case True{}:
      hfb
    case False{}:
      +nr = U32.to_nat(rl)
      +hfit0 = AB.subst(Bool, z => {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, z, U32.from_nat(String.length(r)), 0)) == True{} : Bool}, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), False{}, hfb, hfit)
      +n0 = Equal.trans(Bool, Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U32.is_le(((pos - 1 : U32) + rl : U32), 0), True{}, Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + rl : U32), 0), Nat.is_le(U32.to_nat(((pos - 1 : U32) + rl : U32)), U32.to_nat(0)), U.is_le_to_nat(((pos - 1 : U32) + rl : U32), 0)), hfit0)
      +n1 = AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(0)) == True{} : Bool}, U32.to_nat(((pos - 1 : U32) + rl : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), H.tend(pos, rl, bl, bt, bd, rs, hok, hr, hp, hps), n0)
      +ez = N.add_eq_zero_r(Nat.sub(U32.to_nat(pos), 1n), nr, X.le_zero_eq(Nat.add(Nat.sub(U32.to_nat(pos), 1n), nr), n1))
      +hlt = Equal.trans(Bool, Nat.is_lt(U32.to_nat(0), nr), U32.is_lt(0, rl), True{}, Equal.sym(Bool, U32.is_lt(0, rl), Nat.is_lt(U32.to_nat(0), nr), U.is_lt_to_nat(0, rl)), hrl)
      Empty.absurd({Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}, N.false_ne_true(AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(0), z) == True{} : Bool}, nr, 0n, ez, hlt)))

def ah_lq_lc(+eqv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == True{} : Bool},
  +hq: {H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}) == eqv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  match eqv:
    case True{}:
      (Norm.WHit{}, (CA.ah.q(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf, True{}, hq),
        (H.f2(bl, bt, bd, s, e0, c, cbl, cbt, cbd, hok, okcb, htx, hs, he, hz, hv),
          (f3_lc(r, a, b, bl, bt, bd, pos, rs, rl, hbr, hok, hr, hu, hp, hps, hrl, hc, hq, hf), fits_k(Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), r, a, b, bl, bt, bd, pos, rs, rl, hok, hr, hp, hps, hrl, {==}, hf)))))
    case False{}:
      (Norm.WMiss{}, (CA.ah.q(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf, False{}, hq), ({==}, ({==}, {==}))))

def ah_lf_lc(+fv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == True{} : Bool},
  +hf: {U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == fv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  match fv:
    case True{}:
      ah_lq_lc(H.RQG(U32.to_nat(rl), bl, bt, U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b)), rs, ((pos - 1 : U32) - U32.from_nat(Nat.min(a, String.length(r))) : U32), True{}), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, hc, hf, {==})
    case False{}:
      (Norm.WMiss{}, (CA.ah.f0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc, hf), ({==}, ({==}, {==}))))

def ah_lc_lc(+cv: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))) == cv : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  match cv:
    case True{}:
      ah_lf_lc(U32.is_le(((pos - 1 : U32) + rl : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, hc, {==})
    case False{}:
      (Norm.WNeed{}, (CA.ah.c0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv, hc), ({==}, ({==}, {==}))))

def ah_lv_lc(+v: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))) == v : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  match v:
    case True{}:
      ah_lc_lc(Bool.and(U32.is_le(U32.from_nat(Nat.min(a, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + rl : U32), (U32.from_nat(Nat.min(a, String.length(r))) + U32.from_nat(String.length(CD.letters(r, a, b))) : U32))), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, hv, {==})
    case False{}:
      (Norm.WNeed{}, (CA.ah.v0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz, hv), ({==}, ({==}, {==}))))

def ah_lz_lc(+z: Bool, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +hz: {U32.is_eq((e0 - s : U32), cbl) == z : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  match z:
    case True{}:
      ah_lv_lc(Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(bl, bt), s, C.BT(cbl, cbt), 0, (e0 - s : U32)))), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, hz, {==})
    case False{}:
      (Norm.WNeed{}, (CA.ah.z0(c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, hz), ({==}, ({==}, {==}))))

# The window the picture stands for, with its buffers as mirrors.
def ah_mk_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +cbl: U32, +cbt: AT.Tree<U32>,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +eos: {NR.of_str(c) == C.BT(cbl, cbt) : D.Bytes}) ->
  {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win}:
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hf) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin.k(_, c, a, b, False{}) : Norm.Win}
  %Equal.sym(D.Bytes, NR.of_str(c), C.BT(cbl, cbt), eos) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == Norm.WKnown{c, _, a, b, String.length(r), Nat.min(a, String.length(r)), E.enc(CD.letters(r, a, b)), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} : Norm.Win}
  %Equal.sym(D.Bytes, E.enc(CD.letters(r, a, b)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), PE.enc_bt(CD.letters(r, a, b))) : {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), _, U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} : Norm.Win}
  {==}

def ah_m_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  g: &w: Norm.Wr -> ({Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool})))) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  (w, rest) = g
  (e1, cs) = rest
  (w, (AB.subst(Norm.Win, x => {Norm.against(x, C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{x, C.BT(bl, bt), w} : Norm.Wo}, Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), PE.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, a, b}), emk, e1), cs))

def ah_o_lc(+cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  +eos: {NR.of_str(c) == C.BT(cbl, cbt) : D.Bytes},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  ah_m_lc(fa, c, a, b, r, bl, bt, s, e0, pos, rs, rl, cbl, cbt, ah_mk_lc(fa, c, a, b, r, cbl, cbt, hf, eos),
    ah_lz_lc(U32.is_eq((e0 - s : U32), cbl), c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, cbl, cbt, cbd, hbr, hok, okcb, htx, hs, he, hr, hu, hp, hps, hrl, {==}))

def ah_k_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool},
  h: &l: U32 -> &t: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(c) == C.BT(l, t) : D.Bytes} & ({D.ok(C.BT(l, t), d) == True{} : Bool} & {NR.chars(D.view(C.BT(l, t))) == c : String}))) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  (cbl, h1) = h
  (cbt, h2) = h1
  (cbd, h3) = h2
  (eos, h4) = h3
  (okcb, htx) = h4
  ah_o_lc(cbl, cbt, cbd, fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, hbr, hf, hok, hs, he, hr, hu, hp, hps, hrl, eos, okcb, htx)

def ah_top_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  +he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  +hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  +hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  +hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  +hrl: {U32.is_lt(0, rl) == True{} : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo} & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String} & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w), J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))), Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  ah_k_lc(fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, CA.find_bytes(fa, c, r, hb, hf), hf, hok, hs, he, hr, hu, hp, hps, hrl, H.ofs(c, hcb, hcl))

# jtruth_ok, for the contig found (m).
def jt_k_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +m: Maybe<&2, String>,
  +hm: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  {WS.truthful(fa, c, Some{CD.jtruth.k(m, a, b)}) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, hm) : {Maybe.is_none(&2, String, _) == True{} : Bool}
      {==}
    case Some{r}:
      +n = String.length(r)
      +raw = CD.letters(r, a, b)
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, hm) :
        {WS.known.ok(_, n, Nat.min(a, n), raw) == True{} : Bool}
      %Equal.sym(String, String.drop(r, Nat.min(a, n)), String.drop(r, a), X.drop_min(r, a)) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, String.take(_, String.length(raw)))) == True{} : Bool}
      %Equal.sym(String, String.take(String.drop(r, a), String.length(raw)), raw, X.take_len_take(String.drop(r, a), Nat.sub(b, a))) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, _)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.eq_refl(n)) : {Bool.and(_, String.eq(raw, raw)) == True{} : Bool}
      X.str_eq_refl(raw)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# The reads of a window: each within 2^31 letters, at least one, and all but
# the last full (so a window of n letters takes at most n / 2^31 + 1 reads).
def parts_ok_lc(+c: String, +a: Nat, +b: Nat) ->
  {E.reqs_ok(Norm.parts(c, a, b)) == True{} : Bool}
  & ({Nat.is_le(1n, List.length(&2, Pr.Req, Norm.parts(c, a, b))) == True{} : Bool}
  & {Nat.is_le(List.length(&2, Pr.Req, Norm.parts(c, a, b)), Nat.max(1n, Nat.sub(b, a))) == True{} : Bool}):
  +x = Nat.sub(b, a)
  (Equal.trans(Bool, E.reqs_ok(Norm.parts(c, a, b)), X.rok31(Norm.parts(c, a, b)), True{}, CA.rok31_eq(Norm.parts(c, a, b)),
      X.p31(x, Norm.le31(x), c, a, b, {==}, N.le_refl(x))),
    (X.pl1(x, Norm.le31(x), c, a, b),
      X.pmax(x, Norm.le31(x), c, a, b, {==}, N.le_refl(x))))

# The answers to a window's reads, kept: the window of the picture wpOf
# (a picture the machine can have).
def win_truths_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  hb: {CD.fa_bytes(fa) == True{} : Bool}) ->
  {Norm.win_of(Norm.parts(c, a, b), M.truths(fa, Norm.parts(c, a, b))) == CD.mkWin(fa, CD.wpOf(fa, c, a, b)) : Norm.Win}
  & {CD.wp_ok(fa, CD.wpOf(fa, c, a, b)) == True{} : Bool}:
  (CA.wt.k(B.Fasta.find(fa, c), Norm.le31(Nat.sub(b, a)), fa, c, a, b, hb, {==}, {==}),
    CA.wo.k(B.Fasta.find(fa, c), fa, c, a, b, {==}))

# serve answers truthfully from a window that holds the read, and leaves the
# window as it was; else it answers nothing.
def serve_ok_lc(+fa: List<&2, B.Contig>, +wp: CD.WP, +c: String, +a: Nat, +b: Nat,
  hb: {CD.fa_bytes(fa) == True{} : Bool},
  hv: {CD.wp_ok(fa, wp) == True{} : Bool}) ->
  {Norm.serve(CD.mkWin(fa, wp), c, a, b) ==
    Norm.Sv{CD.mkWin(fa, wp), Bool.pick(Maybe<&2, J.Ans>, CD.holds(fa, wp, c, a, b), Some{CD.jtruth(fa, c, a, b)}, None{}), Bool.pick(Nat, CD.holds(fa, wp, c, a, b), CD.wp.clen(fa, c), 0n)} : Norm.Sv}:
  CA.sv.k(fa, wp, c, a, b, hb, hv)

# After asking Req.of(c, a, e), the window (CD.wpReq) holds the read (a, e):
# the slow path's retry is answered.
def req_holds_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +e: Nat) ->
  {CD.holds(fa, CD.wpReq(fa, c, a, e), c, a, e) == True{} : Bool}:
  CA.rq.p(fa, c, a, e, Norm.le31(Nat.sub(Nat.max(e, Nat.add(a, Norm.ahead())), Nat.sub(a, Norm.margin()))))

# The truthful answer is truthful in the window laws' sense.
def jtruth_ok_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat) ->
  {WS.truthful(fa, c, Some{CD.jtruth(fa, c, a, b)}) == True{} : Bool}:
  jt_k_lc(fa, c, a, b, B.Fasta.find(fa, c), {==})

# The fast path's window test: the window and the line's buffer are handed
# back; a hit means CHROM is the window's contig and the String path's REF
# check passes on the window's letters (REF: rl upper-case ACGTN bytes from
# rs, at least one; POS pos >= 1 and below 10^9, as its at most 9 digits
# make it).
def against_hit_lc(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String,
  +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32, +pos: U32, +rs: U32, +rl: U32,
  hb: {CD.fa_bytes(fa) == True{} : Bool},
  hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool},
  hr: {Nat.is_le(Nat.add(U32.to_nat(rs), U32.to_nat(rl)), U32.to_nat(bl)) == True{} : Bool},
  hu: {Q.lets(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl))) == True{} : Bool},
  hp: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  hps: {U32.is_lt(pos, 1000000000) == True{} : Bool},
  hrl: {U32.is_lt(0, rl) == True{} : Bool}) ->
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), s, e0, pos, rs, rl) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(bl, bt), w} : Norm.Wo}
  & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(bl, bt, s, (e0 - s : U32)), c) == c : String}
  & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(bl, bt)), U32.to_nat(rs), U32.to_nat(rl)))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}))):
  ah_top_lc(fa, c, a, b, r, bl, bt, bd, s, e0, pos, rs, rl, hb, hf, hcb, hcl, hok, hs, he, hr, hu, hp, hps, hrl)

