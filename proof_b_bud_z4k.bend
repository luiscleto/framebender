import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_cut.bend as CU
import ./proof_b_cache.bend as CA
import ./proof_b_cache_hit.bend as H
import ./proof_b_cache_lem.bend as X
import ./proof_b_enc.bend as PE
import ./proof_b_adv_nat.bend as LP
import ./proof_b_run_bl.bend as RB
import ./proof_b_run_buf.bend as BF
import ./proof_window_lists.bend as WL
import ./proof_b_adv_wf.bend as W
import ./proof_b_bud_vd.bend as BV
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-bytes@0.1.0.0/proof_list.bend as PLS
import lawful-bytes@0.1.0.0/proof_seq.bend as SQ
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Z4's proof (proof_b_bud_z4.bend's against_zero calls against_zero.k): with
# the line's zero window held and fitting (bi's zheld), the fast path's window
# test does not say WNeed. zheld names the window's contig as the CHROM and
# gives a = 0 and POS - 1 + |REF| <= min(b, clen); so the CHROM bytes match
# (chars is injective), cover holds (the window starts at 0 and reaches the
# end of REF; PASS gives 1 <= POS), and fits only picks a miss or a REF test.
# Needs hcl (the window's name is at most 2^28 bytes, as mb_win gives it).

# ---------------------------------------------------------------------------
# Tools
# ---------------------------------------------------------------------------

def zhk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +e: Nat) ->
  {BN.zheld(Norm.win_of.k(c0, a0, b0, clen, off, r), c, e)
    == Bool.and(Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, 0n)), Nat.is_le(Nat.min(e, clen), Nat.min(b0, clen))), Nat.is_le(e, clen)) : Bool}:
  match r:
    case (raw, rl):
      {==}

def shd(+s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{+h, +r}:
      Char.to_u32(h)

def stl(+s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +r}:
      r

def isnil(+s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, +r}:
      False{}

# chars is injective.
def chars_inj(+xs: List<&2, U32>, +ys: List<&2, U32>, +h: {NR.chars(xs) == NR.chars(ys) : String}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +u}:
      Empty.absurd({Nil{} == Con{y, u} : List<&2, U32>}, N.false_ne_true(Equal.sym(Bool, True{}, False{},
        Equal.cong(String, Bool, z => isnil(z), NR.chars(Nil{}), NR.chars(Con{y, u}), h))))
    case Con{+x, +t} Nil{}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, U32>}, N.false_ne_true(
        Equal.cong(String, Bool, z => isnil(z), NR.chars(Con{x, t}), NR.chars(Nil{}), h)))
    case Con{+x, +t} Con{+y, +u}:
      +ex = Equal.cong(String, U32, z => shd(z), NR.chars(Con{x, t}), NR.chars(Con{y, u}), h)
      +et = chars_inj(t, u, Equal.cong(String, String, z => stl(z), NR.chars(Con{x, t}), NR.chars(Con{y, u}), h))
      %ex : {Con{x, t} == Con{_, u} : List<&2, U32>}
      %et : {Con{x, t} == Con{x, _} : List<&2, U32>}
      {==}

def minl(+b: Nat, +l: Nat) -> {Nat.is_le(Nat.min(b, l), b) == True{} : Bool}:
  match b l:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      minl(p, q)

def mineq(+x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.min(x, y) == x : Nat}:
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, N.false_ne_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), p, mineq(p, q, h))

def le1(+x: Nat, +h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_le(1n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+q:
      N.le_zero_l(q)

# A slice inside the list has the length asked.
def slen(+xs: List<&2, U32>, +i: Nat, +k: Nat, +h: {Nat.is_le(Nat.add(i, k), List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.length(&2, U32, D.slice(xs, i, k)) == k : Nat}:
  +L0 = List.length(&2, U32, xs)
  +hk0 = AB.subst(Nat, z => {Nat.is_le(z, Nat.sub(L0, i)) == True{} : Bool}, Nat.sub(Nat.add(i, k), i), k, BV.sub_add_l(i, k), X.sub_mono(Nat.add(i, k), L0, i, h))
  +hk = AB.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, Nat.sub(L0, i), List.length(&2, U32, List.drop(&2, U32, xs, i)),
    Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, xs, i)), Nat.sub(L0, i), LP.len_drop(xs, i)), hk0)
  SQ.take_length(List.drop(&2, U32, xs, i), k, hk)

def wpk(+x: Bool, w: Norm.Win, b: D.Bytes) -> {BD.wo_need(Norm.Wo{w, b, Bool.pick(Norm.Wr, x, Norm.WHit{}, Norm.WMiss{})}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------------------------------------------------------------------------
# The window as its mirrors (a = 0): the CHROM test passes, cover holds
# ---------------------------------------------------------------------------

def z4.f(+fv: Bool, +c: String, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32, +pos: U32, +e2: U32, +e3: U32, +cbl: U32, +cbt: AT.Tree<U32>,
  +hzv: {U32.is_eq((e0 - at : U32), cbl) == True{} : Bool},
  +hv: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(len, t), at, C.BT(cbl, cbt), 0, (e0 - at : U32)))) == True{} : Bool},
  +hc: {Bool.and(U32.is_le(U32.from_nat(Nat.min(0n, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), (U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32))) == True{} : Bool},
  +hfv: {U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)) == fv : Bool}) ->
  {BD.wo_need(Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  match fv:
    case False{}:
      AB.subst(Norm.Wo, z => {BD.wo_need(z) == False{} : Bool}, Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), Norm.WMiss{}}, Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)),
        Equal.sym(Norm.Wo, Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), Norm.WMiss{}}, CA.ah.f0(c, 0n, b, r, len, t, at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32), cbl, cbt, hzv, hv, hc, hfv)), {==})
    case True{}:
      AB.subst(Norm.Wo, z => {BD.wo_need(z) == False{} : Bool}, Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), Bool.pick(Norm.Wr, H.RQG(U32.to_nat((e3 - e2 - 1 : U32)), len, t, U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b)), (e2 + 1 : U32), ((pos - 1 : U32) - U32.from_nat(Nat.min(0n, String.length(r))) : U32), True{}), Norm.WHit{}, Norm.WMiss{})}, Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)),
        Equal.sym(Norm.Wo, Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), Bool.pick(Norm.Wr, H.RQG(U32.to_nat((e3 - e2 - 1 : U32)), len, t, U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b)), (e2 + 1 : U32), ((pos - 1 : U32) - U32.from_nat(Nat.min(0n, String.length(r))) : U32), True{}), Norm.WHit{}, Norm.WMiss{})},
          CA.ah.q(c, 0n, b, r, len, t, at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32), cbl, cbt, hzv, hv, hc, hfv, H.RQG(U32.to_nat((e3 - e2 - 1 : U32)), len, t, U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b)), (e2 + 1 : U32), ((pos - 1 : U32) - U32.from_nat(Nat.min(0n, String.length(r))) : U32), True{}), {==})),
        wpk(H.RQG(U32.to_nat((e3 - e2 - 1 : U32)), len, t, U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b)), (e2 + 1 : U32), ((pos - 1 : U32) - U32.from_nat(Nat.min(0n, String.length(r))) : U32), True{}), Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t)))

def z4.c(+c: String, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +e0: U32, +pos: U32, +e2: U32, +e3: U32,
  +cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +ec: {c == P.btext(len, t, at, (e0 - at : U32)) : String},
  +hs0: {Nat.is_le(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool},
  +he0: {Nat.is_le(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hb31: {Norm.le31(b) == True{} : Bool},
  +hE: {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)) == True{} : Bool},
  +hmin: {Nat.is_le(Nat.min(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)), Nat.min(b, String.length(r))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  +k = U32.to_nat((e0 - at : U32))
  +SLb = D.slice(D.view(C.BT(len, t)), U32.to_nat(at), k)
  +VB0 = D.view(C.BT(cbl, cbt))
  +hsU = Equal.trans(Bool, U32.is_le(at, e0), Nat.is_le(U32.to_nat(at), U32.to_nat(e0)), True{}, U.is_le_to_nat(at, e0), hs0)
  +ek = U.to_nat_sub_le(e0, at, hsU)
  +hi1 = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(at), w), U32.to_nat(len)) == True{} : Bool}, Nat.sub(U32.to_nat(e0), U32.to_nat(at)), k, Equal.sym(Nat, k, Nat.sub(U32.to_nat(e0), U32.to_nat(at)), ek),
    AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(len)) == True{} : Bool}, U32.to_nat(e0), Nat.add(U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at))),
      Equal.sym(Nat, Nat.add(U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at))), U32.to_nat(e0), N.le_sub_add(U32.to_nat(at), U32.to_nat(e0), hs0)), he0))
  +hi2 = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(at), k), w) == True{} : Bool}, U32.to_nat(len), List.length(&2, U32, D.view(C.BT(len, t))), LP.len_x(len, t, d, hok), hi1)
  +evl = chars_inj(VB0, SLb, Equal.trans(String, NR.chars(VB0), c, P.btext(len, t, at, (e0 - at : U32)), htx, ec))
  +elen = Equal.trans(Nat, U32.to_nat(cbl), List.length(&2, U32, VB0), k, LP.len_x(cbl, cbt, cbd, okcb),
    Equal.trans(Nat, List.length(&2, U32, VB0), List.length(&2, U32, SLb), k, Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), VB0, SLb, evl),
      slen(D.view(C.BT(len, t)), U32.to_nat(at), k, hi2)))
  +hzv = {%Equal.sym(Bool, U32.is_eq((e0 - at : U32), cbl), Nat.is_eq(k, U32.to_nat(cbl)), U.is_eq_to_nat((e0 - at : U32), cbl)) : {_ == True{} : Bool};
    %elen : {Nat.is_eq(_, U32.to_nat(cbl)) == True{} : Bool};
    N.eq_refl(U32.to_nat(cbl)) : {U32.is_eq((e0 - at : U32), cbl) == True{} : Bool}}
  +en = U.is_eq_true((e0 - at : U32), cbl, hzv)
  +hj1 = AB.subst(U32, w => {Nat.is_le(Nat.add(U32.to_nat(0), U32.to_nat(w)), U32.to_nat(cbl)) == True{} : Bool}, cbl, (e0 - at : U32), Equal.sym(U32, (e0 - at : U32), cbl, en), N.le_refl(U32.to_nat(cbl)))
  +V = Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(len, t), at, C.BT(cbl, cbt), 0, (e0 - at : U32))))
  +SLc = D.slice(VB0, U32.to_nat(0), k)
  +hvl = SM.same_view_t(len, t, cbl, cbt, d, cbd, at, 0, (e0 - at : U32), hok, okcb, hi1, hj1)
  +ev = Equal.trans(List<&2, U32>, SLc, D.slice(VB0, U32.to_nat(0), U32.to_nat(cbl)), VB0,
    Equal.cong(U32, List<&2, U32>, z => D.slice(VB0, U32.to_nat(0), U32.to_nat(z)), (e0 - at : U32), cbl, en), BF.view_all(cbl, cbt, cbd, okcb))
  +hle = AB.subst(List<&2, U32>, z => {D.list_eq(SLb, z) == True{} : Bool}, SLb, SLc,
    Equal.trans(List<&2, U32>, SLb, VB0, SLc, Equal.sym(List<&2, U32>, VB0, SLb, evl), Equal.sym(List<&2, U32>, SLc, VB0, ev)), PLS.list_eq_refl(SLb))
  +hv = Equal.trans(Bool, V, D.list_eq(SLb, SLc), True{}, hvl, hle)
  +h1p = {%Equal.sym(Bool, U32.is_le(1, pos), Nat.is_le(U32.to_nat(1), U32.to_nat(pos)), U.is_le_to_nat(1, pos)) : {_ == True{} : Bool};
    le1(U32.to_nat(pos), hpz) : {U32.is_le(1, pos) == True{} : Bool}}
  +ep = U.to_nat_sub_le(pos, 1, h1p)
  +ML = Nat.min(b, String.length(r))
  +LL = String.length(CD.letters(r, 0n, b))
  +ell = Equal.trans(Nat, LL, Nat.sub(ML, Nat.min(0n, String.length(r))), ML, CA.len_letters(r, 0n, b), N.sub_zero(ML))
  +hLb = AB.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, ML, LL, Equal.sym(Nat, LL, ML, ell), minl(b, String.length(r)))
  +eR = X.le31_fit(LL, X.le31_mono(LL, b, hLb, hb31))
  +eE = AB.subst(Nat, z => {Nat.is_le(z, ML) == True{} : Bool}, Nat.min(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), mineq(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r), hE), hmin)
  +hEL = AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), z) == True{} : Bool}, LL, U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))), Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))), LL, eR),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), z) == True{} : Bool}, ML, LL, Equal.sym(Nat, LL, ML, ell), eE))
  +hfit1 = AB.subst(Nat, z => {Nat.is_lt(Nat.add(z, U32.to_nat((e3 - e2 - 1 : U32))), Nat.pow(2n, 32n)) == True{} : Bool}, Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((pos - 1 : U32)),
    Equal.sym(Nat, U32.to_nat((pos - 1 : U32)), Nat.sub(U32.to_nat(pos), 1n), ep), N.le_lt_trans(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))), Nat.pow(2n, 32n), hEL, U.to_nat_lt_p(U32.from_nat(String.length(CD.letters(r, 0n, b))))))
  +eadd1 = U.to_nat_add_fits_p((pos - 1 : U32), (e3 - e2 - 1 : U32), hfit1)
  +e0R = {{==} : {U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))) == Nat.add(U32.to_nat(U32.from_nat(Nat.min(0n, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b))))) : Nat}}
  +hfit2 = AB.subst(Nat, z => {Nat.is_lt(z, Nat.pow(2n, 32n)) == True{} : Bool}, U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))), Nat.add(U32.to_nat(U32.from_nat(Nat.min(0n, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b))))), e0R, U.to_nat_lt_p(U32.from_nat(String.length(CD.letters(r, 0n, b)))))
  +eadd2 = U.to_nat_add_fits_p(U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), hfit2)
  +c1 = {%Equal.sym(Bool, U32.is_le(U32.from_nat(Nat.min(0n, String.length(r))), (pos - 1 : U32)), Nat.is_le(U32.to_nat(U32.from_nat(Nat.min(0n, String.length(r)))), U32.to_nat((pos - 1 : U32))), U.is_le_to_nat(U32.from_nat(Nat.min(0n, String.length(r))), (pos - 1 : U32))) : {_ == True{} : Bool};
    N.le_zero_l(U32.to_nat((pos - 1 : U32))) : {U32.is_le(U32.from_nat(Nat.min(0n, String.length(r))), (pos - 1 : U32)) == True{} : Bool}}
  +c2 = {%Equal.sym(Bool, U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), (U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32)), Nat.is_le(U32.to_nat(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32)), U32.to_nat((U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32))), U.is_le_to_nat(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), (U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32))) : {_ == True{} : Bool};
    %Equal.sym(Nat, U32.to_nat(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32)), Nat.add(U32.to_nat((pos - 1 : U32)), U32.to_nat((e3 - e2 - 1 : U32))), eadd1) : {Nat.is_le(_, U32.to_nat((U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32))) == True{} : Bool};
    %Equal.sym(Nat, U32.to_nat((U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32)), Nat.add(U32.to_nat(U32.from_nat(Nat.min(0n, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b))))), eadd2) : {Nat.is_le(Nat.add(U32.to_nat((pos - 1 : U32)), U32.to_nat((e3 - e2 - 1 : U32))), _) == True{} : Bool};
    %Equal.sym(Nat, U32.to_nat((pos - 1 : U32)), Nat.sub(U32.to_nat(pos), 1n), ep) : {Nat.is_le(Nat.add(_, U32.to_nat((e3 - e2 - 1 : U32))), Nat.add(U32.to_nat(U32.from_nat(Nat.min(0n, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, 0n, b)))))) == True{} : Bool};
    hEL : {U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), (U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32)) == True{} : Bool}}
  +hc = W.and_tt(U32.is_le(U32.from_nat(Nat.min(0n, String.length(r))), (pos - 1 : U32)), U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), (U32.from_nat(Nat.min(0n, String.length(r))) + U32.from_nat(String.length(CD.letters(r, 0n, b))) : U32)), c1, c2)
  z4.f(U32.is_le(((pos - 1 : U32) + (e3 - e2 - 1 : U32) : U32), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)), c, b, r, len, t, at, e0, pos, e2, e3, cbl, cbt, hzv, hv, hc, {==})

def z4.o2(+cbl: U32, +cbt: AT.Tree<U32>, +cbd: Nat, +fa: List<&2, B.Contig>, +c: String, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32, +e0: U32, +e2: U32, +e3: U32,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +eos: {NR.of_str(c) == C.BT(cbl, cbt) : D.Bytes},
  +okcb: {D.ok(C.BT(cbl, cbt), cbd) == True{} : Bool},
  +htx: {NR.chars(D.view(C.BT(cbl, cbt))) == c : String},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ec: {c == P.btext(len, t, at, (e0 - at : U32)) : String},
  +hs0: {Nat.is_le(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool},
  +he0: {Nat.is_le(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hb31: {Norm.le31(b) == True{} : Bool},
  +hE: {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)) == True{} : Bool},
  +hmin: {Nat.is_le(Nat.min(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)), Nat.min(b, String.length(r))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, 0n, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  AB.subst(Norm.Win, x => {BD.wo_need(Norm.against(x, C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}, Norm.WKnown{c, C.BT(cbl, cbt), 0n, b, String.length(r), Nat.min(0n, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, 0n, b))), PE.enc_t(CD.letters(r, 0n, b))), U32.from_nat(Nat.min(0n, String.length(r))), U32.from_nat(String.length(CD.letters(r, 0n, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(0n, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, 0n, b}),
    CA.ah.mk(fa, c, 0n, b, r, cbl, cbt, hf, eos),
    z4.c(c, b, r, len, t, d, at, e0, pos, e2, e3, cbl, cbt, cbd, hok, okcb, htx, ec, hs0, he0, hpz, hb31, hE, hmin))

def z4.o(+fa: List<&2, B.Contig>, +c: String, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32, +e0: U32, +e2: U32, +e3: U32,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  hofs: &l: U32 -> &tt: AT.Tree<U32> -> &dd: Nat -> ({NR.of_str(c) == C.BT(l, tt) : D.Bytes} & ({D.ok(C.BT(l, tt), dd) == True{} : Bool} & {NR.chars(D.view(C.BT(l, tt))) == c : String})),
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +ec: {c == P.btext(len, t, at, (e0 - at : U32)) : String},
  +hs0: {Nat.is_le(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool},
  +he0: {Nat.is_le(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hb31: {Norm.le31(b) == True{} : Bool},
  +hE: {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)) == True{} : Bool},
  +hmin: {Nat.is_le(Nat.min(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)), Nat.min(b, String.length(r))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, 0n, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  (cbl, h1) = hofs
  (cbt, h2) = h1
  (cbd, h3) = h2
  (eos, h4) = h3
  (okcb, htx) = h4
  z4.o2(cbl, cbt, cbd, fa, c, b, r, len, t, d, at, pos, e0, e2, e3, hf, eos, okcb, htx, hok, ec, hs0, he0, hpz, hb31, hE, hmin)

def z4.s(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32, +e0: U32, +e2: U32, +e3: U32,
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs0: {Nat.is_le(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool},
  +he0: {Nat.is_le(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hz2: {BN.zheld(CD.mkWin.k(Some{r}, c, a, b, False{}), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  +Qe = String.eq(c, P.btext(len, t, at, (e0 - at : U32)))
  +LA = Nat.is_le(a, 0n)
  +LM = Nat.is_le(Nat.min(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r)), Nat.min(b, String.length(r)))
  +LE = Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))), String.length(r))
  +ZK = Bool.and(Bool.and(Bool.and(Qe, LA), LM), LE)
  +ZW = BN.zheld(Norm.win_of.k(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(CD.letters(r, a, b)))), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))))
  +hz3 = Equal.trans(Bool, ZK, ZW, True{}, Equal.sym(Bool, ZW, ZK, zhk(c, a, b, String.length(r), Nat.min(a, String.length(r)), BY.len(E.enc(CD.letters(r, a, b))), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32))))), hz2)
  +hA3 = W.and_l(Bool.and(Bool.and(Qe, LA), LM), LE, hz3)
  +hE = W.and_r(Bool.and(Bool.and(Qe, LA), LM), LE, hz3)
  +hA2 = W.and_l(Bool.and(Qe, LA), LM, hA3)
  +hmin = W.and_r(Bool.and(Qe, LA), LM, hA3)
  +ec = WL.string_eq_sound(c, P.btext(len, t, at, (e0 - at : U32)), W.and_l(Qe, LA, hA2))
  +ea = X.le_zero_eq(a, W.and_r(Qe, LA, hA2))
  +hcb = AB.subst(String, z => {E.is_bytes(z) == True{} : Bool}, P.btext(len, t, at, (e0 - at : U32)), c, Equal.sym(String, c, P.btext(len, t, at, (e0 - at : U32)), ec), RB.btext_bytes(len, t, at, (e0 - at : U32)))
  +hwp0 = AB.subst(Nat, z => {CD.wp_ok(fa, CD.WPKnown{c, z, b}) == True{} : Bool}, a, 0n, ea, hwp)
  +hb31 = AB.subst(Nat, z => {Norm.le31(z) == True{} : Bool}, Nat.sub(b, 0n), b, N.sub_zero(b), hwp0)
  AB.subst(Nat, z => {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, z, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}, 0n, a, Equal.sym(Nat, a, 0n, ea),
    z4.o(fa, c, b, r, len, t, d, at, pos, e0, e2, e3, hf, H.ofs(c, hcb, hcl), hok, ec, hs0, he0, hpz, hb31, hE, hmin))

def z4.m(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32, +e0: U32, +e2: U32, +e3: U32,
  +hf: {B.Fasta.find(fa, c) == m : Maybe<&2, String>},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs0: {Nat.is_le(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool},
  +he0: {Nat.is_le(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hz: {BN.zheld(CD.mkWin(fa, CD.WPKnown{c, a, b}), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  match m:
    case None{}:
      +hz2 = AB.subst(Maybe<&2, String>, z => {BN.zheld(CD.mkWin.k(z, c, a, b, False{}), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}, B.Fasta.find(fa, c), None{}, hf, hz)
      Empty.absurd({BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}, N.false_ne_true(hz2))
    case Some{+r}:
      z4.s(fa, c, a, b, r, len, t, d, at, pos, e0, e2, e3, hf, hwp, hcl, hok, hs0, he0, hpz,
        AB.subst(Maybe<&2, String>, z => {BN.zheld(CD.mkWin.k(z, c, a, b, False{}), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}, B.Fasta.find(fa, c), Some{r}, hf, hz))

# against_zero with hcl (the statement in proof_b_bud_z4.bend).
def against_zero.k(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hz: {BN.zheld(CD.mkWin(fa, CD.WPKnown{c, a, b}), P.btext(len, t, at, (e0 - at : U32)), Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}) ->
  {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}:
  +hs0 = PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +he0 = FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)
  +hpz = PJ.pp_nz(len, t, pos, e0, e1, CU.pass_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  z4.m(B.Fasta.find(fa, c), fa, c, a, b, len, t, d, at, pos, e0, e2, e3, {==}, hwp, hcl, hok, hs0, he0, hpz, hz)
