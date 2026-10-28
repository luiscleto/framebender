import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_cache.bend as CA
import ./proof_b_cut.bend as CU
import ./proof_b_run.bend as PR
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_hit.bend as FH
import ./proof_c_adv.bend as CF
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_cache_lem.bend as X
import ./proof_window_lists.bend as WL
import ./proof_b_lit.bend as LT
import ./proof_b_lines_pd.bend as Y
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_nat.bend as LP
import ../lawful-words/proof_nat.bend as NN
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-words/proof_u32.bend as U
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# adv_ok's fast path (norm.bend fast.pre .. fast.wo): a byte-mode body line
# whose cut passes, against the window. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# Run.same with an empty CHROM
# ---------------------------------------------------------------------------

law sub_lez:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.sub(a, b) == 0n : Nat}

def sub_lez(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+(+ap) 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, W.ft(h))
    case 1n+(+ap) 1n+(+bp):
      sub_lez(ap, bp, h)

# Comparing no bytes hands both buffers back.
def nfs0.k(+z: Bool, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +cbl: U32, +cbt: AT.Tree<U32>, +k0: U32,
  +hk: {U32.to_nat(k0) == 0n : Nat}) ->
  &q: Bool -> {NF.same.if(z, C.BT(bl, bt), s, C.BT(cbl, cbt), k0) == (C.BT(bl, bt), (C.BT(cbl, cbt), q)) : D.Bytes & (D.Bytes & Bool)}:
  match z:
    case True{}:
      (True{},
        %Equal.sym(Nat, U32.to_nat(k0), 0n, hk) :
          {BY.same.go(_, BY.at(C.BT(bl, bt), s), BY.at(C.BT(cbl, cbt), 0), s, 0, True{}) == (C.BT(bl, bt), (C.BT(cbl, cbt), True{})) : D.Bytes & (D.Bytes & Bool)};
        %Equal.sym(D.Bytes & U32, BY.at(C.BT(bl, bt), s), (C.BT(bl, bt), C.AT(bl, bt, s)), C.at_pair_t(bl, bt, s)) :
          {BY.same.go(0n, _, BY.at(C.BT(cbl, cbt), 0), s, 0, True{}) == (C.BT(bl, bt), (C.BT(cbl, cbt), True{})) : D.Bytes & (D.Bytes & Bool)};
        %Equal.sym(D.Bytes & U32, BY.at(C.BT(cbl, cbt), 0), (C.BT(cbl, cbt), C.AT(cbl, cbt, 0)), C.at_pair_t(cbl, cbt, 0)) :
          {BY.same.go(0n, (C.BT(bl, bt), C.AT(bl, bt, s)), _, s, 0, True{}) == (C.BT(bl, bt), (C.BT(cbl, cbt), True{})) : D.Bytes & (D.Bytes & Bool)};
        {==})
    case False{}:
      (False{}, {==})

def NFW(+bl: U32, +bt: AT.Tree<U32>, +s: U32, +k0: U32, +cbl: U32, +cbt: AT.Tree<U32>) -> Type:
  &q: Bool -> {NF.same(C.BT(bl, bt), s, k0, C.BT(cbl, cbt)) == (C.BT(bl, bt), (C.BT(cbl, cbt), q)) : D.Bytes & (D.Bytes & Bool)}

def nfs0(+bl: U32, +bt: AT.Tree<U32>, +s: U32, +cbl: U32, +cbt: AT.Tree<U32>, +k0: U32,
  +hk: {U32.to_nat(k0) == 0n : Nat}) -> NFW(bl, bt, s, k0, cbl, cbt):
  nfs0.k(U32.is_eq(k0, cbl), bl, bt, s, cbl, cbt, k0, hk)

# The run's CHROM buffer.
def rcbl(p: P.RunP) -> U32:
  match p:
    case P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      cbl

def rcbt(p: P.RunP) -> AT.Tree<U32>:
  match p:
    case P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      cbt

def RSG(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32) -> Type:
  &q: Bool -> {Norm.Run.same(P.mkRun(p), C.BT(bl, bt), s, e0) == (P.mkRun(p), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)}

def rs0.m(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +s: U32, +e0: U32,
  w: NFW(bl, bt, s, (e0 - s : U32), rcbl(p), rcbt(p))) -> RSG(p, bl, bt, s, e0):
  match p:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      match w:
        case (+q, eq):
          (q, {%Equal.sym(D.Bytes & (D.Bytes & Bool), NF.same(C.BT(bl, bt), s, (e0 - s : U32), C.BT(cbl, cbt)), (C.BT(bl, bt), (C.BT(cbl, cbt), q)), eq) :
              {Norm.Run.same.k(NR.Run{n0, i, h, c, BY.empty(0n), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, x}, _) == (P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)};
            {==} : {Norm.Run.same(P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), C.BT(bl, bt), s, e0) == (P.mkRun(P.RunP{n0, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)}})

# Run.same with an empty CHROM (s = e0): the run and the buffer come back
# as they were (run_same asks s < e0 for its CHROM fact, which is false
# here: before the first run, cb is empty and c is None).
def run_same0(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32,
  hi: {PR.RunInv(p) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  hlt: {U32.is_lt(s, e0) == False{} : Bool},
  he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool}) ->
  &q: Bool -> {Norm.Run.same(P.mkRun(p), C.BT(bl, bt), s, e0) == (P.mkRun(p), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)}:
  +hge = NN.not_lt_le(n(s), n(e0), %U.is_lt_to_nat(s, e0) : {_ == False{} : Bool}; hlt)
  +hk = {%Equal.sym(Nat, n((e0 - s : U32)), Nat.sub(n(e0), n(s)), LP.sub_u(e0, s, hs)) : {_ == 0n : Nat};
    sub_lez(n(e0), n(s), hge) : {n((e0 - s : U32)) == 0n : Nat}}
  rs0.m(p, bl, bt, s, e0, nfs0(bl, bt, s, rcbl(p), rcbt(p), (e0 - s : U32), hk))

law and_f:
  for +q: Bool
  {Bool.and(q, False{}) == False{} : Bool}

def and_f(q):
  match q:
    case True{}:
      {==}
    case False{}:
      {==}


# ---------------------------------------------------------------------------
# The reads the fast path asks (fast.need)
# ---------------------------------------------------------------------------

law cur_eq:
  for +rp: P.RunP
  {Norm.Run.cur(P.mkRun(rp)) == (P.mkRun(rp), Maybe.default(&2, String, P.RunP.c(rp), "")) : NR.Run & String}

def cur_eq(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# Reads that are not empty are what asked keeps.
def ao(+rs: List<&2, Pr.Req>, +hl: {Nat.is_le(1n, List.length(&2, Pr.Req, rs)) == True{} : Bool}) ->
  {Some{rs} == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}:
  match rs:
    case Nil{}:
      Empty.absurd({Some{Nil{}} == S.asked_of(Nil{}) : Maybe<&2, List<&2, Pr.Req>>}, W.ft(hl))
    case Con{+r, +t}:
      {==}

# Reads whose first is on contig c, a contig of bytes of at most 2^28.
def mbr(+rs: List<&2, Pr.Req>, +c: String, +a: Nat,
  +hd: {X.hd1(rs, c, a) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_reqs.k(rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({S.mb_reqs.k(Nil{}) == True{} : Bool}, NN.false_ne_true(hd))
    case Con{Pr.Req{+c1, +a1, +b1}, +t}:
      +ec = WL.string_eq_sound(c1, c, NN.and_true_l(String.eq(c1, c), Nat.is_eq(a1, a), hd))
      %Equal.sym(String, c1, c, ec) : {Bool.and(E.is_bytes(_), Norm.len_le(_, 268435456)) == True{} : Bool}
      W.and_tt(E.is_bytes(c), Norm.len_le(c, 268435456), hcb, hcl)

def rqk_mb(+one: Bool, +c: String, +a: Nat, +e: Nat, +a2: Nat, +e2: Nat,
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_reqs.k(Norm.Req.of.k(one, c, a, e, a2, e2)) == True{} : Bool}:
  match one:
    case True{}:
      W.and_tt(E.is_bytes(c), Norm.len_le(c, 268435456), hcb, hcl)
    case False{}:
      mbr(Norm.parts(c, a, e), c, a, X.ph(Nat.sub(e, a), Norm.le31(Nat.sub(e, a)), c, a, e), hcb, hcl)

# The reads of Req.of are on its contig.
def reqof_mb(+c: String, +a: Nat, +e: Nat,
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_reqs.k(Norm.Req.of(c, a, e)) == True{} : Bool}:
  +a2 = Nat.sub(a, Norm.margin())
  +e2 = Nat.max(e, Nat.add(a, Norm.ahead()))
  rqk_mb(Norm.le31(Nat.sub(e2, a2)), c, a, e, a2, e2, hcb, hcl)

# CHROM's end is at most the line's LF.
def e0_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e0), n(lf)) == True{} : Bool}:
  +h01 = PJ.lf_01(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h23 = PJ.lf_23(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34 = PJ.lf_34(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  NN.lt_to_le(n(e0), n(lf), NN.lt_le_trans(n(e0), n(e7), n(lf),
    NN.lt_trans(n(e0), n(e1), n(e7), h01, NN.lt_trans(n(e1), n(e2), n(e7), h12, NN.lt_trans(n(e2), n(e3), n(e7), h23, NN.lt_trans(n(e3), n(e4), n(e7), h34,
      NN.lt_trans(n(e4), n(e5), n(e7), h45, NN.lt_trans(n(e5), n(e6), n(e7), h56, h67)))))), h7l))

# CHROM is at most w long when the line is (w kept abstract: the checker
# never expands the literal bound).
def chrom_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +e0: U32, +lf: U32, +w: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs0: {Nat.is_le(n(at), n(e0)) == True{} : Bool},
  +h0l: {Nat.is_le(n(e0), n(len)) == True{} : Bool},
  +hel: {Nat.is_le(n(e0), n(lf)) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hsm: {U32.is_le((lf - at : U32), w) == True{} : Bool}) ->
  {Norm.len_le(P.btext(len, t, at, (e0 - at : U32)), w) == True{} : Bool}:
  +X = D.view(C.BT(len, t))
  +sl = D.slice(X, n(at), n((e0 - at : U32)))
  +hfit = {%Equal.sym(Nat, n((e0 - at : U32)), Nat.sub(n(e0), n(at)), LP.sub_u(e0, at, hs0)) : {Nat.is_le(Nat.add(n(at), _), List.length(&2, U32, X)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(e0), n(at))), n(e0), NN.le_sub_add(n(at), n(e0), hs0)) : {Nat.is_le(_, List.length(&2, U32, X)) == True{} : Bool};
    %LP.len_x(len, t, d, hok) : {Nat.is_le(n(e0), _) == True{} : Bool};
    h0l : {Nat.is_le(Nat.add(n(at), n((e0 - at : U32))), List.length(&2, U32, X)) == True{} : Bool}}
  +m1 = {%Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(e0), n(at))), n(e0), NN.le_sub_add(n(at), n(e0), hs0)) : {Nat.is_le(_, n(lf)) == True{} : Bool};
    hel : {Nat.is_le(Nat.add(n(at), Nat.sub(n(e0), n(at))), n(lf)) == True{} : Bool}}
  +m2 = {%LP.sub_u(lf, at, hal) : {Nat.is_le(_, n(w)) == True{} : Bool};
    LI.u2n((lf - at : U32), w, hsm) : {Nat.is_le(Nat.sub(n(lf), n(at)), n(w)) == True{} : Bool}}
  LT.le_len_le(P.btext(len, t, at, (e0 - at : U32)), w,
    %Equal.sym(Nat, String.length(NR.chars(sl)), List.length(&2, U32, sl), LSS.length_chars(sl)) : {Nat.is_le(_, n(w)) == True{} : Bool};
    %Equal.sym(Nat, List.length(&2, U32, sl), n((e0 - at : U32)), LP.slice_len(X, n(at), n((e0 - at : U32)), hfit)) : {Nat.is_le(_, n(w)) == True{} : Bool};
    %Equal.sym(Nat, n((e0 - at : U32)), Nat.sub(n(e0), n(at)), LP.sub_u(e0, at, hs0)) : {Nat.is_le(_, n(w)) == True{} : Bool};
    NN.le_trans(Nat.sub(n(e0), n(at)), Nat.sub(n(lf), n(at)), n(w), LP.le_sub_r(n(at), Nat.sub(n(e0), n(at)), n(lf), m1), m2))

# ---------------------------------------------------------------------------
# The window says it does not hold the record: ask (a Want)
# ---------------------------------------------------------------------------

def F.wt(+reqs: List<&2, Pr.Req>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hmb: {S.mb_reqs.k(reqs) == True{} : Bool},
  h: MSX.RQOK(reqs)) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.Want{Norm.St{o, Norm.MB{P.mkRun(rp)}, Con{Norm.SB{C.BT(len, t), at}, P.mkSrcs(rest)}, P.mkPd(pd), eof, back, CD.mkWin(fa, wp), Some{reqs}, True{}}, reqs}):
  match h:
    case (hok2, q):
      match q:
        case (hrq, hl):
          (LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, Some{reqs}, True{}), ({==}, (hw, (hr, (hok2, (hrq, (ao(reqs, hl), (hx, (hmb, ({==}, hg))))))))))

def F.need(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.need(o, Norm.Run.cur(P.mkRun(rp)), back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(rest, pd, eof), CD.mkWin(fa, wp))):
  +X = D.view(C.BT(len, t))
  +hs0 = PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = DE.j_range(len, t, d, at, lf, hok, hs, Equal.sym(Nat, D.first(X, n(at), n(len), 10), n(lf), hfl))
  +hal = W.and_l(Nat.is_le(n(at), n(lf)), Nat.is_le(n(lf), n(len)), hjr)
  +hcl = chrom_len(len, t, d, at, e0, lf, 268435456, hok, hs0, FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), e0_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), hal, hsm)
  %Equal.sym(NR.Run & String, Norm.Run.cur(P.mkRun(rp)), (P.mkRun(rp), Maybe.default(&2, String, P.RunP.c(rp), "")), cur_eq(rp)) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.need(o, _, back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(rest, pd, eof), CD.mkWin(fa, wp)))
  %Equal.sym(Maybe<&2, String>, P.RunP.c(rp), Some{P.btext(len, t, at, (e0 - at : U32))}, hcr) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.need(o, (P.mkRun(rp), Maybe.default(&2, String, _, "")), back, pos, (e3 - e2 - 1 : U32), C.BT(len, t), at, DE.CX(rest, pd, eof), CD.mkWin(fa, wp)))
  F.wt(Norm.Req.of(P.btext(len, t, at, (e0 - at : U32)), Nat.sub(n(pos), 1n), Nat.add(Nat.sub(n(pos), 1n), n((e3 - e2 - 1 : U32)))), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hx,
    reqof_mb(P.btext(len, t, at, (e0 - at : U32)), Nat.sub(n(pos), 1n), Nat.add(Nat.sub(n(pos), 1n), n((e3 - e2 - 1 : U32))), Y.bytes_btext(len, t, at, (e0 - at : U32)), hcl),
    MSX.reqof_rq(P.btext(len, t, at, (e0 - at : U32)), Nat.sub(n(pos), 1n), Nat.add(Nat.sub(n(pos), 1n), n((e3 - e2 - 1 : U32)))))

# ---------------------------------------------------------------------------
# The window's verdict
# ---------------------------------------------------------------------------

def F.wn(+fneed: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WNeed{}}, DE.CX(rest, pd, eof), fneed)):
  match fneed:
    case True{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, True{}, True{}, hb, hw, hr, hg, hx, hbig)
    case False{}:
      F.need(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, False{}, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm)

# Not a hit: the decoded path (WMiss), or ask (WNeed).
def F.wo(+w: Norm.Wr, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hn: {Norm.Wr.hit(w) == False{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), w}, DE.CX(rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      Empty.absurd(DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WHit{}}, DE.CX(rest, pd, eof), fneed)), W.ft(Equal.sym(Bool, True{}, False{}, hn)))
    case Norm.WNeed{}:
      F.wn(fneed, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm)
    case Norm.WMiss{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)

# A window known in the reference: the hit, or not.
def F.kw(+w: Norm.Wr, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {Bool.pick(String, Norm.Wr.hit(w), P.btext(len, t, at, (e0 - at : U32)), c) == c : String},
  +hrc: {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat((e3 - e2 - 1 : U32))))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, DE.CX(rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      FH.fhit(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, c, a, b, r, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hp, hse, hcr, hsm, hf, hc, hrc, CA.jtruth_ok(fa, c, a, b), PR.run_tick(rp, hi))
    case Norm.WNeed{}:
      F.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case Norm.WMiss{}:
      F.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})

def AHW(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32, +pos: U32, +e2: U32, +e3: U32) -> Type:
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w} : Norm.Wo}
  & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(len, t, at, (e0 - at : U32)), c) == c : String}
  & {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), CD.bases_of(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat((e3 - e2 - 1 : U32))))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>}))

def F.ks(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  h: AHW(fa, c, a, b, r, len, t, at, e0, pos, e2, e3)) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(rest, pd, eof), fneed)):
  match h:
    case (+w, q):
      match q:
        case (eq, q2):
          match q2:
            case (hc, hrc):
              %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, eq) :
                DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(rest, pd, eof), fneed))
              F.kw(w, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, hf, hc, hrc)

# The window not in the reference (find None) asks; a hit or not otherwise.
def F.kn(+m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(rest, pd, eof), fneed))
      F.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case Some{+r}:
      +p = LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hmw = W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +hcb = W.and_l(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      +hcl = W.and_r(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      F.ks(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, em,
        CA.against_hit(fa, c, a, b, r, len, t, d, at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32), hb, em, hcb, hcl, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp),
          FH.ref_fit(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), FH.ref_up(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp),
          PJ.pp_nz(len, t, pos, e0, e1, CU.pass_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), CU.pass_pos_small(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp), FH.ref_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

# A window held as text (the String mode's) does not serve the byte mode.
def F.st(+m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed, Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(rest, pd, eof), fneed))
      F.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case Some{+r}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}}, eq) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed, Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), _, DE.CX(rest, pd, eof), fneed))
      F.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})

# The line passed the cut and the run's CHROM test: against the window.
def F.win(+wp: CD.WP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.wo(back, o, P.mkRun(rp), at, pos, lf, (e3 - e2 - 1 : U32), Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32)), DE.CX(rest, pd, eof), fneed)):
  match wp:
    case CD.WPNone{}:
      F.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPNone{}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case CD.WPUnk{+c}:
      F.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPUnk{c}, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case CD.WPKnown{+c, +a, +b}:
      F.kn(B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})
    case CD.WPStr{+c, +a, +b}:
      F.st(B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, hsm, {==})

# The line's size test.
def F.le(+le: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +ele: {U32.is_le((lf - at : U32), 268435456) == le : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.run.if(le, back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match le:
    case False{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)
    case True{}:
      F.win(wp, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hcr, ele)

# CHROM against the run's (q).
def F.q(+q: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hpk: {Bool.pick(Maybe<&2, String>, q, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp)) == P.RunP.c(rp) : Maybe<&2, String>}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.run.q(back, o, P.mkRun(rp), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), (C.BT(len, t), q), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match q:
    case False{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)
    case True{}:
      %Equal.sym(Bool, U32.is_lt(at, e0), True{}, hse) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.run.if(Bool.and(Bool.and(True{}, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      F.le(U32.is_le((lf - at : U32), 268435456), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse,
        Equal.sym(Maybe<&2, String>, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp), hpk), {==})

def RSW(+rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32) -> Type:
  &q: Bool -> ({Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0) == (P.mkRun(rp), (C.BT(len, t), q)) : NR.Run & (D.Bytes & Bool)}
  & {Bool.pick(Maybe<&2, String>, q, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp)) == P.RunP.c(rp) : Maybe<&2, String>})

def R0W(+rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32) -> Type:
  &q: Bool -> {Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0) == (P.mkRun(rp), (C.BT(len, t), q)) : NR.Run & (D.Bytes & Bool)}

# CHROM not empty: Run.same compares it with the run's.
def F.rs(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  h: RSW(rp, len, t, at, e0)) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, r):
      match r:
        case (eqs, hpk):
          %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
            DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.run(back, o, _, at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
          F.q(q, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, hse, hpk)

# CHROM empty: the decoded path.
def F.r0(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +el: {U32.is_lt(at, e0) == False{} : Bool},
  h: R0W(rp, len, t, at, e0)) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, eqs):
      %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.run(back, o, _, at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, U32.is_lt(at, e0), False{}, el) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.run.if(Bool.and(Bool.and(q, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, Bool.and(q, False{}), False{}, and_f(q)) :
        DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.run.if(Bool.and(_, U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)

def F.lt(+lt: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +el: {U32.is_lt(at, e0) == lt : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, lf, e0, (e2 + 1 : U32), (e3 - e2 - 1 : U32), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match lt:
    case True{}:
      F.rs(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, el, PR.run_same(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), el, FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))
    case False{}:
      F.r0(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hp, el, run_same0(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, CU.pass_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)), el, FH.e0_le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

# The line's cut.
def F.pre(+pr: NF.Pre, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +ep: {CU.pre_of(len, t, at) == pr : NF.Pre}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.pre(back, o, P.mkRun(rp), at, NF.Pr{C.BT(len, t), pr}, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match pr:
    case NF.Pass{+pos, +e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      F.lt(U32.is_lt(at, e0), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, ep, {==})
    case NF.Slow{}:
      CF.fix_ok(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs)
    case NF.Incomplete{}:
      DE.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig)

# adv_ok on the fast path (proof_b_adv.bend's adv.fast).
def F.top(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool}) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.fast.pre(back, o, P.mkRun(rp), at, NF.line(C.BT(len, t), at), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  +p = LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hi = W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  +hso = LI.srcs_head(rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  %Equal.sym(NF.Pr, NF.line(C.BT(len, t), at), NF.Pr{C.BT(len, t), CU.pre_of(len, t, at)}, CU.line_pair(len, t, at)) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.fast.pre(back, o, P.mkRun(rp), at, _, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
  F.pre(CU.pre_of(len, t, at), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, {==})
