import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_cut.bend as CU
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_cache.bend as CA
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_cache_lem.bend as X
import ./proof_window_lists.bend as WL
import ./proof_b_lit.bend as LT
import ./proof_b_lines_pd.bend as Y
import ./proof_b_lines_str.bend as LSS
import lawful-words@0.1.0.0/proof_nat.bend as NN
import lawful-bytes@0.1.0.0/bytes.bend as BY
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_c_cache.bend as CC
import ./proof_c_advf.bend as AF
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_budget_dec.bend as BDe
import ./proof_c_bud_hit.bend as BH

# Phase C: the budget on the rewrite path (norm.bend fix .. fix.tick),
# generated from proof_c_adv.bend: the same walk with BD.AdvC in place of
# DE.DG, nothing asked, bi carried; the declined cases are BDe.c.dec, the
# window's hit is proof_c_bud_hit.bend. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

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

# Not a hit: the decoded path (WMiss), or ask (WNeed).
def K.wo(+w: Norm.Wr, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hn: {Norm.Wr.hit(w) == False{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), w}, DE.CX(rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      Empty.absurd(BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.Wo{CD.mkWin(fa, wp), C.BT(len, t), Norm.WHit{}}, DE.CX(rest, pd, eof), fneed)), W.ft(Equal.sym(Bool, True{}, False{}, hn)))
    case Norm.WNeed{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case Norm.WMiss{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

# A window known in the reference: the hit, or not.
def K.kw(+w: Norm.Wr, +c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {Bool.pick(String, Norm.Wr.hit(w), P.btext(len, t, at, (e0 - at : U32)), c) == c : String},
  +hrc: {Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat((e3 - (e2 + 1 : U32) : U32))))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, DE.CX(rest, pd, eof), fneed)):
  match w:
    case Norm.WHit{}:
      BH.hit(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hf)
    case Norm.WNeed{}:
      K.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case Norm.WMiss{}:
      K.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})

def AHW(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +r: String, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32, +pos: U32, +e2: U32, +e3: U32) -> Type:
  &w: Norm.Wr -> ({Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w} : Norm.Wo}
  & ({Bool.pick(String, Norm.Wr.hit(w), P.btext(len, t, at, (e0 - at : U32)), c) == c : String}
  & ({Bool.pick(Maybe<&2, Bool>, Norm.Wr.hit(w),
      J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat((e3 - (e2 + 1 : U32) : U32))))),
      Some{True{}}) == Some{True{}} : Maybe<&2, Bool>} & {Bool.pick(Bool, Norm.Wr.hit(w), Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), True{}) == True{} : Bool})))

def K.ks(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  h: AHW(fa, c, a, b, r, len, t, at, e0, pos, e2, e3)) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), DE.CX(rest, pd, eof), fneed)):
  match h:
    case (+w, q):
      match q:
        case (eq, q2):
          match q2:
            case (hc, q3):
              match q3:
                case (hrc, hfs):
                  %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), w}, eq) :
                    BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, _, DE.CX(rest, pd, eof), fneed))
                  K.kw(w, c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs)

# The window not in the reference (find None) asks; a hit or not otherwise.
def K.kn(+m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), DE.CX(rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, False{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), Norm.Wo{CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed), Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, _, DE.CX(rest, pd, eof), fneed))
      K.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case Some{+r}:
      +p = LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, None{}, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hmw = W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +hcb = W.and_l(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      +hcl = W.and_r(E.is_bytes(c), Norm.len_le(c, 268435456), hmw)
      K.ks(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, em,
        CC.against_hit_lc(fa, c, a, b, r, len, t, d, at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32), hb, em, hcb, hcl, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), AF.e0le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp),
          AF.reffit(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), AF.reflets(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp),
          AF.posnz(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), AF.possmall(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), AF.rlpos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

# A window held as text (the String mode's) does not serve the byte mode.
def K.st(+m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +em: {B.Fasta.find(fa, c) == m : Maybe<&2, String>}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), DE.CX(rest, pd, eof), fneed)):
  match m:
    case None{}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), None{}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WNeed{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed), Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, _, DE.CX(rest, pd, eof), fneed))
      K.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case Some{+r}:
      +eq = {%Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, c), Some{r}, em) :
          {Norm.against(CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin.k(_, c, a, b, True{}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo};
        {==} : {Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)) == Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}} : Norm.Wo}}
      %Equal.sym(Norm.Wo, Norm.against(CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), Norm.Wo{CD.mkWin(fa, CD.WPStr{c, a, b}), C.BT(len, t), Norm.WMiss{}}, eq) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, None{}, fneed), Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, _, DE.CX(rest, pd, eof), fneed))
      K.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPStr{c, a, b}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})

# The line passed the cut and the run's CHROM test: against the window.
def K.win(+wp: CD.WP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.wo(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, lf, als, up, Norm.against(CD.mkWin(fa, wp), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - (e2 + 1 : U32) : U32)), DE.CX(rest, pd, eof), fneed)):
  match wp:
    case CD.WPNone{}:
      K.wo(Norm.WNeed{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPNone{}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case CD.WPUnk{+c}:
      K.wo(Norm.WMiss{}, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPUnk{c}, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case CD.WPKnown{+c, +a, +b}:
      K.kn(B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})
    case CD.WPStr{+c, +a, +b}:
      K.st(B.Fasta.find(fa, c), c, a, b, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, {==})

# The line's size test.
def K.le(+le: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +ele: {U32.is_le((lf - at : U32), 268435456) == le : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.if(le, back, o, P.mkRun(rp), C.BT(len, t), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match le:
    case False{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case True{}:
      K.win(wp, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, ele)

# CHROM against the run's (q).
def K.q(+q: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hpk: {Bool.pick(Maybe<&2, String>, q, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp)) == P.RunP.c(rp) : Maybe<&2, String>}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.run.q(back, o, P.mkRun(rp), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, (C.BT(len, t), q), DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match q:
    case False{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case True{}:
      %Equal.sym(Bool, U32.is_lt(at, e0), True{}, hse) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix.if(Bool.and(Bool.and(True{}, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      K.le(U32.is_le((lf - at : U32), 268435456), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse,
        Equal.sym(Maybe<&2, String>, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp), hpk), {==})

def RSW(+rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32) -> Type:
  &q: Bool -> ({Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0) == (P.mkRun(rp), (C.BT(len, t), q)) : NR.Run & (D.Bytes & Bool)}
  & {Bool.pick(Maybe<&2, String>, q, Some{P.btext(len, t, at, (e0 - at : U32))}, P.RunP.c(rp)) == P.RunP.c(rp) : Maybe<&2, String>})

def R0W(+rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +e0: U32) -> Type:
  &q: Bool -> {Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0) == (P.mkRun(rp), (C.BT(len, t), q)) : NR.Run & (D.Bytes & Bool)}

# CHROM not empty: Run.same compares it with the run's.
def K.rs(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  h: RSW(rp, len, t, at, e0)) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, r):
      match r:
        case (eqs, hpk):
          %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
            BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix.run(back, o, _, at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
          K.q(q, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hpk)

# CHROM empty: the decoded path.
def K.r0(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +el: {U32.is_lt(at, e0) == False{} : Bool},
  h: R0W(rp, len, t, at, e0)) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match h:
    case (+q, eqs):
      %Equal.sym(NR.Run & (D.Bytes & Bool), Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), (P.mkRun(rp), (C.BT(len, t), q)), eqs) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix.run(back, o, _, at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, U32.is_lt(at, e0), False{}, el) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix.if(Bool.and(Bool.and(q, _), U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      %Equal.sym(Bool, Bool.and(q, False{}), False{}, and_f(q)) :
        BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed), Norm.fix.if(Bool.and(_, U32.is_le((lf - at : U32), 268435456)), back, o, P.mkRun(rp), C.BT(len, t), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

def K.lt(+lt: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +el: {U32.is_lt(at, e0) == lt : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.run(back, o, Norm.Run.same(P.mkRun(rp), C.BT(len, t), at, e0), at, pos, NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, e0, e2, e3, lf, als, up, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match lt:
    case True{}:
      K.rs(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, el, PR.run_same(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), el, AF.e0le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
    case False{}:
      K.r0(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, el, run_same0(rp, len, t, d, at, e0, hi, hok, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), el, AF.e0le(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))


# ---------------------------------------------------------------------------
# NX.line's verdict
# ---------------------------------------------------------------------------

def K.cut(+c: NF.Cut, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +ep: {Q.fx_of(len, t, at) == NX.Fix{pos, c, als, up} : NX.Fp}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.pre(back, o, P.mkRun(rp), at, NX.Fr{C.BT(len, t), NX.Fix{pos, c, als, up}}, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match c:
    case NF.Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      K.lt(U32.is_lt(at, e0), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, ep, {==})
    case NF.Short{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)
    case NF.Part{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

def K.fp(+fp: NX.Fp, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +ep: {Q.fx_of(len, t, at) == fp : NX.Fp}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.pre(back, o, P.mkRun(rp), at, NX.Fr{C.BT(len, t), fp}, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  match fp:
    case NX.Fix{+pos, +c, +als, +up}:
      K.cut(c, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, pos, als, up, ep)
    case NX.No{}:
      BDe.c.dec(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi)

# adv_ok on the fast path's NF.Slow (proof_b_adv_fast.bend's F.pre).
def fix_ok(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hbi: {BN.biS(S.mkSt(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}) ->
  BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix(back, o, P.mkRun(rp), C.BT(len, t), at, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed)):
  %Equal.sym(NX.Fr, NX.line(C.BT(len, t), at), NX.Fr{C.BT(len, t), Q.fx_of(len, t, at)}, PE.line_pair(len, t, at)) :
    BD.AdvC(fa, cs, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, None{}, fneed),
    Norm.fix.pre(back, o, P.mkRun(rp), at, _, DE.CX(rest, pd, eof), CD.mkWin(fa, wp), fneed))
  K.fp(Q.fx_of(len, t, at), fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, fneed, hb, hw, hr, hg, hx, hbig, hbi, hin, hi, hok, hs, {==})
