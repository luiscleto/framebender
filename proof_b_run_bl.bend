import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_run_flush.bend as FL
import ./proof_b_run_fin.bend as FN
import ./proof_b_run_add.bend as AD
import ./proof_b_run_sr.bend as SR
import ./proof_b_run_kd.bend as KD
import ./proof_b_lit.bend as PL
import ./proof_run_base.bend as RBS
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_seq.bend as Q
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_index.bend as I
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ./proof_b_enc_lem.bend as X

# The body-line deliverables of proof_b_run.bend (fast_done, same_done,
# body_line) from keyed and same_run on pictured runs.

# Sizes
# =====

# x < 2^b and y <= 2^a + 1 give x + y <= 2^e (b = 1 + a, e = 1 + b).
law szk:
  for +x: Nat
  for +y: Nat
  for +a: Nat
  for +b: Nat
  for +e: Nat
  for +h1: {1n+a == b : Nat}
  for +h2: {1n+b == e : Nat}
  for +hx: {Nat.is_lt(x, Nat.pow(2n, b)) == True{} : Bool}
  for +hy: {Nat.is_le(y, Nat.add(Nat.pow(2n, a), 1n)) == True{} : Bool}
  {Nat.is_le(Nat.add(x, y), Nat.pow(2n, e)) == True{} : Bool}

def szk(x, y, a, b, e, h1, h2, hx, hy):
  +A = Nat.pow(2n, a)
  +Bp = Nat.pow(2n, b)
  +h1a = Equal.trans(Bool, Nat.is_le(1n, A), Nat.is_lt(0n, A), True{}, N.le_succ_lt(0n, A), N.pow_pos(a))
  +hyA = N.le_trans(y, Nat.add(A, 1n), Nat.add(A, A), hy, N.le_add_mono_l(A, 1n, A, h1a))
  +hyB = AB.subst(Nat, z => {Nat.is_le(y, z) == True{} : Bool}, Nat.add(A, A), Bp,
    Equal.trans(Nat, Nat.add(A, A), Nat.pow(2n, 1n+a), Bp, Equal.sym(Nat, Nat.pow(2n, 1n+a), Nat.add(A, A), NM.pow_dbl(a)), Equal.cong(Nat, Nat, z => Nat.pow(2n, z), 1n+a, b, h1)), hyA)
  +hs = N.le_trans(Nat.add(x, y), Nat.add(Bp, y), Nat.add(Bp, Bp), N.le_add_mono_r(y, x, Bp, N.lt_to_le(x, Bp, hx)), N.le_add_mono_l(Bp, y, Bp, hyB))
  AB.subst(Nat, z => {Nat.is_le(Nat.add(x, y), z) == True{} : Bool}, Nat.add(Bp, Bp), Nat.pow(2n, e),
    Equal.trans(Nat, Nat.add(Bp, Bp), Nat.pow(2n, 1n+b), Nat.pow(2n, e), Equal.sym(Nat, Nat.pow(2n, 1n+b), Nat.add(Bp, Bp), NM.pow_dbl(b)), Equal.cong(Nat, Nat, z => Nat.pow(2n, z), 1n+b, e, h2)), hs)

# 2^a < 4 * 2^b for a <= b.
law p_lt4:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.pow(2n, a), Nat.mul(4n, Nat.pow(2n, b))) == True{} : Bool}

def p_lt4(a, b, h):
  +X = Nat.pow(2n, b)
  +Y = Nat.add(X, Nat.add(X, Nat.add(X, 0n)))
  +hY = N.lt_le_trans(0n, X, Y, N.pow_pos(b), N.le_add_r(X, Nat.add(X, Nat.add(X, 0n))))
  +hX = AB.subst(Nat, z => {Nat.is_lt(z, Nat.add(X, Y)) == True{} : Bool}, Nat.add(X, 0n), X, N.add_zero(X), N.lt_add_l(X, 0n, Y, hY))
  N.le_lt_trans(Nat.pow(2n, a), X, Nat.add(X, Y), N.pow_le(a, b, h), hX)

# The machine's size checks: ob below 2^29, a line of at most 2^28 + 1 bytes.
def size_raw(+obl: U32, +k: U32, +n: Nat,
  +hbig: {U32.is_le(536870912, obl) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hn: {n == U32.to_nat(k) : Nat}) -> {Nat.is_le(Nat.add(U32.to_nat(obl), n), Nat.pow(2n, 30n)) == True{} : Bool}:
  +hb1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(536870912), U32.to_nat(obl)), U32.is_le(536870912, obl), False{},
    Equal.sym(Bool, U32.is_le(536870912, obl), Nat.is_le(U32.to_nat(536870912), U32.to_nat(obl)), U.is_le_to_nat(536870912, obl)), hbig)
  +hob = AB.subst(Nat, z => {Nat.is_lt(U32.to_nat(obl), z) == True{} : Bool}, U32.to_nat(536870912), Nat.pow(2n, 29n), PL.lit_pow(29n, 536870912, {==}, {==}),
    N.not_le_lt(U32.to_nat(536870912), U32.to_nat(obl), hb1))
  +hk1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(k), U32.to_nat((U32.shln(1, 28n) + 1 : U32))), U32.is_le(k, (U32.shln(1, 28n) + 1 : U32)), True{},
    Equal.sym(Bool, U32.is_le(k, (U32.shln(1, 28n) + 1 : U32)), Nat.is_le(U32.to_nat(k), U32.to_nat((U32.shln(1, 28n) + 1 : U32))), U.is_le_to_nat(k, (U32.shln(1, 28n) + 1 : U32))), hk)
  +e28 = I.size_n(28n, {==})
  +einc = C.inc_fits(U32.shln(1, 28n), 29n, {==}, AB.subst(Nat, z => {Nat.is_lt(z, Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}, Nat.pow(2n, 28n), U32.to_nat(U32.shln(1, 28n)),
    Equal.sym(Nat, U32.to_nat(U32.shln(1, 28n)), Nat.pow(2n, 28n), e28), p_lt4(28n, 29n, {==})))
  +hk2 = AB.subst(Nat, z => {Nat.is_le(U32.to_nat(k), z) == True{} : Bool}, U32.to_nat((U32.shln(1, 28n) + 1 : U32)), Nat.add(Nat.pow(2n, 28n), 1n),
    Equal.trans(Nat, U32.to_nat((U32.shln(1, 28n) + 1 : U32)), Nat.add(U32.to_nat(U32.shln(1, 28n)), 1n), Nat.add(Nat.pow(2n, 28n), 1n), einc,
      Equal.cong(Nat, Nat, z => Nat.add(z, 1n), U32.to_nat(U32.shln(1, 28n)), Nat.pow(2n, 28n), e28)), hk1)
  +hk3 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.pow(2n, 28n), 1n)) == True{} : Bool}, U32.to_nat(k), n, Equal.sym(Nat, n, U32.to_nat(k), hn), hk2)
  szk(U32.to_nat(obl), n, 28n, 29n, 30n, {==}, {==}, hob, hk3)

# A text read from bytes s .. s+sn-1 has sn characters.
def raw_len(+sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sn)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, sn) == tx : String}) -> {String.length(tx) == U32.to_nat(sn) : Nat}:
  +V = D.view(C.BT(sl, st))
  +hsl = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sn)), y) == True{} : Bool}, U32.to_nat(sl), List.length(&2, U32, V),
    Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(sl), O.view_size_t(sl, st, sd, hok)), hs)
  Equal.trans(Nat, String.length(tx), String.length(P.btext(sl, st, s, sn)), U32.to_nat(sn),
    Equal.cong(String, Nat, z => String.length(z), tx, P.btext(sl, st, s, sn), Equal.sym(String, P.btext(sl, st, s, sn), tx, ht)),
    Equal.trans(Nat, String.length(P.btext(sl, st, s, sn)), List.length(&2, U32, D.slice(V, U32.to_nat(s), U32.to_nat(sn))), U32.to_nat(sn),
      AD.chars_len(D.slice(V, U32.to_nat(s), U32.to_nat(sn))), BF.slice_len(V, U32.to_nat(s), U32.to_nat(sn), hsl)))

law all_bytes_drop:
  for +xs: List<&2, U32>
  for +n: Nat
  for +h: {D.all_bytes(xs) == True{} : Bool}
  {D.all_bytes(List.drop(&2, U32, xs, n)) == True{} : Bool}

def all_bytes_drop(xs, n, h):
  match xs n:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      h
    case Con{+x, +t} 1n+m:
      all_bytes_drop(t, m, LM.andr(U32.is_lt(x, 256), D.all_bytes(t), h))

law bytes_r:
  for +a: String
  for +b: String
  for +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}
  {E.is_bytes(b) == True{} : Bool}

def bytes_r(a, b, h):
  match a:
    case SNil{}:
      h
    case SCon{Chr{+x}, +t}:
      bytes_r(t, b, LM.andr(U32.is_lt(x, 256), E.is_bytes(String.append(t, b)), h))

def btext_bytes(+sl: U32, +st: AT.Tree<U32>, +s: U32, +sn: U32) -> {E.is_bytes(P.btext(sl, st, s, sn)) == True{} : Bool}:
  PI.chars_bytes(D.slice(D.view(C.BT(sl, st)), U32.to_nat(s), U32.to_nat(sn)),
    Q.all_bytes_take(List.drop(&2, U32, D.view(C.BT(sl, st)), U32.to_nat(s)), U32.to_nat(sn), all_bytes_drop(D.view(C.BT(sl, st)), U32.to_nat(s), O.view_bytes_t(sl, st))))

def SdG(+p: P.RunP, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +s: U32, +k: U32) -> Type:
  &p2: P.RunP -> ({NR.same_done(P.mkRun(p), o, at, inpos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, inpos, B.Line.body(l), False{}}, P.specRun(p), o, l, at, inpos)) : R.RunSt}))

def sd.k(+n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +o: B.Opts, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  kd: KD.KdG(NR.Raw{}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, inpos, inpos, line, Some{poA}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o), chA, Nil{}, False{}, False{}, False{})) -> SdG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, o, B.Line{bd, tm}, B.At{line, chA, poA}, inpos, sl, st, s, k):
  (+p2, q1) = kd
  (eq2, q2) = q1
  (inv2, sp2) = q2
  +sp = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.keyed(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), R.Opts.w(o), NR.spec.item(NR.Ck{inpos, inpos, line, Some{poA}, k}, chA, String.append(bd, tm)), Nil{}, R.bump(kk, Bool.not(z), False{}, False{}))) : R.RunSt}, True{}, String.eq(bd, bd), Equal.sym(Bool, String.eq(bd, bd), True{}, RBS.str_eq_refl(bd)), sp2)
  (p2, (eq2, (inv2, sp)))

def sd_t(+p: P.RunP, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hin: {P.RunP.i(p) == True{} : Bool},
  +hx: {P.RunP.x(p) == False{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  +hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hcb: {E.is_bytes(NR.At.chrom(at)) == True{} : Bool},
  +hcl: {Norm.len_le(NR.At.chrom(at), 268435456) == True{} : Bool}) -> SdG(p, o, l, at, inpos, sl, st, s, k):
  match p l at:
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, +x} _ _:
      Empty.absurd(SdG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, x}, o, l, at, inpos, sl, st, s, k), AB.false_ne_true(hin))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, True{}} _ _:
      Empty.absurd(SdG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, True{}}, o, l, at, inpos, sl, st, s, k), AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, False{}} B.Line{+bd, +tm} B.At{+line, +chA, +poA}:
      +hxl = raw_len(sl, st, sd, s, k, String.append(bd, tm), hok, hs, ht)
      +hsz = size_raw(obl, k, String.length(String.append(bd, tm)), hbig, hk, hxl)
      sd.k(n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, o, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k,
        KD.kd_t(NR.Raw{}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, inpos, inpos, line, Some{poA}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o), chA, Nil{}, False{}, False{}, False{}, hi, hxl, hsz, hcb, SZ.le28_30(String.length(chA), SZ.len28(chA, hcl)), (hok, (hs, ht))))

def FdG(+p: P.RunP, +o: B.Opts, +l: B.Line, +pos: Nat, +chrom: String, +sl: U32, +st: AT.Tree<U32>, +s: U32, +k: U32) -> Type:
  &p2: P.RunP -> ({NR.fast_done(P.mkRun(p), R.Opts.w(o), P.RunP.n(p), pos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, pos, B.Line.body(l), False{}}, P.specRun(p), o, l, B.At{P.RunP.n(p), chrom, Nat.show(pos)}, pos)) : R.RunSt}))

def fd.k(+n: Nat, +h: String, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +o: B.Opts, +bd: String, +tm: String, +pos: Nat, +chrom: String, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  sr: SR.SrG(NR.Raw{}, n, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, False{}, False{}, False{}), obl, obt, ow, ns, pos, pos, n, None{}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o))) -> FdG(P.RunP{n, True{}, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, o, B.Line{bd, tm}, pos, chrom, sl, st, s, k):
  (+p2, q1) = sr
  (eq2, q2) = q1
  (inv2, sp2) = q2
  +sp3 = Equal.trans(R.RunSt, P.settle(P.specRun(p2)), P.settle(R.same_run(P.specRun(P.RunP{n, True{}, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, False{}, False{}, False{}), obl, obt, ow, ns, False{}}), R.Opts.w(o), NR.spec.item(NR.Ck{pos, pos, n, None{}, k}, chrom, String.append(bd, tm)))), P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, False{}, False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), NR.spec.item(NR.Ck{pos, pos, n, None{}, k}, chrom, String.append(bd, tm)))), sp2,
    Equal.cong(List<&2, B.Note>, R.RunSt, z => P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, False{}, False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), z, False{}}, R.Opts.w(o), NR.spec.item(NR.Ck{pos, pos, n, None{}, k}, chrom, String.append(bd, tm)))), List.reverse(&2, B.Note, ns), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), List.reverse(&2, B.Note, ns), KD.app_nil_n(List.reverse(&2, B.Note, ns)))))
  +sp4 = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, Bool.not(z), False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), NR.spec.item(NR.Ck{pos, pos, n, None{}, k}, chrom, String.append(bd, tm)))) : R.RunSt}, True{}, String.eq(bd, bd), Equal.sym(Bool, String.eq(bd, bd), True{}, RBS.str_eq_refl(bd)), sp3)
  +sp5 = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.keyed.go(z, R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, Bool.not(String.eq(bd, bd)), False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), chrom, NR.spec.item(NR.Ck{pos, pos, n, None{}, k}, chrom, String.append(bd, tm)))) : R.RunSt}, True{}, String.eq(chrom, chrom), Equal.sym(Bool, String.eq(chrom, chrom), True{}, RBS.str_eq_refl(chrom)), sp4)
  (p2, (eq2, (inv2, sp5)))

def fd_t(+p: P.RunP, +o: B.Opts, +l: B.Line, +pos: Nat, +chrom: String, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hin: {P.RunP.i(p) == True{} : Bool},
  +hx: {P.RunP.x(p) == False{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  +hc: {P.RunP.c(p) == Some{chrom} : Maybe<&2, String>},
  +hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool}) -> FdG(p, o, l, pos, chrom, sl, st, s, k):
  match p l:
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, +x} _:
      Empty.absurd(FdG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, x}, o, l, pos, chrom, sl, st, s, k), AB.false_ne_true(hin))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, True{}} _:
      Empty.absurd(FdG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, True{}}, o, l, pos, chrom, sl, st, s, k), AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, False{}} B.Line{+bd, +tm}:
      +hxl = raw_len(sl, st, sd, s, k, String.append(bd, tm), hok, hs, ht)
      +hsz = size_raw(obl, k, String.length(String.append(bd, tm)), hbig, hk, hxl)
      +hi2 = AB.subst(Maybe<&2, String>, z => {RD.inv.k(True{}, h, z, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}, c, Some{chrom}, hc, hi)
      AB.subst(Maybe<&2, String>, z => FdG(P.RunP{n, True{}, h, z, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, o, B.Line{bd, tm}, pos, chrom, sl, st, s, k), Some{chrom}, c, Equal.sym(Maybe<&2, String>, c, Some{chrom}, hc),
        fd.k(n, h, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, o, bd, tm, pos, chrom, sl, st, sd, s, k,
          SR.sr_t(NR.Raw{}, n, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, False{}, False{}, False{}), obl, obt, ow, ns, pos, pos, n, None{}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o), hi2, hxl, hsz, (hok, (hs, ht)))))

def BlG(+p: P.RunP, +r: B.Res, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +s: U32, +k: U32) -> Type:
  &p2: P.RunP -> ({NR.body_line(r, P.mkRun(p), o, l, at, inpos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(r, P.specRun(p), o, l, at, inpos)) : R.RunSt}))

# The run stops with the note nt.
def bl.stop(+n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +nt: B.Note,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) -> &p2: P.RunP -> ({NR.stop(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), nt) == P.mkRun(p2) : NR.Run}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.stop(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), "", nt)) : R.RunSt})):
  +p2 = {P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, nt <> ns, True{}} : P.RunP}
  +RNS = List.reverse(&2, B.Note, ns)
  +RHS = P.settle(R.stop(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), "", nt))
  +s1 = AB.subst(String, z => {R.RunSt{n, True{}, h, c, e, None{}, Nil{}, kk, z, List.append(&2, B.Note, RNS, [nt]), True{}} == RHS : R.RunSt}, String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), ""), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(FL.TXT(obl, obt), U32.to_nat(ow))), {==})
  +s2 = AB.subst(List<&2, B.Note>, z => {R.RunSt{n, True{}, h, c, e, None{}, Nil{}, kk, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), z, True{}} == RHS : R.RunSt}, List.append(&2, B.Note, RNS, [nt]), List.reverse(&2, B.Note, nt <> ns), Equal.sym(List<&2, B.Note>, List.reverse(&2, B.Note, nt <> ns), List.append(&2, B.Note, RNS, [nt]), FL.rev_cons(nt, ns)), s1)
  (p2, ({==}, (FN.pr(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, nt <> ns, hi), s2)))

def bl.stop.k(+r: B.Res, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32, +nt: B.Note,
  sq: &p2: P.RunP -> ({NR.stop(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), nt) == P.mkRun(p2) : NR.Run}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.stop(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), "", nt)) : R.RunSt}))) ->
  &p2: P.RunP -> ({(NR.stop(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), nt), C.BT(sl, st)) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.stop(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), "", nt)) : R.RunSt})):
  (+p2, q1) = sq
  (eq, q2) = q1
  (inv, sp) = q2
  (p2, (Equal.cong(NR.Run, NR.Run & D.Bytes, z => (z, C.BT(sl, st)), NR.stop(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), nt), P.mkRun(p2), eq), (inv, sp)))

# A raw line through keyed (problem under -c w, out of scope).
def bl.kr(+o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == String.append(bd, tm) : String},
  +hbig: {U32.is_le(536870912, obl) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hcb: {E.is_bytes(chA) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chA), Nat.pow(2n, 30n)) == True{} : Bool},
  ) -> KD.KdG(NR.Raw{}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, inpos, inpos, line, Some{poA}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o), chA, nts, ch, sk, wa):
  +hxl = raw_len(sl, st, sd, s, k, String.append(bd, tm), hok, hs, ht)
  +hsz = size_raw(obl, k, String.length(String.append(bd, tm)), hbig, hk, hxl)
  KD.kd_t(NR.Raw{}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, inpos, inpos, line, Some{poA}, k, sl, st, sd, s, k, String.append(bd, tm), R.Opts.w(o), chA, nts, ch, sk, wa, hi, hxl, hsz, hcb, hcl, (hok, (hs, ht)))

def NmG(z: Bool, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32, +k2: Nat, +t: String, +stl: Bool) -> Type:
  &p2: P.RunP -> ({NR.keyed(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), R.Opts.w(o), chA, NR.item(k2, inpos, B.At{line, chA, poA}, NR.txt_len(NR.own.if(z, t, tm), k)), inpos, NR.own.if(z, t, tm), C.BT(sl, st), s, k, R.stale_note(stl, B.At{line, chA, poA}), Bool.not(z), False{}, False{}) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.keyed(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), R.Opts.w(o), R.Item{k2, inpos, B.At{line, chA, poA}, String.append(t, tm)}, R.stale_note(stl, B.At{line, chA, poA}), R.bump(kk, Bool.not(z), False{}, False{}))) : R.RunSt}))

def nm.c(+same: Bool, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32, +k2: Nat, +t: String, +stl: Bool,
  +hsame: {String.eq(t, bd) == same : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == String.append(bd, tm) : String},
  +hbig: {U32.is_le(536870912, obl) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hcb: {E.is_bytes(chA) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chA), Nat.pow(2n, 30n)) == True{} : Bool},
  +hfit: {Bool.pick(Bool, same, True{}, Norm.len_le(String.append(t, tm), (1073741824 - obl : U32))) == True{} : Bool},
  +hb: {E.is_bytes(t) == True{} : Bool}) -> NmG(same, o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, k2, t, stl):
  match same:
    case True{}:
      +et = RBS.str_eq_sound(t, bd, hsame)
      +eT = Equal.cong(String, String, z => String.append(z, tm), t, bd, et)
      +ht2 = Equal.trans(String, P.btext(sl, st, s, k), String.append(bd, tm), String.append(t, tm), ht, Equal.sym(String, String.append(t, tm), String.append(bd, tm), eT))
      +hxl = raw_len(sl, st, sd, s, k, String.append(t, tm), hok, hs, ht2)
      +hsz = size_raw(obl, k, String.length(String.append(t, tm)), hbig, hk, hxl)
      KD.kd_t(NR.Raw{}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, k2, inpos, line, Some{poA}, k, sl, st, sd, s, k, String.append(t, tm), R.Opts.w(o), chA, R.stale_note(stl, B.At{line, chA, poA}), Bool.not(True{}), False{}, False{}, hi, hxl, hsz, hcb, hcl, (hok, (hs, ht2)))
    case False{}:
      +T2 = String.append(t, tm)
      +hob = AD.w30(obl, PI.pr2(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
      +hle = PL.len_le_le(T2, (1073741824 - obl : U32), hfit)
      +hoF = Equal.trans(Bool, U32.is_le(obl, 1073741824), Nat.is_le(U32.to_nat(obl), U32.to_nat(1073741824)), True{}, U.is_le_to_nat(obl, 1073741824), AB.subst(Nat, y => {Nat.is_le(U32.to_nat(obl), y) == True{} : Bool}, Nat.pow(2n, 30n), U32.to_nat(1073741824), Equal.sym(Nat, U32.to_nat(1073741824), Nat.pow(2n, 30n), PL.lit_pow(30n, 1073741824, {==}, {==})), hob))
      +esub = Equal.trans(Nat, U32.to_nat((1073741824 - obl : U32)), Nat.sub(U32.to_nat(1073741824), U32.to_nat(obl)), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), U.to_nat_sub_le(1073741824, obl, hoF),
        Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(obl)), U32.to_nat(1073741824), Nat.pow(2n, 30n), PL.lit_pow(30n, 1073741824, {==}, {==})))
      +hle2 = AB.subst(Nat, y => {Nat.is_le(String.length(T2), y) == True{} : Bool}, U32.to_nat((1073741824 - obl : U32)), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), esub, hle)
      +hsz = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(T2)), y) == True{} : Bool}, Nat.add(U32.to_nat(obl), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl))), Nat.pow(2n, 30n),
        N.le_sub_add(U32.to_nat(obl), Nat.pow(2n, 30n), hob), N.le_add_mono_l(U32.to_nat(obl), String.length(T2), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), hle2))
      +hT4 = N.le_trans(String.length(T2), Nat.add(U32.to_nat(obl), String.length(T2)), Nat.mul(4n, Nat.pow(2n, 29n)), N.le_add_l(String.length(T2), U32.to_nat(obl)),
        N.le_trans(Nat.add(U32.to_nat(obl), String.length(T2)), Nat.add(Nat.add(U32.to_nat(obl), String.length(T2)), 8n), Nat.mul(4n, Nat.pow(2n, 29n)), N.le_add_r(Nat.add(U32.to_nat(obl), String.length(T2)), 8n),
          N.lt_to_le(Nat.add(Nat.add(U32.to_nat(obl), String.length(T2)), 8n), Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(Nat.add(U32.to_nat(obl), String.length(T2)), hsz))))
      +hxl = Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(T2))), String.length(T2), X.to_nat_fits(String.length(T2), hT4))
      +hbt = PI.bytes_app(t, tm, hb, bytes_r(bd, tm, AB.subst(String, y => {E.is_bytes(y) == True{} : Bool}, P.btext(sl, st, s, k), String.append(bd, tm), ht, btext_bytes(sl, st, s, k))))
      KD.kd_t(NR.Own{T2}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, k2, inpos, line, Some{poA}, U32.from_nat(String.length(T2)), sl, st, sd, s, k, T2, R.Opts.w(o), chA, R.stale_note(stl, B.At{line, chA, poA}), Bool.not(False{}), False{}, False{}, hi, hxl, hsz, hcb, hcl, ({==}, hbt))

def bl.r(+r: B.Res, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +line: Nat, +chA: String, +poA: String, +bd: String, +tm: String, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == String.append(bd, tm) : String},
  +hbig: {U32.is_le(536870912, obl) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hcb: {E.is_bytes(chA) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chA), Nat.pow(2n, 30n)) == True{} : Bool},
  +hfit: {Norm.res_fits(r, B.Line{bd, tm}, (1073741824 - obl : U32)) == True{} : Bool},
  +hb: {E.is_bytes(P.res_text(r)) == True{} : Bool}) -> BlG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, r, o, B.Line{bd, tm}, B.At{line, chA, poA}, inpos, sl, st, s, k):
  match r o:
    case B.Res{B.Broken{}, +k2, +t, +stl} _:
      bl.stop.k(B.Res{B.Broken{}, k2, t, stl}, o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, B.Stop{B.Malformed{}, Some{B.At{line, chA, poA}}, None{}}, bl.stop(n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, B.Stop{B.Malformed{}, Some{B.At{line, chA, poA}}, None{}}, hi))
    case B.Res{B.NoContig{}, +k2, +t, +stl} _:
      bl.stop.k(B.Res{B.NoContig{}, k2, t, stl}, o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, B.Stop{B.UnknownChrom{}, Some{B.At{line, chA, poA}}, None{}}, bl.stop(n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, B.Stop{B.UnknownChrom{}, Some{B.At{line, chA, poA}}, None{}}, hi))
    case B.Res{B.Problem{+cd}, +k2, +t, +stl} B.Opts{True{}, +w, +args}:
      bl.stop.k(B.Res{B.Problem{cd}, k2, t, stl}, B.Opts{True{}, w, args}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, B.Stop{cd, Some{B.At{line, chA, poA}}, None{}}, bl.stop(n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, B.Stop{cd, Some{B.At{line, chA, poA}}, None{}}, hi))
    case B.Res{B.Problem{+cd}, +k2, +t, +stl} B.Opts{False{}, +w, +args}:
      bl.kr(B.Opts{False{}, w, args}, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, [B.Warning{cd, B.At{line, chA, poA}}], False{}, False{}, True{}, hi, hok, hs, ht, hbig, hk, hcb, hcl)
    case B.Res{B.Skipped{}, +k2, +t, +stl} _:
      bl.kr(o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, Nil{}, False{}, True{}, False{}, hi, hok, hs, ht, hbig, hk, hcb, hcl)
    case B.Res{B.Normalized{}, +k2, +t, +stl} _:
      nm.c(String.eq(t, bd), o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, k2, t, stl, {==}, hi, hok, hs, ht, hbig, hk, hcb, hcl, hfit, hb)

def bl_t(+p: P.RunP, +r: B.Res, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hin: {P.RunP.i(p) == True{} : Bool},
  +hx: {P.RunP.x(p) == False{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  +hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  +hk: {U32.is_le(k, 268435457) == True{} : Bool},
  +hfit: {Norm.res_fits(r, l, (1073741824 - P.RunP.obl(p) : U32)) == True{} : Bool},
  +hb: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +hcb: {E.is_bytes(NR.At.chrom(at)) == True{} : Bool},
  +hcl: {Norm.len_le(NR.At.chrom(at), 268435456) == True{} : Bool}) -> BlG(p, r, o, l, at, inpos, sl, st, s, k):
  match p l at:
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, +x} _ _:
      Empty.absurd(BlG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, x}, r, o, l, at, inpos, sl, st, s, k), AB.false_ne_true(hin))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, True{}} _ _:
      Empty.absurd(BlG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, True{}}, r, o, l, at, inpos, sl, st, s, k), AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, False{}} B.Line{+bd, +tm} B.At{+line, +chA, +poA}:
      bl.r(r, o, n, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, line, chA, poA, bd, tm, inpos, sl, st, sd, s, k, hi, hok, hs, ht, hbig, hk, hcb, SZ.le28_30(String.length(chA), SZ.len28(chA, hcl)), hfit, hb)
