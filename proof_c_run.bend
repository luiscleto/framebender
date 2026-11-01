import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_flush.bend as FL
import ./proof_b_run_add.bend as AD
import ./proof_b_run_sr.bend as SR
import ./proof_b_run_kd.bend as KD
import ./proof_b_run_bl.bend as BL
import ./proof_b_lit.bend as PL
import ./proof_run_base.bend as RBS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C: the run's step for a record rewritten on its bytes
# (norm_run.bend's NR.fix_done): it is run.bend's body_line for the
# Normalized result with the new text, whose bytes (with the line's
# terminator) are the first m bytes of the buffer the line was written into.
# As proof_b_run_bl.bend's fd_t, with an own text.

def FxG(+p: P.RunP, +o: B.Opts, +l: B.Line, +q: Nat, +inpos: Nat, +t: String, +chrom: String, +sl: U32, +st: AT.Tree<U32>, +m: U32) -> Type:
  &p2: P.RunP -> ({NR.fix_done(P.mkRun(p), R.Opts.w(o), P.RunP.n(p), q, inpos, C.BT(sl, st), m) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, q, t, False{}}, P.specRun(p), o, l, B.At{P.RunP.n(p), chrom, Nat.show(inpos)}, inpos)) : R.RunSt}))

def fx.k(+n: Nat, +h: String, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +la: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +kk: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +o: B.Opts, +bd: String, +tm: String, +q: Nat, +inpos: Nat, +t: String, +chrom: String, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +m: U32,
  +hne: {String.eq(t, bd) == False{} : Bool},
  sr: SR.SrG(NR.Raw{}, n, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, True{}, False{}, False{}), obl, obt, ow, ns, q, inpos, n, Some{Nat.show(inpos)}, m, sl, st, sd, 0, m, String.append(t, tm), R.Opts.w(o))) -> FxG(P.RunP{n, True{}, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, o, B.Line{bd, tm}, q, inpos, t, chrom, sl, st, m):
  (+p2, q1) = sr
  (eq2, q2) = q1
  (inv2, sp2) = q2
  +IT = NR.spec.item(NR.Ck{q, inpos, n, Some{Nat.show(inpos)}, m}, chrom, String.append(t, tm))
  +S0 = {R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, True{}, False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}} : R.RunSt}
  +sp3 = Equal.trans(R.RunSt, P.settle(P.specRun(p2)), P.settle(R.same_run(P.specRun(P.RunP{n, True{}, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, True{}, False{}, False{}), obl, obt, ow, ns, False{}}), R.Opts.w(o), IT)), P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, True{}, False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), IT)), sp2,
    Equal.cong(List<&2, B.Note>, R.RunSt, z => P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, True{}, False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), z, False{}}, R.Opts.w(o), IT)), List.reverse(&2, B.Note, ns), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), List.reverse(&2, B.Note, ns), KD.app_nil_n(List.reverse(&2, B.Note, ns)))))
  +sp4 = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, Bool.not(z), False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), IT)) : R.RunSt}, False{}, String.eq(t, bd), Equal.sym(Bool, String.eq(t, bd), False{}, hne), sp3)
  +sp5 = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.keyed.go(z, R.RunSt{n, True{}, h, Some{chrom}, e, NR.spec.last(la, FL.chromof(Some{chrom})), FL.ISS(RD.items(f, b), Some{chrom}, obl, obt, ow), R.bump(kk, Bool.not(String.eq(t, bd)), False{}, False{}), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), False{}}, R.Opts.w(o), chrom, IT)) : R.RunSt}, True{}, String.eq(chrom, chrom), Equal.sym(Bool, String.eq(chrom, chrom), True{}, RBS.str_eq_refl(chrom)), sp4)
  (p2, (eq2, (inv2, sp5)))

# The text's length bound from the fit test (as proof_b_run_bl.bend's nm.c).
def fx.sz(+obl: U32, +ow: U32, +T: String, +m: U32,
  +hob: {Nat.is_le(U32.to_nat(obl), Nat.pow(2n, 30n)) == True{} : Bool},
  +hxl: {String.length(T) == U32.to_nat(m) : Nat},
  +hfit: {U32.is_le(m, (1073741824 - obl : U32)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(T)), Nat.pow(2n, 30n)) == True{} : Bool}:
  +hle0 = Equal.trans(Bool, Nat.is_le(U32.to_nat(m), U32.to_nat((1073741824 - obl : U32))), U32.is_le(m, (1073741824 - obl : U32)), True{},
    Equal.sym(Bool, U32.is_le(m, (1073741824 - obl : U32)), Nat.is_le(U32.to_nat(m), U32.to_nat((1073741824 - obl : U32))), U.is_le_to_nat(m, (1073741824 - obl : U32))), hfit)
  +hle = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat((1073741824 - obl : U32))) == True{} : Bool}, U32.to_nat(m), String.length(T), Equal.sym(Nat, String.length(T), U32.to_nat(m), hxl), hle0)
  +hoF = Equal.trans(Bool, U32.is_le(obl, 1073741824), Nat.is_le(U32.to_nat(obl), U32.to_nat(1073741824)), True{}, U.is_le_to_nat(obl, 1073741824), AB.subst(Nat, y => {Nat.is_le(U32.to_nat(obl), y) == True{} : Bool}, Nat.pow(2n, 30n), U32.to_nat(1073741824), Equal.sym(Nat, U32.to_nat(1073741824), Nat.pow(2n, 30n), PL.lit_pow(30n, 1073741824, {==}, {==})), hob))
  +esub = Equal.trans(Nat, U32.to_nat((1073741824 - obl : U32)), Nat.sub(U32.to_nat(1073741824), U32.to_nat(obl)), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), U.to_nat_sub_le(1073741824, obl, hoF),
    Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(obl)), U32.to_nat(1073741824), Nat.pow(2n, 30n), PL.lit_pow(30n, 1073741824, {==}, {==})))
  +hle2 = AB.subst(Nat, y => {Nat.is_le(String.length(T), y) == True{} : Bool}, U32.to_nat((1073741824 - obl : U32)), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), esub, hle)
  AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(T)), y) == True{} : Bool}, Nat.add(U32.to_nat(obl), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl))), Nat.pow(2n, 30n),
    N.le_sub_add(U32.to_nat(obl), Nat.pow(2n, 30n), hob), N.le_add_mono_l(U32.to_nat(obl), String.length(T), Nat.sub(Nat.pow(2n, 30n), U32.to_nat(obl)), hle2))

# NR.fix_done on a pictured run in the body, not stopped, whose CHROM is the
# record's: the new text t (with the line's terminator) is the scratch
# buffer's first m bytes, differs from the line's body, and fits the output
# buffer (the fit test of norm.bend's fix.len).
def run_fix_done(+p: P.RunP, +o: B.Opts, +l: B.Line, +q: Nat, +inpos: Nat, +t: String, +chrom: String,
  +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +m: U32,
  +hi: {RD.RunInv(p) == True{} : Bool},
  +hin: {P.RunP.i(p) == True{} : Bool},
  +hx: {P.RunP.x(p) == False{} : Bool},
  +hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(U32.to_nat(m), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, 0, m) == String.append(t, B.Line.term(l)) : String},
  +hne: {String.eq(t, B.Line.body(l)) == False{} : Bool},
  +hc: {P.RunP.c(p) == Some{chrom} : Maybe<&2, String>},
  +hfit: {U32.is_le(m, (1073741824 - P.RunP.obl(p) : U32)) == True{} : Bool}) -> FxG(p, o, l, q, inpos, t, chrom, sl, st, m):
  match p l:
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, +x} _:
      Empty.absurd(FxG(P.RunP{n, False{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, x}, o, l, q, inpos, t, chrom, sl, st, m), AB.false_ne_true(hin))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, True{}} _:
      Empty.absurd(FxG(P.RunP{n, True{}, h, c, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, True{}}, o, l, q, inpos, t, chrom, sl, st, m), AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +kk, +obl, +obt, +ow, +ns, False{}} B.Line{+bd, +tm}:
      +T = String.append(t, tm)
      +hs0 = {%Equal.sym(Nat, Nat.add(0n, U32.to_nat(m)), U32.to_nat(m), {==}) : {Nat.is_le(_, U32.to_nat(sl)) == True{} : Bool}; hs : {Nat.is_le(Nat.add(U32.to_nat(0), U32.to_nat(m)), U32.to_nat(sl)) == True{} : Bool}}
      +hxl = BL.raw_len(sl, st, sd, 0, m, T, hok, hs0, ht)
      +hob = AD.w30(obl, PI.pr2(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
      +hsz = fx.sz(obl, ow, T, m, hob, hxl, hfit)
      +hi2 = AB.subst(Maybe<&2, String>, z => {RD.inv.k(True{}, h, z, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}, c, Some{chrom}, hc, hi)
      AB.subst(Maybe<&2, String>, z => FxG(P.RunP{n, True{}, h, z, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}, o, B.Line{bd, tm}, q, inpos, t, chrom, sl, st, m), Some{chrom}, c, Equal.sym(Maybe<&2, String>, c, Some{chrom}, hc),
        fx.k(n, h, cbl, cbt, e, la, f, b, bn, tl, kk, obl, obt, ow, ns, o, bd, tm, q, inpos, t, chrom, sl, st, sd, m, hne,
          SR.sr_t(NR.Raw{}, n, h, Some{chrom}, cbl, cbt, e, la, f, b, bn, tl, R.bump(kk, True{}, False{}, False{}), obl, obt, ow, ns, q, inpos, n, Some{Nat.show(inpos)}, m, sl, st, sd, 0, m, T, R.Opts.w(o), hi2, hxl, hsz, (hok, (hs0, ht)))))
