import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_flush.bend as FL
import ./proof_b_run_fin.bend as FN
import ./proof_b_run_add.bend as AD
import ./proof_b_run_sr.bend as SR
import ./proof_b_run_nr.bend as NW
import ./proof_run_base.bend as RBS
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT

# run.bend's keyed on a pictured run: the line's messages and counts, then
# its CHROM run (same_run) or a new one (new_run).

law app_nil_n:
  for +xs: List<&2, B.Note>
  {List.append(&2, B.Note, xs, Nil{}) == xs : List<&2, B.Note>}

def app_nil_n(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %app_nil_n(t) : {x <> List.append(&2, B.Note, t, Nil{}) == x <> _ : List<&2, B.Note>}
      {==}

law rev_onto_eq:
  for +nts: List<&2, B.Note>
  for +ns: List<&2, B.Note>
  {List.reverse(&2, B.Note, NR.rev_onto(nts, ns)) == List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts) : List<&2, B.Note>}

def rev_onto_eq(nts, ns):
  match nts:
    case Nil{}:
      Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), Nil{}), List.reverse(&2, B.Note, ns), app_nil_n(List.reverse(&2, B.Note, ns)))
    case Con{+x, +t}:
      +RN = List.reverse(&2, B.Note, ns)
      Equal.trans(List<&2, B.Note>, List.reverse(&2, B.Note, NR.rev_onto(t, x <> ns)), List.append(&2, B.Note, List.reverse(&2, B.Note, x <> ns), t), List.append(&2, B.Note, RN, x <> t),
        rev_onto_eq(t, x <> ns),
        Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, x <> ns), t), List.append(&2, B.Note, List.append(&2, B.Note, RN, [x]), t), List.append(&2, B.Note, RN, x <> t),
          Equal.cong(List<&2, B.Note>, List<&2, B.Note>, z => List.append(&2, B.Note, z, t), List.reverse(&2, B.Note, x <> ns), List.append(&2, B.Note, RN, [x]), FL.rev_cons(x, ns)),
          FL.app_assoc_n(RN, [x], t)))

# The current CHROM run's: its CHROM is chromN.
def cur_eq(+c: Maybe<&2, String>, +chromN: String, +h: {R.is_cur(c, chromN) == True{} : Bool}) -> {FL.chromof(c) == chromN : String}:
  match c:
    case None{}:
      Empty.absurd({FL.chromof(None{}) == chromN : String}, AB.false_ne_true(h))
    case Some{+s0}:
      RBS.str_eq_sound(s0, chromN, h)

def KdG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool) -> Type:
  &p2: P.RunP -> ({NR.keyed(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn, nts, ch, sk, wa) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.keyed(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx), nts, R.bump(k, ch, sk, wa))) : R.RunSt}))

def KdC(z: Bool, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool) -> Type:
  &p2: P.RunP -> ({NR.keyed.go(z, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), C.BT(obl, obt), ow, NR.rev_onto(nts, ns), False{}}, w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.keyed.go(z, R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))) : R.RunSt}))

def kd.sr(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool,
  +ec: {FL.chromof(c) == chromN : String},
  sr: SR.SrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w)) -> KdC(True{}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa):
  (+p2, q1) = sr
  (eq2, q2) = q1
  (inv2, sp2) = q2
  +es = Equal.cong(List<&2, B.Note>, R.RunSt, z => R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), z, False{}}, List.reverse(&2, B.Note, NR.rev_onto(nts, ns)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), rev_onto_eq(nts, ns))
  +ei = Equal.cong(String, R.Item, z => NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, z, tx), FL.chromof(c), chromN, ec)
  +sp = Equal.trans(R.RunSt, P.settle(P.specRun(p2)), P.settle(R.same_run(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), False{}}), w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx))), P.settle(R.same_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), sp2,
    Equal.trans(R.RunSt, P.settle(R.same_run(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), False{}}), w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx))), P.settle(R.same_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx))), P.settle(R.same_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))),
      Equal.cong(R.RunSt, R.RunSt, z => P.settle(R.same_run(z, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx))), P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), False{}}), R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, es),
      Equal.cong(R.Item, R.RunSt, z => P.settle(R.same_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, z)), NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx), ei)))
  (p2, (eq2, (inv2, sp)))

def kd.nr(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool,
  nr: NW.NrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN)) -> KdC(False{}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa):
  (+p2, q1) = nr
  (eq2, q2) = q1
  (inv2, sp2) = q2
  +es = Equal.cong(List<&2, B.Note>, R.RunSt, z => R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), z, False{}}, List.reverse(&2, B.Note, NR.rev_onto(nts, ns)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), rev_onto_eq(nts, ns))
  +sp = Equal.trans(R.RunSt, P.settle(P.specRun(p2)), P.settle(R.new_run(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), False{}}), w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), P.settle(R.new_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), sp2,
    Equal.cong(R.RunSt, R.RunSt, z => P.settle(R.new_run(z, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), False{}}), R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), R.bump(k, ch, sk, wa), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), nts), False{}}, es))
  (p2, (eq2, (inv2, sp)))

def kd.c(+cur: Bool, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcur: {R.is_cur(c, chromN) == cur : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> KdC(cur, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa):
  match cur:
    case True{}:
    +invk = FN.ns_body(h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, NR.rev_onto(nts, ns), hi)
      kd.sr(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa, cur_eq(c, chromN, hcur), SR.sr_t(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, invk, hxl, hsz, htx))
    case False{}:
    +invk = FN.ns_body(h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, NR.rev_onto(nts, ns), hi)
      kd.nr(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa, NW.nr_t(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), obl, obt, ow, NR.rev_onto(nts, ns), kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, invk, hxl, hsz, hcb, hcl, htx))

# run.bend's keyed on a pictured run that goes on, in the body.
def kd_t(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +nts: List<&2, B.Note>, +ch: Bool, +sk: Bool, +wa: Bool,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> KdG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa):
  kd.c(R.is_cur(c, chromN), t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, nts, ch, sk, wa, hi, hxl, hsz, hcb, hcl, {==}, htx)
