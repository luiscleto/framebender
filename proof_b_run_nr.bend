import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
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
import ./proof_run_base.bend as RBS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# run.bend's new_run on a pictured run: the buffer written, then a stop
# (UNSORTED, or this CHROM's run ended) or the new CHROM's run started.

law push_eq:
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  {NR.push_cur(c, e) == R.push_cur(c, e) : List<&2, String>}

def push_eq(c, e):
  match c:
    case None{}:
      {==}
    case Some{+s}:
      {==}

law spec_nil:
  for +xs: List<&2, NR.Ck>
  for +chrom: String
  for +t: String
  for +h: {NR.spec.items(xs, chrom, t) == Nil{} : List<&2, R.Item>}
  {RD.lens(xs) == 0n : Nat}

def spec_nil(xs, chrom, t, h):
  match xs:
    case Nil{}:
      {==}
    case Con{NR.Ck{+k, +ip, +ln, +ps, +n}, +rest}:
      Empty.absurd({RD.lens(Con{NR.Ck{k, ip, ln, ps, n}, rest}) == 0n : Nat},
        AB.false_ne_true(Equal.cong(List<&2, R.Item>, Bool, z => List.is_empty(&2, R.Item, z), NR.spec.items(Con{NR.Ck{k, ip, ln, ps, n}, rest}, chrom, t), Nil{}, h)))

def NrG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String) -> Type:
  &p2: P.RunP -> ({NR.new_run(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.new_run(R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))) : R.RunSt}))

def NrC(fl: R.Flush, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool) -> Type:
  &p2: P.RunP -> ({NR.new_run.k(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, x1}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.new_run.go(fl, R.has(chromN, e), R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))) : R.RunSt}))


def nr.new.k(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool, +o2: String, +la: Maybe<&2, R.Item>,
  +hx1: {x1 == False{} : Bool},
  +hout: {String.take(FL.TXT(obl, obt), U32.to_nat(ow1)) == String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2) : String},
  +hns: {ns1 == ns : List<&2, B.Note>},
  +hag: {R.has(chromN, e) == False{} : Bool},
  +eqo: {NR.of_str(chromN) == C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)) : D.Bytes},
  sr: SR.SrG(t, nl, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w)) -> NrC(R.Flushed{o2, la}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1):
  (+p4, q1) = sr
  (eq4, q2) = q1
  (inv4, sp4) = q2
  +e1 = AB.subst(D.Bytes, z => {NR.same_run(NR.Run{nl, True{}, h, Some{chromN}, z, NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, C.BT(obl, obt), ow1, ns1, False{}}, w, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p4), C.BT(sl, st)) : NR.Run & D.Bytes},
    C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)), NR.of_str(chromN), Equal.sym(D.Bytes, NR.of_str(chromN), C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)), eqo), eq4)
  +e2 = AB.subst(Bool, z => {NR.new_run.go(False{}, z, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l1, f1, b1, bn1, tl, k, C.BT(obl, obt), ow1, ns1, False{}}, w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p4), C.BT(sl, st)) : NR.Run & D.Bytes},
    False{}, R.has(chromN, e), Equal.sym(Bool, R.has(chromN, e), False{}, hag), e1)
  +eq = AB.subst(Bool, z => {NR.new_run.k(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, z}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p4), C.BT(sl, st)) : NR.Run & D.Bytes}, False{}, x1, Equal.sym(Bool, x1, False{}, hx1), e2)
  +ST3 = {R.RunSt{nl, True{}, h, Some{chromN}, R.push_cur(c, e), None{}, Nil{}, k, String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2), List.reverse(&2, B.Note, ns), False{}} : R.RunSt}
  +es1 = AB.subst(List<&2, String>, z => {P.specRun(P.RunP{nl, True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, False{}}) == R.RunSt{nl, True{}, h, Some{chromN}, z, None{}, Nil{}, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow1)), List.reverse(&2, B.Note, ns1), False{}} : R.RunSt}, NR.push_cur(c, e), R.push_cur(c, e), push_eq(c, e), {==})
  +es2 = AB.subst(String, z => {P.specRun(P.RunP{nl, True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, False{}}) == R.RunSt{nl, True{}, h, Some{chromN}, R.push_cur(c, e), None{}, Nil{}, k, z, List.reverse(&2, B.Note, ns1), False{}} : R.RunSt}, String.take(FL.TXT(obl, obt), U32.to_nat(ow1)), String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2), hout, es1)
  +es3 = AB.subst(List<&2, B.Note>, z => {P.specRun(P.RunP{nl, True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, False{}}) == R.RunSt{nl, True{}, h, Some{chromN}, R.push_cur(c, e), None{}, Nil{}, k, String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2), List.reverse(&2, B.Note, z), False{}} : R.RunSt}, ns1, ns, hns, es2)
  +sp = Equal.trans(R.RunSt, P.settle(P.specRun(p4)), P.settle(R.same_run(P.specRun(P.RunP{nl, True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, False{}}), w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), P.settle(R.same_run(ST3, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), sp4,
    Equal.cong(R.RunSt, R.RunSt, z => P.settle(R.same_run(z, w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))), P.specRun(P.RunP{nl, True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, False{}}), ST3, es3))
  +sp2 = AB.subst(Bool, z => {P.settle(P.specRun(p4)) == P.settle(R.new_run.go(R.Flushed{o2, la}, z, R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))) : R.RunSt}, False{}, R.has(chromN, e), Equal.sym(Bool, R.has(chromN, e), False{}, hag), sp)
  (p4, (eq, (inv4, sp2)))

# Everything written, this CHROM's run did not end: its run starts.
def nr.new(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool, +o2: String, +la: Maybe<&2, R.Item>,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  +hx1: {x1 == False{} : Bool},
  +hout: {String.take(FL.TXT(obl, obt), U32.to_nat(ow1)) == String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2) : String},
  +hns: {ns1 == ns : List<&2, B.Note>},
  +hdr: {NR.spec.items(RD.items(f1, b1), FL.chromof(c), String.drop(FL.TXT(obl, obt), U32.to_nat(ow1))) == Nil{} : List<&2, R.Item>},
  +hag: {R.has(chromN, e) == False{} : Bool},
  +invf: {RD.inv.k(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, x1) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> NrC(R.Flushed{o2, la}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1):
  +invF = AB.subst(Bool, z => {RD.inv.k(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, z) == True{} : Bool}, x1, False{}, hx1, invf)
  +hL = NM.lt_c0(String.length(chromN), Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(String.length(chromN), hcl))
  +hok0 = AB.subst(D.Bytes, z => {D.ok(z, 0n) == True{} : Bool}, BY.empty(0n), C.BT(0, G.tnew(0n, 0)), G.empty_eq(0n), G.empty_ok(0n, {==}))
  +eqo = AB.subst(D.Bytes, z => {NR.put_str(z, chromN) == C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)) : D.Bytes}, C.BT(0, G.tnew(0n, 0)), BY.empty(0n), Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, G.tnew(0n, 0)), G.empty_eq(0n)), BF.put_str_eq(0, G.tnew(0n, 0), chromN, G.tnew_full(0n, 0)))
  +oko = BF.put_str_ok(0, G.tnew(0n, 0), 0n, chromN, hok0, hL)
  +txo = BF.put_str_text(0, G.tnew(0n, 0), 0n, chromN, hok0, hcb, hL)
  +h4 = AB.subst(String, z => {String.eq(z, chromN) == True{} : Bool}, chromN, NR.chars(D.view(C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)))), Equal.sym(String, NR.chars(D.view(C.BT(BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN)))), chromN, txo), RBS.str_eq_refl(chromN))
  +el0 = spec_nil(RD.items(f1, b1), FL.chromof(c), String.drop(FL.TXT(obl, obt), U32.to_nat(ow1)), hdr)
  +h5 = AB.subst(Nat, z => {Nat.is_eq(Nat.add(U32.to_nat(ow1), z), U32.to_nat(obl)) == True{} : Bool}, RD.lens(RD.items(f1, b1)), 0n, el0, PI.pr5(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, False{}, invF))
  +inv3 = PI.inv_mk(True{}, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), Nil{}, Nil{}, 0n, 0n, obl, obt, ow1, ns1, False{},
    (PI.pr1(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, False{}, invF), (PI.pr2(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, False{}, invF), (oko, (h4, (h5, ({==}, ({==}, ({==}, (PI.pr9(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, False{}, invF), ({==}, PI.pr11(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, False{}, invF))))))))))))
  nr.new.k(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, o2, la, hx1, hout, hns, hag, eqo,
    SR.sr_t(t, nl, h, Some{chromN}, BF.pstl(chromN, 0), BF.PSR(0, G.tnew(0n, 0), chromN), NR.push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, obl, obt, ow1, ns1, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, inv3, hxl, hsz, htx))

# This CHROM's run ended: UNSORTED.
def nr.again(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool, +o2: String, +la: Maybe<&2, R.Item>,
  +hx1: {x1 == False{} : Bool},
  +hout: {String.take(FL.TXT(obl, obt), U32.to_nat(ow1)) == String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2) : String},
  +hns: {ns1 == ns : List<&2, B.Note>},
  +hag: {R.has(chromN, e) == True{} : Bool},
  +invf: {RD.inv.k(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, x1) == True{} : Bool}) -> NrC(R.Flushed{o2, la}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1):
  +STA = {B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{kx, ipx, lnx, psx, nx}, chromN)}, None{}} : B.Note}
  +p2 = {P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, STA <> ns1, True{}} : P.RunP}
  +e2 = AB.subst(Bool, z => {NR.new_run.go(False{}, z, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l1, f1, b1, bn1, tl, k, C.BT(obl, obt), ow1, ns1, False{}}, w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}, True{}, R.has(chromN, e), Equal.sym(Bool, R.has(chromN, e), True{}, hag), {==})
  +eq = AB.subst(Bool, z => {NR.new_run.k(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, z}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}, False{}, x1, Equal.sym(Bool, x1, False{}, hx1), e2)
  +RHS = P.settle(R.new_run.go(R.Flushed{o2, la}, True{}, R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx)))
  +s1 = AB.subst(String, z => {R.RunSt{nl, True{}, h, c, e, None{}, Nil{}, k, z, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STA]), True{}} == RHS : R.RunSt}, String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2), String.take(FL.TXT(obl, obt), U32.to_nat(ow1)), Equal.sym(String, String.take(FL.TXT(obl, obt), U32.to_nat(ow1)), String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2), hout), {==})
  +s2 = AB.subst(List<&2, B.Note>, z => {R.RunSt{nl, True{}, h, c, e, None{}, Nil{}, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow1)), z, True{}} == RHS : R.RunSt}, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STA]), List.reverse(&2, B.Note, STA <> ns1),
    Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STA]), List.reverse(&2, B.Note, STA <> ns), List.reverse(&2, B.Note, STA <> ns1), Equal.sym(List<&2, B.Note>, List.reverse(&2, B.Note, STA <> ns), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STA]), FL.rev_cons(STA, ns)), Equal.cong(List<&2, B.Note>, List<&2, B.Note>, z => List.reverse(&2, B.Note, STA <> z), ns, ns1, Equal.sym(List<&2, B.Note>, ns1, ns, hns))), s1)
  +s3 = AB.subst(Bool, z => {P.settle(P.specRun(p2)) == P.settle(R.new_run.go(R.Flushed{o2, la}, z, R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, w, chromN, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, chromN, tx))) : R.RunSt}, True{}, R.has(chromN, e), Equal.sym(Bool, R.has(chromN, e), True{}, hag), s2)
  (p2, (eq, (FN.pr(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, x1, STA <> ns1, invf), s3)))

def nr.ag(+ag: Bool, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool, +o2: String, +la: Maybe<&2, R.Item>,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  +hx1: {x1 == False{} : Bool},
  +hout: {String.take(FL.TXT(obl, obt), U32.to_nat(ow1)) == String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2) : String},
  +hns: {ns1 == ns : List<&2, B.Note>},
  +hdr: {NR.spec.items(RD.items(f1, b1), FL.chromof(c), String.drop(FL.TXT(obl, obt), U32.to_nat(ow1))) == Nil{} : List<&2, R.Item>},
  +hag: {R.has(chromN, e) == ag : Bool},
  +invf: {RD.inv.k(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, x1) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> NrC(R.Flushed{o2, la}, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1):
  match ag:
    case True{}:
      nr.again(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, o2, la, hx1, hout, hns, hag, invf)
    case False{}:
      nr.new(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, o2, la, hi, hxl, hsz, hcb, hcl, hx1, hout, hns, hdr, hag, invf, htx)

def nr.c(fl: R.Flush, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  +invf: {RD.inv.k(True{}, h, c, cbl, cbt, f1, b1, bn1, tl, obl, obt, ow1, ns1, x1) == True{} : Bool},
  flr: FL.FLR(FL.fs(fl), FL.chromof(c), FL.TXT(obl, obt), ow, ns, Nil{}, l1, f1, b1, ow1, ns1, x1),
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> NrC(fl, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1):
  match fl:
    case R.Broke{+o2, +bad, +prev}:
      (+hx1, q1) = flr
      (hout, hns) = q1
      +eq = AB.subst(Bool, z => {NR.new_run.k(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, z}), w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, z}), C.BT(sl, st)) : NR.Run & D.Bytes}, True{}, x1, Equal.sym(Bool, x1, True{}, hx1), {==})
      +sp = SR.fsettle(R.Broke{o2, bad, prev}, nl, h, c, cbl, cbt, e, tl, k, obl, obt, ow, ns, l1, f1, b1, bn1, ow1, ns1, x1, NR.spec.last(l, FL.chromof(c)), FL.ISS(RD.items(f, b), c, obl, obt, ow), Nil{}, B.At{0n, "", ""}, (hx1, (hout, hns)))
      (P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, x1}, (eq, (invf, sp)))
    case R.Flushed{+o2, +la}:
      (+hx1, q1) = flr
      (hout, q2) = q1
      (hns, q3) = q2
      (hl, hdr) = q3
      nr.ag(R.has(chromN, e), t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, o2, la, hi, hxl, hsz, hcb, hcl, hx1, hout, hns, hdr, {==}, invf, htx)

def nr.k2(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String, +l1: Maybe<&2, NR.Ck>, +f1: List<&2, NR.Ck>, +b1: List<&2, NR.Ck>, +bn1: Nat, +ow1: U32, +ns1: List<&2, B.Note>, +x1: Bool,
  +eqf: {NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, w, 0n, True{}) == P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, x1}) : NR.Run},
  r: NrC(R.flush(FL.ISS(RD.items(f, b), c, obl, obt, ow), NR.spec.last(l, FL.chromof(c))), t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1)) -> NrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN):
  (+p2, q1) = r
  (eqc, q2) = q1
  (invc, spc) = q2
  +eq = AB.subst(NR.Run, z => {NR.new_run.k(z, w, chromN, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}, P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, x1}), NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, w, 0n, True{}),
    Equal.sym(NR.Run, NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, w, 0n, True{}), P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l1, f1, b1, bn1, tl, k, obl, obt, ow1, ns1, x1}), eqf), eqc)
  (p2, (eq, (invc, spc)))

def nr.k(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx),
  fl: FL.LoopR(Nat.add(bn, 2n), nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, w, 0n, True{}, RD.items(f, b))) -> NrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN):
  (+l1, q1) = fl
  (+f1, q2) = q1
  (+b1, q3) = q2
  (+bn1, q4) = q3
  (+ow1, q5) = q4
  (+ns1, q6) = q5
  (+x1, q7) = q6
  (eqf, q8) = q7
  (invf, flr) = q8
  nr.k2(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, eqf,
    nr.c(R.flush(FL.ISS(RD.items(f, b), c, obl, obt, ow), NR.spec.last(l, FL.chromof(c))), t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, l1, f1, b1, bn1, ow1, ns1, x1, hi, hxl, hsz, hcb, hcl, invf, flr, htx))

# run.bend's new_run on a pictured run that goes on, in the body.
def nr_t(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat, +chromN: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hcb: {E.is_bytes(chromN) == True{} : Bool},
  +hcl: {Nat.is_le(String.length(chromN), Nat.pow(2n, 30n)) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> NrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN):
  nr.k(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, chromN, hi, hxl, hsz, hcb, hcl, htx, FL.flush_t(nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, w, 0n, True{}, hi))
