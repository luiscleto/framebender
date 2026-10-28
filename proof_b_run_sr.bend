import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_flush.bend as FL
import ./proof_b_run_add.bend as AD
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N

# run.bend's same_run on a pictured run: the item added (proof_b_run_add),
# then the ready items written (proof_b_run_flush), up to P.settle.

# After a flush with outcome F: the run settles as run.bend's emit.ready.
def fsettle(fl: R.Flush, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +l3: Maybe<&2, NR.Ck>, +f3: List<&2, NR.Ck>, +b3: List<&2, NR.Ck>, +bn3: Nat, +ow3: U32, +ns3: List<&2, B.Note>, +x3: Bool, +L0: Maybe<&2, R.Item>, +B0: List<&2, R.Item>, +dr: List<&2, R.Item>, +at: B.At,
  hf: FL.FLR(FL.fs(fl), FL.chromof(c), FL.TXT(obl, obt), ow, ns, dr, l3, f3, b3, ow3, ns3, x3)) ->
  {P.settle(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl, k, obl, obt, ow3, ns3, x3})) == P.settle(R.emit.ready(fl, R.RunSt{nl, True{}, h, c, e, L0, B0, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, dr, at)) : R.RunSt}:
  match fl:
    case R.Flushed{+o2, +la}:
      (+hx3, q1) = hf
      (hout, q2) = q1
      (hns, q3) = q2
      (hl, hdr) = q3
      +SL = NR.spec.items(RD.items(f3, b3), FL.chromof(c), String.drop(FL.TXT(obl, obt), U32.to_nat(ow3)))
      +OUT = String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2)
      +RHS = P.settle(R.emit.ready(R.Flushed{o2, la}, R.RunSt{nl, True{}, h, c, e, L0, B0, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, dr, at))
      +eL = Equal.trans(Maybe<&2, R.Item>, P.blank(NR.spec.last(l3, FL.chromof(c))), NR.spec.last(l3, FL.chromof(c)), P.blank(la), FL.blank_last(l3, FL.chromof(c)), hl)
      +s1 = AB.subst(Maybe<&2, R.Item>, z => {R.RunSt{nl, True{}, h, c, e, z, dr, k, OUT, List.reverse(&2, B.Note, ns), False{}} == RHS : R.RunSt}, P.blank(la), P.blank(NR.spec.last(l3, FL.chromof(c))), Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l3, FL.chromof(c))), P.blank(la), eL), {==})
      +s2 = AB.subst(List<&2, R.Item>, z => {R.RunSt{nl, True{}, h, c, e, P.blank(NR.spec.last(l3, FL.chromof(c))), z, k, OUT, List.reverse(&2, B.Note, ns), False{}} == RHS : R.RunSt}, dr, SL, Equal.sym(List<&2, R.Item>, SL, dr, hdr), s1)
      +s3 = AB.subst(String, z => {R.RunSt{nl, True{}, h, c, e, P.blank(NR.spec.last(l3, FL.chromof(c))), SL, k, z, List.reverse(&2, B.Note, ns), False{}} == RHS : R.RunSt}, OUT, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), Equal.sym(String, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), OUT, hout), s2)
      +s4 = AB.subst(List<&2, B.Note>, z => {R.RunSt{nl, True{}, h, c, e, P.blank(NR.spec.last(l3, FL.chromof(c))), SL, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), List.reverse(&2, B.Note, z), False{}} == RHS : R.RunSt}, ns, ns3, Equal.sym(List<&2, B.Note>, ns3, ns, hns), s3)
      AB.subst(Bool, z => {P.settle(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl, k, obl, obt, ow3, ns3, z})) == RHS : R.RunSt}, False{}, x3, Equal.sym(Bool, x3, False{}, hx3), s4)
    case R.Broke{+o2, +bad, +prev}:
      (+hx3, q1) = hf
      (hout, hns) = q1
      +STP = {B.Stop{B.Unsorted{}, Some{bad}, prev} : B.Note}
      +OUT = String.append(String.take(FL.TXT(obl, obt), U32.to_nat(ow)), o2)
      +RHS = P.settle(R.emit.ready(R.Broke{o2, bad, prev}, R.RunSt{nl, True{}, h, c, e, L0, B0, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, dr, at))
      +s1 = AB.subst(String, z => {R.RunSt{nl, True{}, h, c, e, None{}, Nil{}, k, z, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STP]), True{}} == RHS : R.RunSt}, OUT, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), Equal.sym(String, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), OUT, hout), {==})
      +s2 = AB.subst(List<&2, B.Note>, z => {R.RunSt{nl, True{}, h, c, e, None{}, Nil{}, k, String.take(FL.TXT(obl, obt), U32.to_nat(ow3)), z, True{}} == RHS : R.RunSt}, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STP]), List.reverse(&2, B.Note, ns3),
        Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STP]), List.reverse(&2, B.Note, STP <> ns), List.reverse(&2, B.Note, ns3), Equal.sym(List<&2, B.Note>, List.reverse(&2, B.Note, STP <> ns), List.append(&2, B.Note, List.reverse(&2, B.Note, ns), [STP]), FL.rev_cons(STP, ns)), Equal.cong(List<&2, B.Note>, List<&2, B.Note>, z => List.reverse(&2, B.Note, z), STP <> ns, ns3, Equal.sym(List<&2, B.Note>, ns3, STP <> ns, hns))), s1)
      AB.subst(Bool, z => {P.settle(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl, k, obl, obt, ow3, ns3, z})) == RHS : R.RunSt}, True{}, x3, Equal.sym(Bool, x3, True{}, hx3), s2)

def SrG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat) -> Type:
  &p2: P.RunP -> ({NR.same_run(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), w, NR.Ck{kx, ipx, lnx, psx, nx}, ipx, t, C.BT(sl, st), s, sn) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.same_run(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), w, NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx))) : R.RunSt}))

def sr.k2(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat,
  +obl2: U32, +obt2: AT.Tree<U32>, +f2: List<&2, NR.Ck>, +b2: List<&2, NR.Ck>, +bn2: Nat, +tl2: Nat,
  +eqa: {NR.add(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)) : NR.Run & D.Bytes},
  +speca: {FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>},
  +outa: {String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String},
  fl: FL.LoopR(Nat.add(bn2, 2n), nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, w, ipx, False{}, RD.items(f2, b2))) -> SrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w):
  (+l3, q1) = fl
  (+f3, q2) = q1
  (+b3, q3) = q2
  (+bn3, q4) = q3
  (+ow3, q5) = q4
  (+ns3, q6) = q5
  (+x3, q7) = q6
  (eqf, q8) = q7
  (invf, flr) = q8
  +m1 = AB.subst(NR.Run, z => {(z, C.BT(sl, st)) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3}), C.BT(sl, st)) : NR.Run & D.Bytes}, P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3}), NR.flush.go(Nat.add(bn2, 2n), NR.Fl{P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), True{}}, w, ipx, False{}),
    Equal.sym(NR.Run, NR.flush.go(Nat.add(bn2, 2n), NR.Fl{P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), True{}}, w, ipx, False{}), P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3}), eqf), {==})
  +eq = AB.subst(NR.Run & D.Bytes, z => {NR.same_run.k(w, ipx, z) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3}), C.BT(sl, st)) : NR.Run & D.Bytes}, (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)), NR.add(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn),
    Equal.sym(NR.Run & D.Bytes, NR.add(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn), (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)), eqa), m1)
  +fs1 = fsettle(R.flush(R.take_ready(w, ipx, FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow)), NR.spec.last(l, FL.chromof(c))), nl, h, c, cbl, cbt, e, tl2, k, obl2, obt2, ow, ns, l3, f3, b3, bn3, ow3, ns3, x3, NR.spec.last(l, FL.chromof(c)), Nil{}, R.drop_ready(w, ipx, FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow)), B.At{lnx, FL.chromof(c), NR.pos_text(psx, kx)}, flr)
  +fs2 = AB.subst(List<&2, R.Item>, z => {P.settle(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3})) == P.settle(R.emit.ready(R.flush(R.take_ready(w, ipx, z), NR.spec.last(l, FL.chromof(c))), R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), Nil{}, k, String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)), List.reverse(&2, B.Note, ns), False{}}, R.drop_ready(w, ipx, z), B.At{lnx, FL.chromof(c), NR.pos_text(psx, kx)})) : R.RunSt}, FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow), R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)), speca, fs1)
  +fs3 = AB.subst(String, z => {P.settle(P.specRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3})) == P.settle(R.emit.ready(R.flush(R.take_ready(w, ipx, R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow))), NR.spec.last(l, FL.chromof(c))), R.RunSt{nl, True{}, h, c, e, NR.spec.last(l, FL.chromof(c)), Nil{}, k, z, List.reverse(&2, B.Note, ns), False{}}, R.drop_ready(w, ipx, R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow))), B.At{lnx, FL.chromof(c), NR.pos_text(psx, kx)})) : R.RunSt}, String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), outa, fs2)
  (P.RunP{nl, True{}, h, c, cbl, cbt, e, l3, f3, b3, bn3, tl2, k, obl2, obt2, ow3, ns3, x3}, (eq, (invf, fs3)))

def sr.k(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat,
  ad: AD.AddG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx)) -> SrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w):
  (+obl2, q1) = ad
  (+obt2, q2) = q1
  (+f2, q3) = q2
  (+b2, q4) = q3
  (+bn2, q5) = q4
  (+tl2, q6) = q5
  (eqa, q7) = q6
  (inva, q8) = q7
  (speca, q9) = q8
  (outa, lena) = q9
  sr.k2(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, obl2, obt2, f2, b2, bn2, tl2, eqa, speca, outa,
    FL.flush_t(nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, w, ipx, False{}, inva))

# run.bend's same_run on a pictured run that goes on, in the body.
def sr_t(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String, +w: Nat,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  htx: AD.TxtP(t, sl, st, sd, s, sn, tx)) -> SrG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w):
  sr.k(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, w, AD.add_t(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, htx))
