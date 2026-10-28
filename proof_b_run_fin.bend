import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_flush.bend as FL
import ./proof_run_base.bend as RBS
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# run_finish (proof_b_run.bend): the end of the run on a pictured run.

def FinG(+p: P.RunP, +o: B.Opts) -> Type:
  &p2: P.RunP -> &code: Nat -> ({NR.finish(P.mkRun(p), R.Opts.w(o)) == (P.mkRun(p2), code) : NR.Run & Nat}
  & ({RD.RunInv(p2) == True{} : Bool}
  & {R.Report{P.RunSt.out(P.specRun(p2)), P.RunSt.notes(P.specRun(p2)), code} == R.finish(P.specRun(p)) : R.Report}))

# pre once the run stopped, with any notes.
def pre_halt(+i: Bool, +obl: U32, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +x: Bool, +ns: List<&2, B.Note>, +ns2: List<&2, B.Note>,
  +h: {RD.pre(i, obl, f, b, x, ns) == True{} : Bool}) -> {RD.pre(i, obl, f, b, True{}, ns2) == True{} : Bool}:
  match i:
    case True{}:
      {==}
    case False{}:
      +R0 = RD.is_nil(f) && (RD.is_nil(b) && (x || RD.no_notes(ns)))
      +hr = LM.andr(U32.is_zero(obl), R0, h)
      +hr2 = LM.andr(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(ns)), hr)
      LM.and_mk(U32.is_zero(obl), RD.is_nil(f) && (RD.is_nil(b) && (True{} || RD.no_notes(ns2))), LM.andl(U32.is_zero(obl), R0, h),
        LM.and_mk(RD.is_nil(f), RD.is_nil(b) && (True{} || RD.no_notes(ns2)), LM.andl(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(ns)), hr),
          LM.and_mk(RD.is_nil(b), True{} || RD.no_notes(ns2), LM.andl(RD.is_nil(b), x || RD.no_notes(ns), hr2), {==})))

def pr(+i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +ns2: List<&2, B.Note>,
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) ->
  {RD.inv.k(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns2, True{}) == True{} : Bool}:
  PI.inv_mk(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns2, True{},
    (PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr2(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr3(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr4(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
    ({==}, ({==}, (PI.pr7(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr8(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr9(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
    (pre_halt(i, obl, f, b, x, ns, ns2, PI.pr10(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)), PI.pr11(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))))))))))))

# The invariant with other notes, in the body.
def ns_body(+h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +x: Bool, +ns2: List<&2, B.Note>,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x) == True{} : Bool}) ->
  {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns2, x) == True{} : Bool}:
  PI.inv_mk(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns2, x,
    (PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr2(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr3(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr4(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
    (PI.pr5(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr6(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr7(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr8(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi), (PI.pr9(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi),
    ({==}, PI.pr11(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi))))))))))))

# After the flush of everything, by its outcome.
def fin.c(fl: R.Flush, +k: R.Cnt, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +l2: Maybe<&2, NR.Ck>, +f2: List<&2, NR.Ck>, +b2: List<&2, NR.Ck>, +bn2: Nat, +ow2: U32, +ns2: List<&2, B.Note>, +x2: Bool,
  +hF: {R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))) == fl : R.Flush},
  +eq: {NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, R.Opts.w(o), 0n, True{}) == P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, x2}) : NR.Run},
  +hinv: {RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, x2) == True{} : Bool},
  flr: FL.FLR(FL.fs(fl), Maybe.default(&2, String, c, ""), NR.chars(D.view(C.BT(obl, obt))), ow, ns, Nil{}, l2, f2, b2, ow2, ns2, x2)) -> FinG(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}, o):
  match fl k:
    case R.Flushed{+o2, +la} R.Cnt{+c1, +c2, +c3, +c4}:
      (+hx2, q1) = flr
      (hout, q2) = q1
      (hns, q3) = q2
      +kk = {R.Cnt{c1, c2, c3, c4} : R.Cnt}
      +SU = {B.Summary{c1, c2, c3, c4} : B.Note}
      +p2 = {P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, kk, obl, obt, ow2, SU <> ns2, False{}} : P.RunP}
      +ex = AB.subst(Bool, z => {NR.finish.k(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, kk, obl, obt, ow2, ns2, z})) == (P.mkRun(p2), 0n) : NR.Run & Nat}, False{}, x2, Equal.sym(Bool, x2, False{}, hx2), {==})
      +eqf = AB.subst(NR.Run, z => {NR.finish.k(z) == (P.mkRun(p2), 0n) : NR.Run & Nat}, P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, kk, obl, obt, ow2, ns2, x2}), NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), True{}}, R.Opts.w(o), 0n, True{}),
        Equal.sym(NR.Run, NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, kk, obl, obt, ow, ns, False{}}), True{}}, R.Opts.w(o), 0n, True{}), P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, kk, obl, obt, ow2, ns2, x2}), eq), ex)
      +hinv2 = ns_body(h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, False{}, SU <> ns2,
        AB.subst(Bool, z => {RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, z) == True{} : Bool}, x2, False{}, hx2, hinv))
      +RNS = List.reverse(&2, B.Note, ns)
      +erep = AB.subst(String, z => {R.Report{z, List.reverse(&2, B.Note, SU <> ns2), 0n} == R.finish.flush(R.Flushed{o2, la}, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, kk) : R.Report},
        String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), Equal.sym(String, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), hout),
        AB.subst(List<&2, B.Note>, z => {R.Report{String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), z, 0n} == R.finish.flush(R.Flushed{o2, la}, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, kk) : R.Report},
          List.append(&2, B.Note, RNS, [SU]), List.reverse(&2, B.Note, SU <> ns2),
          Equal.sym(List<&2, B.Note>, List.reverse(&2, B.Note, SU <> ns2), List.append(&2, B.Note, RNS, [SU]),
            AB.subst(List<&2, B.Note>, z => {List.reverse(&2, B.Note, SU <> z) == List.append(&2, B.Note, RNS, [SU]) : List<&2, B.Note>}, ns, ns2, Equal.sym(List<&2, B.Note>, ns2, ns, hns), FL.rev_cons(SU, ns))),
          {==}))
      +erep2 = AB.subst(R.Flush, z => {R.Report{String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), List.reverse(&2, B.Note, SU <> ns2), 0n} == R.finish.flush(z, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, kk) : R.Report},
        R.Flushed{o2, la}, R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))), Equal.sym(R.Flush, R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))), R.Flushed{o2, la}, hF), erep)
      (p2, (0n, (eqf, (hinv2, erep2))))
    case R.Broke{+o2, +bad, +prev} _:
      (+hx2, q1) = flr
      (hout, hns) = q1
      +ST = {B.Stop{B.Unsorted{}, Some{bad}, prev} : B.Note}
      +p2 = {P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, True{}} : P.RunP}
      +ex = AB.subst(Bool, z => {NR.finish.k(P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, z})) == (P.mkRun(p2), 1n) : NR.Run & Nat}, True{}, x2, Equal.sym(Bool, x2, True{}, hx2), {==})
      +eqf = AB.subst(NR.Run, z => {NR.finish.k(z) == (P.mkRun(p2), 1n) : NR.Run & Nat}, P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, x2}), NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, R.Opts.w(o), 0n, True{}),
        Equal.sym(NR.Run, NR.flush.go(Nat.add(bn, 2n), NR.Fl{P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, R.Opts.w(o), 0n, True{}), P.mkRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, x2}), eq), ex)
      +hinv2 = AB.subst(Bool, z => {RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, z) == True{} : Bool}, x2, True{}, hx2, hinv)
      +RNS = List.reverse(&2, B.Note, ns)
      +erep = AB.subst(String, z => {R.Report{z, List.reverse(&2, B.Note, ns2), 1n} == R.finish.flush(R.Broke{o2, bad, prev}, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, k) : R.Report},
        String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), Equal.sym(String, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), hout),
        AB.subst(List<&2, B.Note>, z => {R.Report{String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), o2), z, 1n} == R.finish.flush(R.Broke{o2, bad, prev}, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, k) : R.Report},
          List.append(&2, B.Note, RNS, [ST]), List.reverse(&2, B.Note, ns2),
          Equal.sym(List<&2, B.Note>, List.reverse(&2, B.Note, ns2), List.append(&2, B.Note, RNS, [ST]),
            AB.subst(List<&2, B.Note>, z => {List.reverse(&2, B.Note, z) == List.append(&2, B.Note, RNS, [ST]) : List<&2, B.Note>}, ST <> ns, ns2, Equal.sym(List<&2, B.Note>, ns2, ST <> ns, hns), FL.rev_cons(ST, ns))),
          {==}))
      +erep2 = AB.subst(R.Flush, z => {R.Report{String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow2)), List.reverse(&2, B.Note, ns2), 1n} == R.finish.flush(z, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RNS, k) : R.Report},
        R.Broke{o2, bad, prev}, R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))), Equal.sym(R.Flush, R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))), R.Broke{o2, bad, prev}, hF), erep)
      (p2, (1n, (eqf, (hinv2, erep2))))

def fin.k(+o: B.Opts, +k: R.Cnt, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>,
  fl: FL.LoopR(Nat.add(bn, 2n), n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, R.Opts.w(o), 0n, True{}, RD.items(f, b))) -> FinG(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}, o):
  (+l2, q1) = fl
  (+f2, q2) = q1
  (+b2, q3) = q2
  (+bn2, q4) = q3
  (+ow2, q5) = q4
  (+ns2, q6) = q5
  (+x2, q7) = q6
  (eq, q8) = q7
  (hinv, flr) = q8
  fin.c(R.flush(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), Maybe.default(&2, String, c, ""), String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))), NR.spec.last(l, Maybe.default(&2, String, c, ""))), k, o, n, h, c, cbl, cbt, e, l, f, b, bn, tl, obl, obt, ow, ns, l2, f2, b2, bn2, ow2, ns2, x2, {==}, eq, hinv, flr)

def fin_t(+p: P.RunP, +o: B.Opts, +hi: {RD.RunInv(p) == True{} : Bool}) -> FinG(p, o):
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, True{}}:
      (P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, True{}}, (1n, ({==}, (hi, {==}))))
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, False{}}:
      +hp = PI.pr10(False{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
      +hz = LM.andl(U32.is_zero(obl), RD.is_nil(f) && (RD.is_nil(b) && (False{} || RD.no_notes(ns))), hp)
      +e0 = U.is_eq_true(obl, 0, hz)
      +p2 = {P.RunP{n, False{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, [B.Stop{B.NoHeader{}, None{}, None{}}], True{}} : P.RunP}
      +hout = AB.subst(U32, z => {String.take(NR.chars(D.view(C.BT(z, obt))), U32.to_nat(ow)) == "" : String}, 0, obl, Equal.sym(U32, obl, 0, e0),
        AB.subst(List<&2, U32>, z => {String.take(NR.chars(z), U32.to_nat(ow)) == "" : String}, Nil{}, D.view(C.BT(0, obt)), Equal.sym(List<&2, U32>, D.view(C.BT(0, obt)), Nil{}, BF.view0(obt)), {==}))
      +erep = AB.subst(String, z => {R.Report{z, [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} == R.Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} : R.Report}, "", String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), Equal.sym(String, String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), "", hout), {==})
      (p2, (1n, ({==}, (pr(False{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, [B.Stop{B.NoHeader{}, None{}, None{}}], hi), erep))))
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, False{}}:
      fin.k(o, k, n, h, c, cbl, cbt, e, l, f, b, bn, tl, obl, obt, ow, ns, FL.flush_t(n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, R.Opts.w(o), 0n, True{}, hi))
