import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_inv.bend as PI
import ./proof_e_merge_lem.bend as ML
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Phase E, area "merge": the run merge.if builds is good (merge_inv, at the
# level of the runs' fields): T's buffers and counts with the line numbers
# moved on, S's header, in the body, no notes, not stopped.

def inv_w(+sh: String, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +tcbl: U32, +tcbt: AT.Tree<U32>, +tf: List<&2, NR.Ck>, +tb: List<&2, NR.Ck>, +tbn: Nat, +ttl: Nat, +tobl: U32, +tobt: AT.Tree<U32>, +tow: U32, +tns: List<&2, B.Note>, +tx: Bool, +d: Nat,
  +hh: {E.is_bytes(sh) == True{} : Bool},
  +ht: {RD.inv.k(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, tx) == True{} : Bool},
  +htx: {tx == False{} : Bool}) -> {RD.inv.k(True{}, sh, tc, tcbl, tcbt, W.cks_shift(d, tf), W.cks_shift(d, tb), tbn, ttl, tobl, tobt, tow, Nil{}, False{}) == True{} : Bool}:
  match tx:
    case True{}:
      Empty.absurd({RD.inv.k(True{}, sh, tc, tcbl, tcbt, W.cks_shift(d, tf), W.cks_shift(d, tb), tbn, ttl, tobl, tobt, tow, Nil{}, False{}) == True{} : Bool}, N.true_ne_false(htx))
    case False{}:
      +x5 = PI.pr5(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht)
      +x6 = PI.pr6(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht)
      +x7 = PI.pr7(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht)
      +x8 = PI.pr8(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht)
      +its = RD.items(tf, tb)
      +sits = RD.items(W.cks_shift(d, tf), W.cks_shift(d, tb))
      +eqL = Equal.trans(Nat, RD.lens(sits), RD.lens(W.cks_shift(d, its)), RD.lens(its),
        Equal.cong(List<&2, NR.Ck>, Nat, z => RD.lens(z), sits, W.cks_shift(d, its), ML.shift_items(d, tf, tb)),
        ML.lens_shift(d, its))
      +y5 = Equal.trans(Bool, Nat.is_eq(Nat.add(U32.to_nat(tow), RD.lens(sits)), U32.to_nat(tobl)), Nat.is_eq(Nat.add(U32.to_nat(tow), RD.lens(its)), U32.to_nat(tobl)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_eq(Nat.add(U32.to_nat(tow), z), U32.to_nat(tobl)), RD.lens(sits), RD.lens(its), eqL), x5)
      +eq6 = Equal.trans(Nat, Nat.add(List.length(&2, NR.Ck, W.cks_shift(d, tf)), List.length(&2, NR.Ck, W.cks_shift(d, tb))), Nat.add(List.length(&2, NR.Ck, tf), List.length(&2, NR.Ck, W.cks_shift(d, tb))), Nat.add(List.length(&2, NR.Ck, tf), List.length(&2, NR.Ck, tb)),
        Equal.cong(Nat, Nat, z => Nat.add(z, List.length(&2, NR.Ck, W.cks_shift(d, tb))), List.length(&2, NR.Ck, W.cks_shift(d, tf)), List.length(&2, NR.Ck, tf), ML.len_shift(d, tf)),
        Equal.cong(Nat, Nat, z => Nat.add(List.length(&2, NR.Ck, tf), z), List.length(&2, NR.Ck, W.cks_shift(d, tb)), List.length(&2, NR.Ck, tb), ML.len_shift(d, tb)))
      +y6 = Equal.trans(Bool, Nat.is_eq(tbn, Nat.add(List.length(&2, NR.Ck, W.cks_shift(d, tf)), List.length(&2, NR.Ck, W.cks_shift(d, tb)))), Nat.is_eq(tbn, Nat.add(List.length(&2, NR.Ck, tf), List.length(&2, NR.Ck, tb))), True{},
        Equal.cong(Nat, Bool, z => Nat.is_eq(tbn, z), Nat.add(List.length(&2, NR.Ck, W.cks_shift(d, tf)), List.length(&2, NR.Ck, W.cks_shift(d, tb))), Nat.add(List.length(&2, NR.Ck, tf), List.length(&2, NR.Ck, tb)), eq6), x6)
      +y7 = Equal.trans(Bool, RD.keys_le(W.cks_shift(d, tf), ttl), RD.keys_le(tf, ttl), True{}, ML.kl_shift(d, tf, ttl), x7)
      +y8 = Equal.trans(Bool, RD.keys_le(W.cks_shift(d, tb), ttl), RD.keys_le(tb, ttl), True{}, ML.kl_shift(d, tb, ttl), x8)
      PI.inv_mk(True{}, sh, tc, tcbl, tcbt, W.cks_shift(d, tf), W.cks_shift(d, tb), tbn, ttl, tobl, tobt, tow, Nil{}, False{},
        (PI.pr1(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht),
        (PI.pr2(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht),
        (PI.pr3(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht),
        (PI.pr4(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht),
        (y5, (y6, (y7, (y8, (hh, ({==}, PI.pr11(ti, th, tc, tcbl, tcbt, tf, tb, tbn, ttl, tobl, tobt, tow, tns, False{}, ht))))))))))))
