import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_inv.bend as PI
import ./proof_e_defs.bend as SD
import ./proof_e_merge_lem.bend as ML
import ./proof_e_merge_sp.bend as MS
import ./proof_e_merge_ok.bend as OK
import ./proof_run_base.bend as RB
import ../lawful-words/proof_nat.bend as N
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/defs.bend as A
import ../lawful-arrays/proof_tree.bend as AT

# Phase E, area "merge": the merged run, with S's output buffer and notes
# handed out before it, stands for SD.shiftS (merge_spec, at the level of the
# runs' fields): field by field on the settled states.

# T's last is the phantom and S's CHROM is y: merge.ok's phantom test makes
# T's CHROM c0, which is y when S's CHROM is c0.
def last_k(+sm: Bool, +y: String, +tc: Maybe<&2, String>, +c0: String, +k: Nat, +ip: Nat, +p: Maybe<&2, String>, +n: U32, +sl: Maybe<&2, NR.Ck>, +sf: List<&2, NR.Ck>, +sb: List<&2, NR.Ck>, +sn: Nat, +u: String,
  +hsm: {String.eq(y, c0) == sm : Bool},
  +hph: {R.is_cur(tc, c0) == True{} : Bool}) -> {P.blank(NR.spec.last(W.last_of.k(True{}, NR.Ck{k, ip, 0n, p, n}, sm, sl, W.buf_last(sf, sb), sn), Maybe.default(&2, String, tc, ""))) == P.blank(SD.last_shift.k(True{}, NR.spec.item(NR.Ck{k, ip, 0n, p, n}, Maybe.default(&2, String, tc, ""), ""), sm, NR.spec.last(sl, y), SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), y, u)), sn)) : Maybe<&2, R.Item>}:
  match sm:
    case False{}:
      {==}
    case True{}:
      match tc:
        case None{}:
          Empty.absurd({P.blank(NR.spec.last(W.last_of.k(True{}, NR.Ck{k, ip, 0n, p, n}, sm, sl, W.buf_last(sf, sb), sn), "")) == P.blank(SD.last_shift.k(True{}, NR.spec.item(NR.Ck{k, ip, 0n, p, n}, "", ""), sm, NR.spec.last(sl, y), SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), y, u)), sn)) : Maybe<&2, R.Item>}, N.false_ne_true(hph))
        case Some{+x}:
          +hx = RB.str_eq_sound(x, c0, hph)
          +hy = RB.str_eq_sound(y, c0, hsm)
          +hxy = Equal.trans(String, y, c0, x, hy, Equal.sym(String, x, c0, hx))
          %hxy : {P.blank(NR.spec.last(Maybe.or(&2, NR.Ck, W.buf_last(sf, sb), sl), _)) == P.blank(Maybe.or(&2, R.Item, SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), y, u)), NR.spec.last(sl, y))) : Maybe<&2, R.Item>}
          MS.last_same(sf, sb, sl, y, u)

law last_eq:
  for +tl: Maybe<&2, NR.Ck>
  for +sl: Maybe<&2, NR.Ck>
  for +sf: List<&2, NR.Ck>
  for +sb: List<&2, NR.Ck>
  for +sn: Nat
  for +tc: Maybe<&2, String>
  for +sc: Maybe<&2, String>
  for +c0: String
  for +u: String
  for +hph: {Bool.or(Bool.not(W.last_ph(tl)), R.is_cur(tc, c0)) == True{} : Bool}
  {P.blank(NR.spec.last(W.last_of(tl, R.is_cur(sc, c0), sl, W.buf_last(sf, sb), sn), Maybe.default(&2, String, tc, ""))) == P.blank(SD.last_shift(NR.spec.last(tl, Maybe.default(&2, String, tc, "")), R.is_cur(sc, c0), NR.spec.last(sl, Maybe.default(&2, String, sc, "")), SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), u)), sn)) : Maybe<&2, R.Item>}

def last_eq(tl, sl, sf, sb, sn, tc, sc, c0, u, hph):
  match tl:
    case None{}:
      {==}
    case Some{+c}:
      match c:
        case NR.Ck{+k, +ip, +ln, +p, +n}:
          match ln:
            case 1n+q:
              {==}
            case 0n:
              match sc:
                case None{}:
                  {==}
                case Some{+y}:
                  last_k(String.eq(y, c0), y, tc, c0, k, ip, p, n, sl, sf, sb, sn, u, {==}, hph)

# S's whole output buffer: what it wrote, then its items' texts.
law out_eq:
  for +obl: U32
  for +obt: AT.Tree<U32>
  for +ow: U32
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +X: String
  for +hsum: {Nat.add(U32.to_nat(ow), RD.lens(cs)) == U32.to_nat(obl) : Nat}
  {String.append(NR.chars(D.view(C.BT(obl, obt))), X) == String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(SD.texts(NR.spec.items(cs, ch, String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)))), X)) : String}

def out_eq(obl, obt, ow, cs, ch, X, hsum):
  +e01 = Equal.cong(String, String, z => String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(z, X)), SD.texts(NR.spec.items(cs, ch, String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)))), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs)), MS.texts_take(cs, ch, String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow))))
  +e12 = Equal.sym(String, String.append(String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs))), X), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs)), X)), ML.str_assoc(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs)), X))
  +e23 = Equal.cong(String, String, z => String.append(z, X), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs))), String.take(NR.chars(D.view(C.BT(obl, obt))), Nat.add(U32.to_nat(ow), RD.lens(cs))), Equal.sym(String, String.take(NR.chars(D.view(C.BT(obl, obt))), Nat.add(U32.to_nat(ow), RD.lens(cs))), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs))), ML.take_add(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow), RD.lens(cs))))
  +e34 = Equal.cong(Nat, String, z => String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), z), X), Nat.add(U32.to_nat(ow), RD.lens(cs)), U32.to_nat(obl), hsum)
  +e45 = Equal.cong(String, String, z => String.append(z, X), String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(obl)), NR.chars(D.view(C.BT(obl, obt))), ML.ctake(D.unpack(A.view(U32, AT.fromT(U32, obt))), U32.to_nat(obl)))
  Equal.sym(String, String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(SD.texts(NR.spec.items(cs, ch, String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)))), X)), String.append(NR.chars(D.view(C.BT(obl, obt))), X),
    Equal.trans(String, String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(SD.texts(NR.spec.items(cs, ch, String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)))), X)), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs)), X)), String.append(NR.chars(D.view(C.BT(obl, obt))), X), e01,
      Equal.trans(String, String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.append(String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs)), X)), String.append(String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs))), X), String.append(NR.chars(D.view(C.BT(obl, obt))), X), e12,
        Equal.trans(String, String.append(String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), String.take(String.drop(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(ow)), RD.lens(cs))), X), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), Nat.add(U32.to_nat(ow), RD.lens(cs))), X), String.append(NR.chars(D.view(C.BT(obl, obt))), X), e23,
          Equal.trans(String, String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), Nat.add(U32.to_nat(ow), RD.lens(cs))), X), String.append(String.take(NR.chars(D.view(C.BT(obl, obt))), U32.to_nat(obl)), X), String.append(NR.chars(D.view(C.BT(obl, obt))), X), e34, e45)))))

law st_cong:
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e1: List<&2, String>
  for +e2: List<&2, String>
  for +l1: Maybe<&2, R.Item>
  for +l2: Maybe<&2, R.Item>
  for +b1: List<&2, R.Item>
  for +b2: List<&2, R.Item>
  for +k1: R.Cnt
  for +k2: R.Cnt
  for +o1: String
  for +o2: String
  for +ns1: List<&2, B.Note>
  for +ns2: List<&2, B.Note>
  for +he: {e1 == e2 : List<&2, String>}
  for +hl: {P.blank(l1) == P.blank(l2) : Maybe<&2, R.Item>}
  for +hb: {b1 == b2 : List<&2, R.Item>}
  for +hk: {k1 == k2 : R.Cnt}
  for +ho: {o1 == o2 : String}
  for +hns: {ns1 == ns2 : List<&2, B.Note>}
  {P.settle(R.RunSt{n, True{}, h, c, e1, l1, b1, k1, o1, ns1, False{}}) == P.settle(R.RunSt{n, True{}, h, c, e2, l2, b2, k2, o2, ns2, False{}}) : R.RunSt}

def st_cong(n, h, c, e1, e2, l1, l2, b1, b2, k1, k2, o1, o2, ns1, ns2, he, hl, hb, hk, ho, hns):
  %he : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, _, P.blank(l2), b2, k2, o2, ns2, False{}} : R.RunSt}
  %hl : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, e1, _, b2, k2, o2, ns2, False{}} : R.RunSt}
  %hb : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, e1, P.blank(l1), _, k2, o2, ns2, False{}} : R.RunSt}
  %hk : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, _, o2, ns2, False{}} : R.RunSt}
  %ho : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, _, ns2, False{}} : R.RunSt}
  %hns : {R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, ns1, False{}} == R.RunSt{n, True{}, h, c, e1, P.blank(l1), b1, k1, o1, _, False{}} : R.RunSt}
  {==}

# merge_spec on the runs' fields (s* for S's, t* for T's).
def spec_w(+l: Nat, +w: Nat, +c0: String, +sn: Nat, +si: Bool, +sh: String, +sc: Maybe<&2, String>, +scbl: U32, +scbt: AT.Tree<U32>, +se: List<&2, String>, +sl: Maybe<&2, NR.Ck>, +sf: List<&2, NR.Ck>, +sb: List<&2, NR.Ck>, +sbn: Nat, +stl: Nat, +sk: R.Cnt, +sobl: U32, +sobt: AT.Tree<U32>, +sow: U32, +sns: List<&2, B.Note>, +sx: Bool, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +tcbl: U32, +tcbt: AT.Tree<U32>, +te: List<&2, String>, +tl: Maybe<&2, NR.Ck>, +tf: List<&2, NR.Ck>, +tb: List<&2, NR.Ck>, +tbn: Nat, +ttl: Nat, +tk: R.Cnt, +tobl: U32, +tobt: AT.Tree<U32>, +tow: U32, +tns: List<&2, B.Note>, +tx: Bool,
  +hs: {RD.inv.k(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx) == True{} : Bool},
  +hok: {W.merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx) == True{} : Bool}) -> {P.settle(R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, NR.push_cur(sc, se))), NR.spec.last(W.last_of(tl, R.is_cur(sc, c0), sl, W.buf_last(sf, sb), sn), Maybe.default(&2, String, tc, "")), NR.spec.items(NR.append_ck(W.cks_shift(sn, tf), NR.rev_ck(W.cks_shift(sn, tb), Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), W.cnt_add(sk, tk), String.append(NR.chars(D.view(C.BT(sobl, sobt))), String.take(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), List.append(&2, B.Note, List.reverse(&2, B.Note, sns), Nil{}), False{}}) == P.settle(R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, R.push_cur(sc, se))), SD.last_shift(NR.spec.last(tl, Maybe.default(&2, String, tc, "")), R.is_cur(sc, c0), NR.spec.last(sl, Maybe.default(&2, String, sc, "")), SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), String.drop(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)))), sn), SD.items_shift(sn, NR.spec.items(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)))), SD.cnt_add(sk, tk), String.append(String.take(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)), String.append(SD.texts(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), String.drop(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)))), String.take(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)))), List.reverse(&2, B.Note, sns), False{}}) : R.RunSt}:
  +hsx = ML.not_t(sx, OK.ok3(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +x5 = PI.pr5(si, sh, sc, scbl, scbt, sf, sb, sbn, stl, sobl, sobt, sow, sns, sx, hs)
  +hsum = N.eq_sound(Nat.add(U32.to_nat(sow), RD.lens(RD.items(sf, sb))), U32.to_nat(sobl), ML.or_fl(sx, Nat.is_eq(Nat.add(U32.to_nat(sow), RD.lens(RD.items(sf, sb))), U32.to_nat(sobl)), hsx, x5))
  +he = Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, z)), NR.push_cur(sc, se), R.push_cur(sc, se), ML.push_eq(sc, se))
  +hl = last_eq(tl, sl, sf, sb, sn, tc, sc, c0, String.drop(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)), OK.ok8(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +hb = Equal.trans(List<&2, R.Item>, NR.spec.items(NR.append_ck(W.cks_shift(sn, tf), NR.rev_ck(W.cks_shift(sn, tb), Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), NR.spec.items(W.cks_shift(sn, NR.append_ck(tf, NR.rev_ck(tb, Nil{}))), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), SD.items_shift(sn, NR.spec.items(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)))),
    Equal.cong(List<&2, NR.Ck>, List<&2, R.Item>, z => NR.spec.items(z, Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), NR.append_ck(W.cks_shift(sn, tf), NR.rev_ck(W.cks_shift(sn, tb), Nil{})), W.cks_shift(sn, NR.append_ck(tf, NR.rev_ck(tb, Nil{}))), ML.shift_items(sn, tf, tb)),
    MS.sp_shift(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), sn, Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))))
  +ho = out_eq(sobl, sobt, sow, NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), String.take(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)), hsum)
  st_cong(Nat.add(sn, tn), sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, NR.push_cur(sc, se))), List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, R.push_cur(sc, se))), NR.spec.last(W.last_of(tl, R.is_cur(sc, c0), sl, W.buf_last(sf, sb), sn), Maybe.default(&2, String, tc, "")), SD.last_shift(NR.spec.last(tl, Maybe.default(&2, String, tc, "")), R.is_cur(sc, c0), NR.spec.last(sl, Maybe.default(&2, String, sc, "")), SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), String.drop(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)))), sn), NR.spec.items(NR.append_ck(W.cks_shift(sn, tf), NR.rev_ck(W.cks_shift(sn, tb), Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), SD.items_shift(sn, NR.spec.items(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), Maybe.default(&2, String, tc, ""), String.drop(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)))), W.cnt_add(sk, tk), SD.cnt_add(sk, tk), String.append(NR.chars(D.view(C.BT(sobl, sobt))), String.take(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow))), String.append(String.take(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)), String.append(SD.texts(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), Maybe.default(&2, String, sc, ""), String.drop(NR.chars(D.view(C.BT(sobl, sobt))), U32.to_nat(sow)))), String.take(NR.chars(D.view(C.BT(tobl, tobt))), U32.to_nat(tow)))), List.append(&2, B.Note, List.reverse(&2, B.Note, sns), Nil{}), List.reverse(&2, B.Note, sns), he, hl, hb, ML.cnt_eq(sk, tk), ho, ML.note_app_nil(List.reverse(&2, B.Note, sns)))
