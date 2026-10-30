import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_e_defs.bend as SD
import ./proof_e_merge_lem.bend as ML
import ./proof_e_merge_sp.bend as MS
import ./proof_e_merge_ok.bend as OK
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area "merge": merge.ok on the byte runs gives SD.segok on the
# states they stand for (merge_segok, at the level of the runs' fields).
# merge.ok bounds max(E) by S's tail key (tl bounds every buffered key), at
# least segok's max(E); the other tests are the same on the pictures.


def g10_m(+ee: Bool, +maxeS: Nat, +maxeW: Nat, +w: Nat, +mlow: Nat,
  +hme: {Nat.is_le(maxeS, maxeW) == True{} : Bool},
  +hC: {Bool.or(ee, Nat.is_le(Nat.add(maxeW, w), mlow)) == True{} : Bool}) -> {Bool.or(ee, Nat.is_le(Nat.add(maxeS, w), mlow)) == True{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      N.le_trans(Nat.add(maxeS, w), Nat.add(maxeW, w), mlow, N.le_add_mono_r(w, maxeS, maxeW, hme), hC)

def g10_c(+ch: Bool, +eeS: Bool, +eeW: Bool, +hee: {eeS == eeW : Bool}, +maxeS: Nat, +maxeW: Nat, +w: Nat, +mlowS: Nat, +mlowW: Nat, +hml: {mlowS == mlowW : Nat}, +hme: {Nat.is_le(maxeS, maxeW) == True{} : Bool}, +kgS: Bool, +kgf: Bool, +kgb: Bool, +hkg: {kgS == Bool.and(kgf, kgb) : Bool},
  +hB: {Bool.or(ch, Bool.and(kgf, kgb)) == True{} : Bool},
  +hC: {Bool.or(Bool.or(ch, eeW), Nat.is_le(Nat.add(maxeW, w), mlowW)) == True{} : Bool}) -> {Bool.or(ch, Bool.and(kgS, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS)))) == True{} : Bool}:
  match ch:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, kgS, True{}, Equal.trans(Bool, kgS, Bool.and(kgf, kgb), True{}, hkg, hB)) : {Bool.and(_, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS))) == True{} : Bool}
      %Equal.sym(Bool, eeS, eeW, hee) : {Bool.or(_, Nat.is_le(Nat.add(maxeS, w), mlowS)) == True{} : Bool}
      %Equal.sym(Nat, mlowS, mlowW, hml) : {Bool.or(eeW, Nat.is_le(Nat.add(maxeS, w), _)) == True{} : Bool}
      g10_m(eeW, maxeS, maxeW, w, mlowW, hme, hC)

def g10_s(+ch: Bool, +l: Nat, +eeS: Bool, +eeW: Bool, +hee: {eeS == eeW : Bool}, +maxeS: Nat, +maxeW: Nat, +w: Nat, +mlowS: Nat, +mlowW: Nat, +hml: {mlowS == mlowW : Nat}, +hme: {Nat.is_le(maxeS, maxeW) == True{} : Bool}, +kgS: Bool, +kgf: Bool, +kgb: Bool, +hkg: {kgS == Bool.and(kgf, kgb) : Bool},
  +h: {Bool.and(Bool.and(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb))), Bool.or(Bool.or(ch, eeW), Nat.is_le(Nat.add(maxeW, w), mlowW))) == True{} : Bool}) -> {Bool.and(Nat.is_le(maxeS, l), Bool.or(ch, Bool.and(kgS, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS))))) == True{} : Bool}:
  +hAB = N.and_true_l(Bool.and(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb))), Bool.or(Bool.or(ch, eeW), Nat.is_le(Nat.add(maxeW, w), mlowW)), h)
  +hC2 = N.and_true_r(Bool.and(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb))), Bool.or(Bool.or(ch, eeW), Nat.is_le(Nat.add(maxeW, w), mlowW)), h)
  +hA = N.and_true_l(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb)), hAB)
  +hB2 = N.and_true_r(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb)), hAB)
  ML.and_mk(Nat.is_le(maxeS, l), Bool.or(ch, Bool.and(kgS, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS)))), N.le_trans(maxeS, maxeW, l, hme, hA), g10_c(ch, eeS, eeW, hee, maxeS, maxeW, w, mlowS, mlowW, hml, hme, kgS, kgf, kgb, hkg, hB2, hC2))

def g10(+same: Bool, +ch: Bool, +l: Nat, +eeS: Bool, +eeW: Bool, +hee: {eeS == eeW : Bool}, +maxeS: Nat, +maxeW: Nat, +w: Nat, +mlowS: Nat, +mlowW: Nat, +hml: {mlowS == mlowW : Nat}, +hme: {Nat.is_le(maxeS, maxeW) == True{} : Bool}, +kgS: Bool, +kgf: Bool, +kgb: Bool, +hkg: {kgS == Bool.and(kgf, kgb) : Bool},
  +h: {Bool.or(Bool.not(same), Bool.and(Bool.and(Nat.is_le(maxeW, l), Bool.or(ch, Bool.and(kgf, kgb))), Bool.or(Bool.or(ch, eeW), Nat.is_le(Nat.add(maxeW, w), mlowW)))) == True{} : Bool}) -> {Bool.or(Bool.not(same), Bool.and(Nat.is_le(maxeS, l), Bool.or(ch, Bool.and(kgS, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS)))))) == True{} : Bool}:
  match same:
    case False{}:
      {==}
    case True{}:
      g10_s(ch, l, eeS, eeW, hee, maxeS, maxeW, w, mlowS, mlowW, hml, hme, kgS, kgf, kgb, hkg, h)

law rev_empty:
  for +ns: List<&2, B.Note>
  for +h: {List.is_empty(&2, B.Note, ns) == True{} : Bool}
  {List.is_empty(&2, B.Note, List.reverse(&2, B.Note, ns)) == True{} : Bool}

def rev_empty(ns, h):
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({List.is_empty(&2, B.Note, List.reverse(&2, B.Note, Con{x, t})) == True{} : Bool}, N.false_ne_true(h))

# The largest key of items with keys at most k, from m: at most any K above
# both.
law mk_le:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +m: Nat
  for +k: Nat
  for +kk: Nat
  for +hk: {RD.keys_le(cs, k) == True{} : Bool}
  for +hkK: {Nat.is_le(k, kk) == True{} : Bool}
  for +hm: {Nat.is_le(m, kk) == True{} : Bool}
  {Nat.is_le(SD.maxkey(NR.spec.items(cs, ch, t), m), kk) == True{} : Bool}

def mk_le(cs, ch, t, m, k, kk, hk, hkK, hm):
  match cs:
    case Nil{}:
      hm
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+ck, +ip, +ln, +p, +n}:
          mk_le(rest, ch, String.drop(t, U32.to_nat(n)), Nat.max(m, ck), k, kk, N.and_true_r(Nat.is_le(ck, k), RD.keys_le(rest, k), hk), hkK,
            ML.max_le(m, ck, kk, hm, N.le_trans(ck, k, kk, N.and_true_l(Nat.is_le(ck, k), RD.keys_le(rest, k), hk), hkK)))

# segok's max(E) is at most merge.ok's (tl for a buffer with items).
law maxe_le:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +m: Nat
  for +tl: Nat
  for +hk: {RD.keys_le(cs, tl) == True{} : Bool}
  {Nat.is_le(SD.maxkey(NR.spec.items(cs, ch, t), m), Nat.max(Bool.pick(Nat, RD.is_nil(cs), 0n, tl), m)) == True{} : Bool}

def maxe_le(cs, ch, t, m, tl, hk):
  match cs:
    case Nil{}:
      N.le_refl(m)
    case Con{+c, +rest}:
      mk_le(Con{c, rest}, ch, t, m, tl, Nat.max(tl, m), hk, ML.le_max_l(tl, m), ML.le_max_r(tl, m))

def segok_w(+w: Nat, +c0: String, +l: Nat, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, NR.Ck>, +sf: List<&2, NR.Ck>, +sb: List<&2, NR.Ck>, +sbn: Nat, +stl: Nat, +si: Bool, +sx: Bool, +tn: Nat, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, NR.Ck>, +tf: List<&2, NR.Ck>, +tb: List<&2, NR.Ck>, +tns: List<&2, B.Note>, +ti: Bool, +tx: Bool, +sch: String, +st: String, +tch: String, +tt: String,
  +hok: {W.merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx) == True{} : Bool},
  +hbn: {Bool.or(sx, Nat.is_eq(sbn, Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb)))) == True{} : Bool},
  +hkf: {RD.keys_le(sf, stl) == True{} : Bool},
  +hkb: {RD.keys_le(sb, stl) == True{} : Bool}) -> {SD.segok.k(w, c0, l, sc, se, NR.spec.last(sl, sch), NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), sch, st), si, sx, tn, tc, te, NR.spec.last(tl, tch), NR.spec.items(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), tch, tt), List.reverse(&2, B.Note, tns), tx) == True{} : Bool}:
  +sits = NR.append_ck(sf, NR.rev_ck(sb, Nil{}))
  +tits = NR.append_ck(tf, NR.rev_ck(tb, Nil{}))
  +sB = NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), sch, st)
  +tB = NR.spec.items(NR.append_ck(tf, NR.rev_ck(tb, Nil{})), tch, tt)
  +sL = NR.spec.last(sl, sch)
  +tL = NR.spec.last(tl, tch)
  +same = R.is_cur(sc, c0)
  +ch = Bool.not(List.is_empty(&2, String, te))
  +eeW = Nat.is_eq(sbn, 0n)
  +eeS = List.is_empty(&2, R.Item, sB)
  +maxeW = Nat.max(Bool.pick(Nat, eeW, 0n, stl), W.key_or(sl, 0n))
  +maxeS = SD.maxkey(sB, SD.key_or(sL, 0n))
  +pk = Bool.pick(Nat, ch, 0n, W.real_inpos(tl))
  +mlowW = W.max_inpos(tf, W.max_inpos(tb, pk))
  +mlowS = SD.max_inpos(tB, Bool.pick(Nat, ch, 0n, SD.real_inpos(tL)))
  +kgS = SD.keys_ge(tB, l)
  +kgf = W.keys_ge(tf, l)
  +kgb = W.keys_ge(tb, l)
  +hsx = ML.not_t(sx, OK.ok3(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +hsbn = N.eq_sound(sbn, Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb)), ML.or_fl(sx, Nat.is_eq(sbn, Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb))), hsx, hbn))
  +heeW = Equal.trans(Bool, RD.is_nil(sits), Nat.is_eq(Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb)), 0n), eeW, ML.nil_items(sf, sb),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb)), sbn, Equal.sym(Nat, sbn, Nat.add(List.length(&2, NR.Ck, sf), List.length(&2, NR.Ck, sb)), hsbn)))
  +hee = Equal.trans(Bool, eeS, RD.is_nil(sits), eeW, MS.sp_is_empty(sits, sch, st), heeW)
  +g1 = OK.ok1(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok)
  +g2 = OK.ok3(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok)
  +g3 = OK.ok4(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok)
  +g4 = rev_empty(tns, OK.ok5(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +g5 = OK.ok6(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok)
  +g6 = OK.ok7(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok)
  +g7 = Equal.trans(Bool, SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc), W.chroms_ok(List.append(&2, String, W.cur_list(tc), te), c0, se, sc), True{}, ML.chroms_full(tc, te, c0, se, sc), OK.ok9(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +g8 = Equal.trans(Bool, SD.sorted(sB), W.sorted(sits), True{}, MS.sp_sorted(sits, sch, st), OK.ok10(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +kS = SD.key_or(SD.first_item(sB), 0n)
  +kW = W.key_or(W.buf_first(sf, sb), 0n)
  +eqk = Equal.trans(Nat, kS, W.key_or(W.first_ck(sits), 0n), kW, MS.sp_key_first(sits, sch, st, 0n),
    Equal.cong(Maybe<&2, NR.Ck>, Nat, z => W.key_or(z, 0n), W.first_ck(sits), W.buf_first(sf, sb), ML.first_items(sf, sb)))
  +eql = Equal.trans(Bool, SD.last_le(sL, kS), SD.last_le(sL, kW), NR.last_le(sl, kW),
    Equal.cong(Nat, Bool, z => SD.last_le(sL, z), kS, kW, eqk), MS.sp_last_le(sl, sch, kW))
  +g9 = Equal.trans(Bool, Bool.or(eeS, SD.last_le(sL, kS)), Bool.or(eeW, NR.last_le(sl, kW)), True{},
    ML.or_cong(eeS, eeW, SD.last_le(sL, kS), NR.last_le(sl, kW), hee, eql), OK.ok11(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +kl = ML.kl_items(sf, sb, stl, hkf, hkb)
  +x1 = maxe_le(sits, sch, st, W.key_or(sl, 0n), stl, kl)
  +c1 = Equal.cong(Nat, Bool, z => Nat.is_le(SD.maxkey(sB, z), maxeW), SD.key_or(sL, 0n), W.key_or(sl, 0n), MS.sp_key_last(sl, sch, 0n))
  +c2 = Equal.cong(Bool, Bool, z => Nat.is_le(SD.maxkey(sB, W.key_or(sl, 0n)), Nat.max(Bool.pick(Nat, z, 0n, stl), W.key_or(sl, 0n))), eeW, RD.is_nil(sits), Equal.sym(Bool, RD.is_nil(sits), eeW, heeW))
  +hme = Equal.trans(Bool, Nat.is_le(maxeS, maxeW), Nat.is_le(SD.maxkey(sB, W.key_or(sl, 0n)), maxeW), True{}, c1,
    Equal.trans(Bool, Nat.is_le(SD.maxkey(sB, W.key_or(sl, 0n)), maxeW), Nat.is_le(SD.maxkey(sB, W.key_or(sl, 0n)), Nat.max(Bool.pick(Nat, RD.is_nil(sits), 0n, stl), W.key_or(sl, 0n))), True{}, c2, x1))
  +hml = Equal.trans(Nat, mlowS, SD.max_inpos(tB, pk), mlowW,
    Equal.cong(Nat, Nat, z => SD.max_inpos(tB, Bool.pick(Nat, ch, 0n, z)), SD.real_inpos(tL), W.real_inpos(tl), MS.sp_real_inpos(tl, tch)),
    Equal.trans(Nat, SD.max_inpos(tB, pk), W.max_inpos(tits, pk), mlowW, MS.sp_max_inpos(tits, tch, tt, pk), ML.mi_items(tf, tb, pk)))
  +hkg = Equal.trans(Bool, kgS, W.keys_ge(tits, l), Bool.and(kgf, kgb), MS.sp_keys_ge(tits, tch, tt, l), ML.kg_items(tf, tb, l))
  +g10v = g10(same, ch, l, eeS, eeW, hee, maxeS, maxeW, w, mlowS, mlowW, hml, hme, kgS, kgf, kgb, hkg, OK.ok12(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, tns, ti, tx, hok))
  +e1 = si
  +e2 = Bool.not(sx)
  +e3 = Bool.not(tx)
  +e4 = List.is_empty(&2, B.Note, List.reverse(&2, B.Note, tns))
  +e5 = Nat.is_lt(0n, tn)
  +e6 = Bool.not(R.has(c0, se))
  +e7 = SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)
  +e8 = SD.sorted(sB)
  +e9 = Bool.or(eeS, SD.last_le(sL, kS))
  +e10 = Bool.or(Bool.not(same), Bool.and(Nat.is_le(maxeS, l), Bool.or(ch, Bool.and(kgS, Bool.or(eeS, Nat.is_le(Nat.add(maxeS, w), mlowS))))))
  +q1 = e1
  +q2 = Bool.and(q1, e2)
  +q3 = Bool.and(q2, e3)
  +q4 = Bool.and(q3, e4)
  +q5 = Bool.and(q4, e5)
  +q6 = Bool.and(q5, e6)
  +q7 = Bool.and(q6, e7)
  +q8 = Bool.and(q7, e8)
  +q9 = Bool.and(q8, e9)
  +q10 = Bool.and(q9, e10)
  +h2 = ML.and_mk(q1, e2, g1, g2)
  +h3 = ML.and_mk(q2, e3, h2, g3)
  +h4 = ML.and_mk(q3, e4, h3, g4)
  +h5 = ML.and_mk(q4, e5, h4, g5)
  +h6 = ML.and_mk(q5, e6, h5, g6)
  +h7 = ML.and_mk(q6, e7, h6, g7)
  +h8 = ML.and_mk(q7, e8, h7, g8)
  +h9 = ML.and_mk(q8, e9, h8, g9)
  ML.and_mk(q9, e10, h9, g10v)
