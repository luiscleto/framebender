import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G
import ./proof_e_seg_lem.bend as EL
import ./proof_e_seg_lem2.bend as E2
import ./proof_e_seg_mono.bend as EM
import ./proof_e_seg_par.bend as EP
import ./proof_e_seg_drain.bend as ED
import ./proof_e_seg_top.bend as ET

# Phase E, area "seg": the assembly. The true run from S over ls is exactly
# SD.shiftS of S and T (proof_e_seg.bend applies P.settle to both sides).

# lift of T's end is shiftS.
law fin:
  for +sn: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +same: Bool
  for +sl: Maybe<&2, R.Item>
  for +elast: Maybe<&2, R.Item>
  for +outr: String
  for +tn: Nat
  for +th: String
  for +tc: Maybe<&2, String>
  for +te: List<&2, String>
  for +tl: Maybe<&2, R.Item>
  for +tb: List<&2, R.Item>
  for +tk: R.Cnt
  for +to: String
  for +tns: List<&2, B.Note>
  for +hq: {q == Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}) : Maybe<&2, R.Item>}
  for +ho: {String.append(p, to) == outr : String}
  {G.lift(sn, sh, z, p, sk, sns, q, R.RunSt{tn, True{}, th, tc, te, tl, tb, tk, to, tns, False{}})
    == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}

def fin(sn, sh, z, p, sk, sns, q, same, sl, elast, outr, tn, th, tc, te, tl, tb, tk, to, tns, hq, ho):
  +rhs = {R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  %P.add_comm(tn, sn) :
    {R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), G.img(q, tl, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(p, to), sns, False{}}
      == R.RunSt{_, True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  %Equal.sym(Maybe<&2, R.Item>, q, Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), hq) :
    {R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), G.img(_, tl, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(p, to), sns, False{}}
      == R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  %ET.img_ls(same, sl, elast, tl, sn) :
    {R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), G.img(Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), tl, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(p, to), sns, False{}}
      == R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), _, SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  %ho :
    {R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), G.img(Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), tl, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(p, to), sns, False{}}
      == R.RunSt{Nat.add(tn, sn), True{}, sh, tc, List.append(&2, String, te, z), G.img(Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), tl, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), _, sns, False{}} : R.RunSt}
  {==}

# The same with T's inbody and halt as variables.
law fin2:
  for +sn: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +same: Bool
  for +sl: Maybe<&2, R.Item>
  for +elast: Maybe<&2, R.Item>
  for +outr: String
  for +tn: Nat
  for +ti: Bool
  for +th: String
  for +tc: Maybe<&2, String>
  for +te: List<&2, String>
  for +tl: Maybe<&2, R.Item>
  for +tb: List<&2, R.Item>
  for +tk: R.Cnt
  for +to: String
  for +tns: List<&2, B.Note>
  for +tx: Bool
  for +eti: {ti == True{} : Bool}
  for +etx: {tx == False{} : Bool}
  for +hq: {q == Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}) : Maybe<&2, R.Item>}
  for +ho: {String.append(p, to) == outr : String}
  {G.lift(sn, sh, z, p, sk, sns, q, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx})
    == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}

def fin2(sn, sh, z, p, sk, sns, q, same, sl, elast, outr, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, eti, etx, hq, ho):
  %Equal.sym(Bool, ti, True{}, eti) :
    {G.lift(sn, sh, z, p, sk, sns, q, R.RunSt{tn, _, th, tc, te, tl, tb, tk, to, tns, tx})
      == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  %Equal.sym(Bool, tx, False{}, etx) :
    {G.lift(sn, sh, z, p, sk, sns, q, R.RunSt{tn, True{}, th, tc, te, tl, tb, tk, to, tns, _})
      == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, z), SD.last_shift(tl, same, sl, elast, sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), outr, sns, False{}} : R.RunSt}
  fin(sn, sh, z, p, sk, sns, q, same, sl, elast, outr, tn, th, tc, te, tl, tb, tk, to, tns, hq, ho)

law ho1:
  for +so: String
  for +sb: List<&2, R.Item>
  for +to: String
  {String.append(String.append(so, L.texts(sb)), to) == String.append(so, String.append(SD.texts(sb), to)) : String}

def ho1(so, sb, to):
  %Equal.sym(String, SD.texts(sb), L.texts(sb), EL.texts_eq(sb)) : {String.append(String.append(so, L.texts(sb)), to) == String.append(so, String.append(_, to)) : String}
  Q.s_append_assoc(so, L.texts(sb), to)

# segok's end condition as Good1's (S's buffer not empty).
law g1_conv:
  for +l: Nat
  for +mb: Nat
  for +tn: Nat
  for +ti: Bool
  for +th: String
  for +tc: Maybe<&2, String>
  for +te: List<&2, String>
  for +tl: Maybe<&2, R.Item>
  for +tb: List<&2, R.Item>
  for +tk: R.Cnt
  for +to: String
  for +tns: List<&2, B.Note>
  for +tx: Bool
  for +a5: {Nat.is_lt(0n, tn) == True{} : Bool}
  for +ab: {(Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && Nat.is_le(mb, SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl)))))) == True{} : Bool}
  {G.G1(l, mb, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool}

def g1_conv(l, mb, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, a5, ab):
  match te:
    case Nil{}:
      S.and_intro(Nat.is_lt(0n, tn), Bool.and(SD.keys_ge(tb, l), Nat.is_le(mb, SD.max_inpos(tb, SD.real_inpos(tl)))), a5, ab)
    case +y <> +ys:
      S.and_intro(Nat.is_lt(0n, tn), True{}, a5, {==})

def segx.ns.k(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool, +rest: List<&2, B.Line>, +l1: B.Line, +eT: {L.run.go(l1 <> rest, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt}, +h1: {R.has(c0, se) == False{} : Bool},
  +h2: {R.is_cur(sc, c0) == False{} : Bool}, +gls: {G.Good(c0, se, sc, L.run.go(rest, fa, o, L.line_step(fa, o, SD.rs0(c0, l), l1))) == True{} : Bool},
  +eti: {ti == True{} : Bool}, +etx: {tx == False{} : Bool}, pr: {L.line_step(fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, l1) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.line_step(fa, o, SD.rs0(c0, l), l1)) : R.RunSt} & {G.inv2(None{}, L.line_step(fa, o, SD.rs0(c0, l), l1)) == True{} : Bool}) ->
  {L.run.go(rest, fa, o, L.line_step(fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, l1)) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}:
  match pr:
    case (e1, iv):
      %Equal.sym(R.RunSt, L.line_step(fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, l1), G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.line_step(fa, o, SD.rs0(c0, l), l1)), e1) : {L.run.go(rest, fa, o, _) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}
      +ep = EP.par(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, c0, se, sc, rest, fa, o, False{}, {==}, h1, h2, L.line_step(fa, o, SD.rs0(c0, l), l1), iv, gls)
      +el = Equal.cong(R.RunSt, R.RunSt, st => G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, st), L.run.go(rest, fa, o, L.line_step(fa, o, SD.rs0(c0, l), l1)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT)
      +ef = fin2(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, False{}, sl, SD.last_item(sb), String.append(so, String.append(SD.texts(sb), to)),
        tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, eti, etx, {==}, ho1(so, sb, to))
      Equal.trans(R.RunSt, L.run.go(rest, fa, o, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.line_step(fa, o, SD.rs0(c0, l), l1))), G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.run.go(rest, fa, o, L.line_step(fa, o, SD.rs0(c0, l), l1))), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}}, ep,
        Equal.trans(R.RunSt, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.run.go(rest, fa, o, L.line_step(fa, o, SD.rs0(c0, l), l1))), G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}}, el, ef))

# S's CHROM is not c0.
def segx.ns(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool, +ls: List<&2, B.Line>, +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt},
  +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool},
  +a8: {SD.sorted(sb) == True{} : Bool}, +a9: {(List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n))) == True{} : Bool}, +gT: {G.Good(c0, se, sc, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool},
  +eti: {ti == True{} : Bool}, +etx: {tx == False{} : Bool}) ->
  {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}:
  match ls:
    case Nil{}:
      Empty.absurd({L.run.go(Nil{}, fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, False{}, se, R.push_cur(sc, se))), SD.last_shift(tl, False{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt},
        P.false_ne_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{c0}, hc)))
    case +l1 <> +rest:
      +f0 = B.Rec.field(B.Rec.fields(B.Line.body(l1)), 0n)
      +ef0 = Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, ""), Some{f0}, Some{c0}, hc)
      +hs = ET.sorted_conv(sb, sl, a8, a9)
      +gls = Equal.trans(Bool, G.Good(c0, se, sc, L.run.go(l1 <> rest, fa, o, SD.rs0(c0, l))), G.Good(c0, se, sc, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), True{},
        Equal.cong(R.RunSt, Bool, st => G.Good(c0, se, sc, st), L.run.go(l1 <> rest, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT), gT)
      +hg1 = EM.good_back(c0, se, sc, rest, fa, o, L.line_step(fa, o, SD.rs0(c0, l), l1), gls)
      segx.ns.k(fa, o, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, rest, l1, eT, h1, h2, gls, eti, etx, ET.first(fa, o, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, l1, ef0, h1, h2, hs, hg1))

# S's CHROM is c0 and its buffer is empty: phase 2 from the start (the
# phantom stands for S's last).
def segx.s0(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +sh: String, +s: String, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool,
  +ls: List<&2, B.Line>, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt}, +h1: {R.has(c0, se) == False{} : Bool}, +esame: {R.is_cur(Some{s}, c0) == True{} : Bool},
  +a10: {Nat.is_le(SD.key_or(sl, 0n), l) == True{} : Bool}, +gT: {G.Good(c0, se, Some{s}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool},
  +eti: {ti == True{} : Bool}, +etx: {tx == False{} : Bool}) ->
  {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{s}, se, sl, Nil{}, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}} : R.RunSt}:
  +es = Q.str_eq_sound(s, c0, esame)
  %Equal.sym(String, s, c0, es) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{_}, se, sl, Nil{}, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}} : R.RunSt}
  %EL.cnt_zero(sk) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{c0}, se, sl, Nil{}, _, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}} : R.RunSt}
  %Q.s_append_nil(so) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{c0}, se, sl, Nil{}, SD.cnt_add(sk, R.Cnt{0n, 0n, 0n, 0n}), _, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}} : R.RunSt}
  +gls = Equal.trans(Bool, G.Good(c0, se, Some{s}, L.run.go(ls, fa, o, SD.rs0(c0, l))), G.Good(c0, se, Some{s}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), True{},
    Equal.cong(R.RunSt, Bool, st => G.Good(c0, se, Some{s}, st), L.run.go(ls, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT), gT)
  +iv = Equal.trans(Bool, Nat.is_le(S.lkey(sl), l), Nat.is_le(SD.key_or(sl, 0n), l), True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, l), S.lkey(sl), SD.key_or(sl, 0n), ET.lkey_ko(sl)), a10)
  +ep = EP.par(sn, sh, se, so, sk, sns, sl, c0, se, Some{s}, ls, fa, o, True{}, {==}, h1, esame, SD.rs0(c0, l), iv, gls)
  +el = Equal.cong(R.RunSt, R.RunSt, st => G.lift(sn, sh, se, so, sk, sns, sl, st), L.run.go(ls, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT)
  +ef = fin2(sn, sh, se, so, sk, sns, sl, True{}, sl, None{}, String.append(so, to), tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, eti, etx, {==}, {==})
  Equal.trans(R.RunSt, L.run.go(ls, fa, o, G.lift(sn, sh, se, so, sk, sns, sl, SD.rs0(c0, l))), G.lift(sn, sh, se, so, sk, sns, sl, L.run.go(ls, fa, o, SD.rs0(c0, l))), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}}, ep,
    Equal.trans(R.RunSt, G.lift(sn, sh, se, so, sk, sns, sl, L.run.go(ls, fa, o, SD.rs0(c0, l))), G.lift(sn, sh, se, so, sk, sns, sl, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(Nil{}), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(Nil{}), to)), sns, False{}}, el, ef))

# S's CHROM is c0 and its buffer E is not empty: phase 1 (drain).
def segx.s1(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +sh: String, +s: String, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +x0: R.Item, +t0: List<&2, R.Item>,
  +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool,
  +ls: List<&2, B.Line>, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt}, +h1: {R.has(c0, se) == False{} : Bool}, +esame: {R.is_cur(Some{s}, c0) == True{} : Bool},
  +a5: {Nat.is_lt(0n, tn) == True{} : Bool}, +a8: {SD.sorted(x0 <> t0) == True{} : Bool},
  +a9: {(List.is_empty(&2, R.Item, x0 <> t0) || SD.last_le(sl, SD.key_or(SD.first_item(x0 <> t0), 0n))) == True{} : Bool},
  +hml: {Nat.is_le(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), l) == True{} : Bool},
  +ab: {(Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && Nat.is_le(Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl)))))) == True{} : Bool}, +gT: {G.Good(c0, se, Some{s}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool},
  +eti: {ti == True{} : Bool}, +etx: {tx == False{} : Bool}) ->
  {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{s}, se, sl, x0 <> t0, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}} : R.RunSt}:
  +es = Q.str_eq_sound(s, c0, esame)
  %Equal.sym(String, s, c0, es) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{_}, se, sl, x0 <> t0, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}} : R.RunSt}
  %P.append_nil(R.Item, x0 <> t0) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{c0}, se, sl, _, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}} : R.RunSt}
  %EL.cnt_zero(sk) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, Some{c0}, se, sl, S.app(x0 <> t0, Nil{}), _, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}} : R.RunSt}
  +hle = ET.maxkey_all(x0 <> t0, SD.key_or(sl, 0n))
  +hq0 = Equal.trans(Bool, Nat.is_le(S.lkey(Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl)), l), Nat.is_le(S.lkey(SD.last_item(x0 <> t0)), l), True{},
    Equal.cong(Maybe<&2, R.Item>, Bool, m => Nat.is_le(S.lkey(m), l), Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), SD.last_item(x0 <> t0), E2.last_or_ne(x0 <> t0, sl, {==})),
    Q.le_trans(S.lkey(SD.last_item(x0 <> t0)), SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), l, ET.last_le_all(x0 <> t0, SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), hle, {==}), hml))
  +g1 = Equal.trans(Bool, G.Good1(c0, se, Some{s}, l, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), L.run.go(ls, fa, o, SD.rs0(c0, l))), G.Good1(c0, se, Some{s}, l, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), True{},
    Equal.cong(R.RunSt, Bool, st => G.Good1(c0, se, Some{s}, l, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), st), L.run.go(ls, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT),
    S.and_intro(G.Good(c0, se, Some{s}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), G.G1(l, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), gT, g1_conv(l, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, a5, ab)))
  +ed = ED.drain(sn, sh, sk, sns, c0, se, Some{s}, l, SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), String.append(so, SD.texts(x0 <> t0)), Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), h1, esame, hml, hq0, ls, fa, o, 0n, "", Nil{}, R.Cnt{0n, 0n, 0n, 0n}, x0 <> t0, sl, so,
    {==}, ET.sorted_conv(x0 <> t0, sl, a8, a9), hle, {==}, {==}, {==}, S.or_true_r(Nat.is_lt(0n, Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)))), {==}, {==}, g1)
  +el = Equal.cong(R.RunSt, R.RunSt, st => G.lift(sn, sh, se, String.append(so, SD.texts(x0 <> t0)), sk, sns, Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), st), L.run.go(ls, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT)
  +ef = fin2(sn, sh, se, String.append(so, SD.texts(x0 <> t0)), sk, sns, Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), True{}, sl, SD.last_item(x0 <> t0), String.append(so, String.append(SD.texts(x0 <> t0), to)), tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, eti, etx, {==},
    Q.s_append_assoc(so, SD.texts(x0 <> t0), to))
  Equal.trans(R.RunSt, L.run.go(ls, fa, o, R.RunSt{Nat.add(0n, sn), True{}, sh, Some{c0}, se, sl, S.app(x0 <> t0, SD.items_shift(sn, Nil{})), SD.cnt_add(sk, R.Cnt{0n, 0n, 0n, 0n}), so, sns, False{}}), G.lift(sn, sh, se, String.append(so, SD.texts(x0 <> t0)), sk, sns, Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), L.run.go(ls, fa, o, SD.rs0(c0, l))), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}}, ed,
    Equal.trans(R.RunSt, G.lift(sn, sh, se, String.append(so, SD.texts(x0 <> t0)), sk, sns, Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), L.run.go(ls, fa, o, SD.rs0(c0, l))), G.lift(sn, sh, se, String.append(so, SD.texts(x0 <> t0)), sk, sns, Maybe.or(&2, R.Item, SD.last_item(x0 <> t0), sl), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(Some{s}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(x0 <> t0), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(x0 <> t0), to)), sns, False{}}, el, ef))

def segx.same(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool, +ls: List<&2, B.Line>, +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt},
  +h1: {R.has(c0, se) == False{} : Bool}, +a5: {Nat.is_lt(0n, tn) == True{} : Bool}, +a8: {SD.sorted(sb) == True{} : Bool},
  +a9: {(List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n))) == True{} : Bool}, +gT: {G.Good(c0, se, sc, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool},
  +eti: {ti == True{} : Bool}, +etx: {tx == False{} : Bool}, +same: Bool, +esame: {R.is_cur(sc, c0) == same : Bool},
  +a10: {(Bool.not(same) || (Nat.is_le(SD.maxkey(sb, SD.key_or(sl, 0n)), l) && (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, sb) || Nat.is_le(Nat.add(SD.maxkey(sb, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))))) == True{} : Bool}) ->
  {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))), SD.last_shift(tl, same, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}:
  match sc sb same:
    case _ _ False{}:
      segx.ns(fa, o, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, ls, hc, eT, h1, esame, a8, a9, gT, eti, etx)
    case None{} _ True{}:
      Empty.absurd({L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, None{}, se, sl, sb, sk, so, sns, False{}}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, True{}, se, R.push_cur(None{}, se))), SD.last_shift(tl, True{}, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}, P.false_ne_true(esame))
    case Some{+s} Nil{} True{}:
      segx.s0(fa, o, c0, l, sn, sh, s, se, sl, sk, so, sns, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, ls, eT, h1, esame, P.and_true_l(Nat.is_le(SD.maxkey(Nil{}, SD.key_or(sl, 0n)), l), (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, Nil{}) || Nat.is_le(Nat.add(SD.maxkey(Nil{}, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))), a10), gT, eti, etx)
    case Some{+s} +x0 <> +t0 True{}:
      segx.s1(fa, o, c0, l, sn, sh, s, se, sl, x0, t0, sk, so, sns, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, ls, eT, h1, esame, a5, a8, a9,
        P.and_true_l(Nat.is_le(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), l), (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, x0 <> t0) || Nat.is_le(Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))), a10), P.and_true_r(Nat.is_le(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), l), (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, x0 <> t0) || Nat.is_le(Nat.add(SD.maxkey(x0 <> t0, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))), a10), gT, eti, etx)

def segx.f(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +sn: Nat, +si: Bool, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>,
  +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +sx: Bool, +tn: Nat, +ti: Bool, +th: String, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tk: R.Cnt, +to: String, +tns: List<&2, B.Note>, +tx: Bool,
  +ls: List<&2, B.Line>, +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx} : R.RunSt},
  +hk: {SD.segok(R.Opts.w(o), c0, l, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sx}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) == True{} : Bool}) ->
  {L.run.go(ls, fa, o, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sx}) == SD.shiftS(c0, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sx}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}) : R.RunSt}:
  +a10 = P.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb)), (List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n)))), (Bool.not(R.is_cur(sc, c0)) || (Nat.is_le(SD.maxkey(sb, SD.key_or(sl, 0n)), l) && (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, sb) || Nat.is_le(Nat.add(SD.maxkey(sb, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))))), hk)
  +c9 = P.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb)), (List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n)))), (Bool.not(R.is_cur(sc, c0)) || (Nat.is_le(SD.maxkey(sb, SD.key_or(sl, 0n)), l) && (Bool.not(List.is_empty(&2, String, te)) || (SD.keys_ge(tb, l) && (List.is_empty(&2, R.Item, sb) || Nat.is_le(Nat.add(SD.maxkey(sb, SD.key_or(sl, 0n)), R.Opts.w(o)), SD.max_inpos(tb, Bool.pick(Nat, Bool.not(List.is_empty(&2, String, te)), 0n, SD.real_inpos(tl))))))))), hk)
  +a9 = P.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb)), (List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n))), c9)
  +c8 = P.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb)), (List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n))), c9)
  +a8 = P.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb), c8)
  +c7 = P.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)), SD.sorted(sb), c8)
  +a7 = P.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc), c7)
  +c6 = P.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se))), SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc), c7)
  +a6 = P.and_true_r(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se)), c6)
  +c5 = P.and_true_l(Bool.and(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn)), Bool.not(R.has(c0, se)), c6)
  +a5 = P.and_true_r(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn), c5)
  +c4 = P.and_true_l(Bool.and(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns)), Nat.is_lt(0n, tn), c5)
  +a4 = P.and_true_r(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns), c4)
  +c3 = P.and_true_l(Bool.and(Bool.and(si, Bool.not(sx)), Bool.not(tx)), List.is_empty(&2, B.Note, tns), c4)
  +a3 = P.and_true_r(Bool.and(si, Bool.not(sx)), Bool.not(tx), c3)
  +c2 = P.and_true_l(Bool.and(si, Bool.not(sx)), Bool.not(tx), c3)
  +a2 = P.and_true_r(si, Bool.not(sx), c2)
  +c1 = P.and_true_l(si, Bool.not(sx), c2)
  +a1 = c1
  %Equal.sym(Bool, si, True{}, a1) : {L.run.go(ls, fa, o, R.RunSt{sn, _, sh, sc, se, sl, sb, sk, so, sns, sx}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, R.push_cur(sc, se))), SD.last_shift(tl, R.is_cur(sc, c0), sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}
  %Equal.sym(Bool, sx, False{}, P.not_true(sx, a2)) : {L.run.go(ls, fa, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, _}) == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, R.is_cur(sc, c0), se, R.push_cur(sc, se))), SD.last_shift(tl, R.is_cur(sc, c0), sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}} : R.RunSt}
  +eti = Equal.trans(Bool, ti, R.RunSt.inbody(L.run.go(ls, fa, o, SD.rs0(c0, l))), True{},
    Equal.sym(Bool, R.RunSt.inbody(L.run.go(ls, fa, o, SD.rs0(c0, l))), ti, Equal.cong(R.RunSt, Bool, st => R.RunSt.inbody(st), L.run.go(ls, fa, o, SD.rs0(c0, l)), R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}, eT)),
    ET.ib_go(ls, fa, o, SD.rs0(c0, l), {==}))
  +chs = SD.chroms_ok(List.append(&2, String, SD.cur_list(tc), te), c0, se, sc)
  +gT = S.and_intro(Bool.not(tx), G.M(c0, se, sc, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, tx}), a3, S.and_intro(List.is_empty(&2, B.Note, tns), chs, a4, a7))
  segx.same(fa, o, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, ls, hc, eT, P.not_true(R.has(c0, se), a6), a5, a8, a9, gT, eti, P.not_true(tx, a3), R.is_cur(sc, c0), {==}, a10)

def segx.t(+fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +st: R.RunSt, +ls: List<&2, B.Line>,
  +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}, +t: R.RunSt, +eT: {L.run.go(ls, fa, o, SD.rs0(c0, l)) == t : R.RunSt},
  +hk: {SD.segok(R.Opts.w(o), c0, l, st, t) == True{} : Bool}) ->
  {L.run.go(ls, fa, o, st) == SD.shiftS(c0, st, t) : R.RunSt}:
  match st t:
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +tx}:
      segx.f(fa, o, c0, l, sn, si, sh, sc, se, sl, sb, sk, so, sns, sx, tn, ti, th, tc, te, tl, tb, tk, to, tns, tx, ls, hc, eT, hk)

# The segment lemma, exactly (no settle needed).
law segx:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +st: R.RunSt
  for +ls: List<&2, B.Line>
  for +hc: {SD.first_chrom(ls) == Some{c0} : Maybe<&2, String>}
  for +hk: {SD.segok(R.Opts.w(o), c0, l, st, L.run.go(ls, fa, o, SD.rs0(c0, l))) == True{} : Bool}
  {L.run.go(ls, fa, o, st) == SD.shiftS(c0, st, L.run.go(ls, fa, o, SD.rs0(c0, l))) : R.RunSt}

def segx(fa, o, c0, l, st, ls, hc, hk):
  segx.t(fa, o, c0, l, st, ls, hc, L.run.go(ls, fa, o, SD.rs0(c0, l)), {==}, hk)
