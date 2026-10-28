import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as ST
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G
import ./proof_e_seg_lem.bend as EL
import ./proof_e_seg_lem2.bend as E2
import ./proof_e_seg_mono.bend as EM
import ./proof_e_seg_par.bend as EP

# Phase E, area "seg", phase 1: T's first CHROM is S's (c0) and S's buffer E
# is not all written yet. The true run's buffer is (E not written) ++ T's
# (moved), T's last is the phantom and T wrote nothing. When E is all
# written, phase 2 (proof_e_seg_par.bend) takes over; at the end E cannot be
# left (segok's mlow).

# What X wrote, once E is written: P0 then Y's.
law out_eq:
  for +px: String
  for +e: List<&2, R.Item>
  for +o2: String
  for +p0: String
  for +hP: {String.append(px, SD.texts(e)) == p0 : String}
  {String.append(px, String.append(L.texts(e), o2)) == String.append(p0, o2) : String}

def out_eq(px, e, o2, p0, hP):
  %Q.s_append_assoc(px, L.texts(e), o2) : {_ == String.append(p0, o2) : String}
  %EL.texts_eq(e) : {String.append(String.append(px, _), o2) == String.append(p0, o2) : String}
  %hP : {String.append(String.append(px, SD.texts(e)), o2) == String.append(_, o2) : String}
  {==}

# What X wrote, E partly written.
law hp_step:
  for +px: String
  for +te: List<&2, R.Item>
  for +de: List<&2, R.Item>
  for +e: List<&2, R.Item>
  for +p0: String
  for +etd: {S.app(te, de) == e : List<&2, R.Item>}
  for +hP: {String.append(px, SD.texts(e)) == p0 : String}
  {String.append(String.append(px, L.texts(te)), SD.texts(de)) == p0 : String}

def hp_step(px, te, de, e, p0, etd, hP):
  %Equal.sym(String, String.append(String.append(px, L.texts(te)), SD.texts(de)), String.append(px, String.append(L.texts(te), SD.texts(de))), Q.s_append_assoc(px, L.texts(te), SD.texts(de))) : {_ == p0 : String}
  %Equal.sym(String, SD.texts(de), L.texts(de), EL.texts_eq(de)) : {String.append(px, String.append(L.texts(te), _)) == p0 : String}
  %S.texts_app(te, de) : {String.append(px, _) == p0 : String}
  %Equal.sym(List<&2, R.Item>, S.app(te, de), e, etd) : {String.append(px, L.texts(_)) == p0 : String}
  %EL.texts_eq(e) : {String.append(px, _) == p0 : String}
  hP

# What X wrote last, E partly written.
law hq_step:
  for +te: List<&2, R.Item>
  for +de: List<&2, R.Item>
  for +e: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +q0: Maybe<&2, R.Item>
  for +etd: {S.app(te, de) == e : List<&2, R.Item>}
  for +hde: {List.is_empty(&2, R.Item, de) == False{} : Bool}
  for +he: {List.is_empty(&2, R.Item, e) == False{} : Bool}
  for +hQ: {Maybe.or(&2, R.Item, SD.last_item(e), q) == q0 : Maybe<&2, R.Item>}
  {Maybe.or(&2, R.Item, SD.last_item(de), S.flast(te, q)) == q0 : Maybe<&2, R.Item>}

def hq_step(te, de, e, q, q0, etd, hde, he, hQ):
  %Equal.sym(Maybe<&2, R.Item>, Maybe.or(&2, R.Item, SD.last_item(de), S.flast(te, q)), SD.last_item(de), E2.last_or_ne(de, S.flast(te, q), hde)) : {_ == q0 : Maybe<&2, R.Item>}
  %E2.last_app_ne(te, de, hde) : {_ == q0 : Maybe<&2, R.Item>}
  %Equal.sym(List<&2, R.Item>, S.app(te, de), e, etd) : {SD.last_item(_) == q0 : Maybe<&2, R.Item>}
  %E2.last_or_ne(e, q, he) : {_ == q0 : Maybe<&2, R.Item>}
  hQ

# A key below l: T stops, or keeps it buffered in its first run.
law ds1_low:
  for +rest: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +c0: String
  for +l: Nat
  for +n: Nat
  for +h: String
  for +b: List<&2, R.Item>
  for +k2: R.Cnt
  for +w: Nat
  for +key: Nat
  for +inpos: Nat
  for +ln: Nat
  for +ch: String
  for +ps: String
  for +text: String
  for +hkb: {SD.keys_ge(b, l) == True{} : Bool}
  for +hv: {Nat.is_le(l, key) == False{} : Bool}
  {G.Bad(l, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}

def ds1_low(rest, fa, op, c0, l, n, h, b, k2, w, key, inpos, ln, ch, ps, text, hkb, hv):
  +ity = {R.Item{key, inpos, B.At{ln, ch, ps}, text} : R.Item}
  %Equal.sym(List<&2, R.Item>, R.insert(ity, b), ity <> b, E2.ins_front(ity, b, l, hkb, hv)) :
    {G.Bad(l, L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(w, inpos, _), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}),
      R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(w, inpos, _), B.At{ln, ch, ps}))) == True{} : Bool}
  EM.doom.rd(rest, fa, op, c0, l, n, h, k2, "", Nil{}, w, inpos, B.At{ln, ch, ps}, ity, b, R.ready(w, inpos, ity), hv,
    n2 => h2 => k3 => out2 => ns2 => y0 => t2 => hy0 => EM.doom(rest, fa, op, c0, l, n2, h2, k3, out2, ns2, y0, t2, hy0))

law emit1_eq:
  for +d: Nat
  for +sh: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +c0: String
  for +se: List<&2, String>
  for +l: Nat
  for +P0: String
  for +Q0: Maybe<&2, R.Item>
  for +n: Nat
  for +h: String
  for +k2: R.Cnt
  for +q: Maybe<&2, R.Item>
  for +Px: String
  for +E: List<&2, R.Item>
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +dr: List<&2, R.Item>
  for +atX: B.At
  for +atY: B.At
  for +F: R.Flush
  for +rest: List<&2, R.Item>
  for e3: {F == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush}
  for er: {rest == SD.items_shift(d, dr) : List<&2, R.Item>}
  for +hP: {String.append(Px, SD.texts(E)) == P0 : String}
  {R.emit.ready(F, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, rest, atX) == G.lift(d, sh, se, P0, sk, sns, Q0, R.emit.ready(R.Flushed{o2, l2}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, dr, atY)) : R.RunSt}

def emit1_eq(d, sh, sk, sns, c0, se, l, P0, Q0, n, h, k2, q, Px, E, o2, l2, dr, atX, atY, F, rest, e3, er, hP):
  %Equal.sym(R.Flush, F, R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)}, e3) :
    {R.emit.ready(_, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, rest, atX) == G.lift(d, sh, se, P0, sk, sns, Q0, R.emit.ready(R.Flushed{o2, l2}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, dr, atY)) : R.RunSt}
  %Equal.sym(List<&2, R.Item>, rest, SD.items_shift(d, dr), er) :
    {R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, G.img(Q0, l2, d), _, SD.cnt_add(sk, k2), String.append(Px, String.append(L.texts(E), o2)), sns, False{}}
      == G.lift(d, sh, se, P0, sk, sns, Q0, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, l2, dr, k2, String.append("", o2), Nil{}, False{}}) : R.RunSt}
  %out_eq(Px, E, o2, P0, hP) :
    {R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, G.img(Q0, l2, d), SD.items_shift(d, dr), SD.cnt_add(sk, k2), String.append(Px, String.append(L.texts(E), o2)), sns, False{}}
      == R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, G.img(Q0, l2, d), SD.items_shift(d, dr), SD.cnt_add(sk, k2), _, sns, False{}} : R.RunSt}
  {==}

# X writes E whole, then what Y writes from the phantom (E's last for it).
law fx_eq:
  for +d: Nat
  for +l: Nat
  for +c0: String
  for +Q0: Maybe<&2, R.Item>
  for +E: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}
  for +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}
  for +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}
  for +ha: {G.allreal(ys) == True{} : Bool}
  for +ef: {R.flush(ys, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}) == R.Flushed{o2, l2} : R.Flush}
  {R.flush(S.app(E, SD.items_shift(d, ys)), q) == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush}

def fx_eq(d, l, c0, Q0, E, ys, q, o2, l2, hs, hQ, hQ0, ha, ef):
  %Equal.sym(R.Flush, R.flush(S.app(E, SD.items_shift(d, ys)), q), R.Flush.pre(L.texts(E), R.flush(SD.items_shift(d, ys), S.flast(E, q))), E2.flush_app(E, SD.items_shift(d, ys), q, hs)) :
    {_ == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush}
  %Equal.sym(Maybe<&2, R.Item>, S.flast(E, q), Q0, Equal.trans(Maybe<&2, R.Item>, S.flast(E, q), Maybe.or(&2, R.Item, SD.last_item(E), q), Q0, E2.flast_or(E, q), hQ)) :
    {R.Flush.pre(L.texts(E), R.flush(SD.items_shift(d, ys), _)) == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush}
  %Equal.sym(R.Flush, R.flush(SD.items_shift(d, ys), Q0), R.Flushed{o2, G.img(Q0, l2, d)}, EP.fl2_eq(ys, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Q0, d, o2, l2, ha, hQ0, ef)) :
    {R.Flush.pre(L.texts(E), _) == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush}
  {==}

def ds1_all.f(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +k2: R.Cnt, +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String,
  +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +bx: List<&2, R.Item>, +b2: List<&2, R.Item>, f: R.Flush,
  +ef: {R.flush(R.take_ready(R.Opts.w(op), inpos, b2), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}) == f : R.Flush},
  +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hP: {String.append(Px, SD.texts(E)) == P0 : String},
  +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}, +hb2: {G.allreal(b2) == True{} : Bool},
  +ear: {S.all_ready(E, R.Opts.w(op), inpos) == True{} : Bool}, +ebx: {bx == S.app(E, SD.items_shift(d, b2)) : List<&2, R.Item>},
  hg: {G.Good(c0, se, sc, R.emit.ready(f, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, b2), B.At{ln, ch, ps})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(f, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, b2), B.At{ln, ch, ps}))) == True{} : Bool}) ->
  {L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, bx), q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, bx), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(f, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, b2), B.At{ln, ch, ps}))) : R.RunSt}:
  match f:
    case R.Broke{o3, bad, prev}:
      Empty.absurd({L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, bx), q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, bx), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(R.Broke{o3, bad, prev}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, b2), B.At{ln, ch, ps}))) : R.RunSt}, P.false_ne_true(hg))
    case R.Flushed{+o2, +l2}:
      +w = R.Opts.w(op)
      +tr2 = R.take_ready(w, inpos, b2)
      +htr = EL.allreal_tr(w, inpos, b2, hb2)
      +et = Equal.trans(List<&2, R.Item>, R.take_ready(w, inpos, bx), R.take_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), S.app(E, SD.items_shift(d, tr2)),
        Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.take_ready(w, inpos, xs), bx, S.app(E, SD.items_shift(d, b2)), ebx),
        Equal.trans(List<&2, R.Item>, R.take_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), S.app(E, R.take_ready(w, inpos, SD.items_shift(d, b2))), S.app(E, SD.items_shift(d, tr2)),
          E2.tr_app_ready(w, inpos, E, SD.items_shift(d, b2), ear),
          Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => S.app(E, xs), R.take_ready(w, inpos, SD.items_shift(d, b2)), SD.items_shift(d, tr2), EL.tr_sh(w, inpos, d, b2))))
      +e3 = Equal.trans(R.Flush, R.flush(R.take_ready(w, inpos, bx), q), R.flush(S.app(E, SD.items_shift(d, tr2)), q), R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)},
        Equal.cong(List<&2, R.Item>, R.Flush, xs => R.flush(xs, q), R.take_ready(w, inpos, bx), S.app(E, SD.items_shift(d, tr2)), et),
        fx_eq(d, l, c0, Q0, E, tr2, q, o2, l2, hs, hQ, hQ0, htr, ef))
      +er = Equal.trans(List<&2, R.Item>, R.drop_ready(w, inpos, bx), R.drop_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), SD.items_shift(d, R.drop_ready(w, inpos, b2)),
        Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.drop_ready(w, inpos, xs), bx, S.app(E, SD.items_shift(d, b2)), ebx),
        Equal.trans(List<&2, R.Item>, R.drop_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), R.drop_ready(w, inpos, SD.items_shift(d, b2)), SD.items_shift(d, R.drop_ready(w, inpos, b2)),
          E2.dr_app_ready(w, inpos, E, SD.items_shift(d, b2), ear), EL.dr_sh(w, inpos, d, b2)))
      +y2 = R.emit.ready(R.Flushed{o2, l2}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, b2), B.At{ln, ch, ps})
      +eqx = emit1_eq(d, sh, sk, sns, c0, se, l, P0, Q0, n, h, k2, q, Px, E, o2, l2, R.drop_ready(w, inpos, b2), B.At{Nat.add(ln, d), ch, ps}, B.At{ln, ch, ps},
        R.flush(R.take_ready(w, inpos, bx), q), R.drop_ready(w, inpos, bx), e3, er, hP)
      %Equal.sym(R.RunSt, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, bx), q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, bx), B.At{Nat.add(ln, d), ch, ps}), G.lift(d, sh, se, P0, sk, sns, Q0, y2), eqx) : {L.run.go(rest, fa, op, _) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, y2)) : R.RunSt}
      +iv = S.and_intro(G.allreal(R.drop_ready(w, inpos, b2)), G.qok(Q0, l2), EL.allreal_dr(w, inpos, b2, hb2), EP.qok_l2(tr2, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Q0, o2, l2, htr, hQ0, ef))
      +gd = P.and_true_l(G.Good(c0, se, sc, L.run.go(rest, fa, op, y2)), G.G1(l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, y2)), hg1)
      EP.par(d, sh, se, P0, sk, sns, Q0, c0, se, sc, rest, fa, op, True{}, {==}, h1, h2, y2, iv, gd)

# The induction hypothesis of drain, for any phase 1 state on the rest.
def DrainIH(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts) -> Type:
  @n: Nat -> @h: String -> @b: List<&2, R.Item> -> @k: R.Cnt -> @E: List<&2, R.Item> -> @q: Maybe<&2, R.Item> -> @Px: String ->
    {List.is_empty(&2, R.Item, E) == False{} : Bool} -> {S.sorted_from(E, S.lkey(q)) == True{} : Bool} -> {S.all_le(E, mx) == True{} : Bool} -> {SD.keys_ge(b, l) == True{} : Bool} -> {G.allreal(b) == True{} : Bool} -> {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool} -> {(Nat.is_lt(0n, Nat.add(mx, R.Opts.w(op))) || Nat.is_eq(n, 0n)) == True{} : Bool} -> {String.append(Px, SD.texts(E)) == P0 : String} -> {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>} -> {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}})) == True{} : Bool} ->
    {L.run.go(rest, fa, op, R.RunSt{Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}})) : R.RunSt}

# E not all ready: X writes a prefix of E, Y nothing (its keys are at
# least l, so not ready either); phase 1 goes on.
def ds1_part(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String,
  +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hb2: {G.allreal(R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)) == True{} : Bool}, +hkb2: {SD.keys_ge(R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), l) == True{} : Bool},
  +ear: {S.all_ready(E, R.Opts.w(op), inpos) == False{} : Bool}, +ebx: {R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b))) == S.app(E, SD.items_shift(d, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b))) : List<&2, R.Item>},
  hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}))) == True{} : Bool}, ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}))) : R.RunSt}:
  +w = R.Opts.w(op)
  +ity = {R.Item{key, inpos, B.At{ln, ch, ps}, text} : R.Item}
  +b2 = R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)
  +bx = R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))
  +te = R.take_ready(w, inpos, E)
  +de = R.drop_ready(w, inpos, E)
  +etd = S.take_drop(w, inpos, E)
  +s2 = Equal.trans(Bool, S.sorted_from(S.app(te, de), S.lkey(q)), S.sorted_from(E, S.lkey(q)), True{},
    Equal.cong(List<&2, R.Item>, Bool, xs => S.sorted_from(xs, S.lkey(q)), S.app(te, de), E, etd), hs)
  +efe = S.flush_sorted(te, q, S.sorted_prefix(te, de, S.lkey(q), s2))
  +etx = Equal.trans(List<&2, R.Item>, R.take_ready(w, inpos, bx), R.take_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), te,
    Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.take_ready(w, inpos, xs), bx, S.app(E, SD.items_shift(d, b2)), ebx),
    E2.tr_app_nr(w, inpos, E, SD.items_shift(d, b2), ear))
  +edx = Equal.trans(List<&2, R.Item>, R.drop_ready(w, inpos, bx), R.drop_ready(w, inpos, S.app(E, SD.items_shift(d, b2))), S.app(de, SD.items_shift(d, b2)),
    Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.drop_ready(w, inpos, xs), bx, S.app(E, SD.items_shift(d, b2)), ebx),
    E2.dr_app_nr(w, inpos, E, SD.items_shift(d, b2), ear))
  +nb = E2.nr_bound(w, inpos, E, mx, ear, hle)
  +hr = E2.hr_false(w, inpos, b2, mx, l, nb, hml, hkb2)
  +ety = E2.tr_nil(w, inpos, b2, hr)
  +edy = E2.dr_self(w, inpos, b2, hr)
  +ey = Equal.trans(R.RunSt, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}), R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}), R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}),
    Equal.cong(List<&2, R.Item>, R.RunSt, t => R.emit.ready(R.flush(t, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(w, inpos, b2), B.At{ln, ch, ps}), R.take_ready(w, inpos, b2), Nil{}, ety),
    Equal.cong(List<&2, R.Item>, R.RunSt, dd => R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, dd, B.At{ln, ch, ps}), R.drop_ready(w, inpos, b2), b2, edy))
  +hg2 = Equal.trans(Bool, G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}))), G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}))), True{},
    Equal.sym(Bool, G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}))), G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}))),
      Equal.cong(R.RunSt, Bool, s => G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, s)), R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}), R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}), ey)), hg1)
  %Equal.sym(R.RunSt, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), B.At{ln, ch, ps}), R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}), ey) : {L.run.go(rest, fa, op, R.emit.ready(R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, _)) : R.RunSt}
  %Equal.sym(List<&2, R.Item>, R.take_ready(w, inpos, bx), te, etx) :
    {L.run.go(rest, fa, op, R.emit.ready(R.flush(_, q), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}))) : R.RunSt}
  %Equal.sym(R.Flush, R.flush(te, q), R.Flushed{L.texts(te), S.flast(te, q)}, efe) :
    {L.run.go(rest, fa, op, R.emit.ready(_, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, R.drop_ready(R.Opts.w(op), inpos, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b)))), B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}))) : R.RunSt}
  %Equal.sym(List<&2, R.Item>, R.drop_ready(w, inpos, bx), S.app(de, SD.items_shift(d, b2)), edx) :
    {L.run.go(rest, fa, op, R.emit.ready(R.Flushed{L.texts(te), S.flast(te, q)}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, Nil{}, SD.cnt_add(sk, k2), Px, sns, False{}}, _, B.At{Nat.add(ln, d), ch, ps})) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.emit.ready(R.flush(Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), B.At{ln, ch, ps}))) : R.RunSt}
  +hde = E2.de_ne(w, inpos, E, ear)
  +hinp = E2.lt_of_le_false(Nat.add(mx, w), inpos, nb)
  ih(1n+n, h, b2, k2, de, S.flast(te, q), String.append(Px, L.texts(te)),
    hde, S.sorted_rest(te, de, q, s2),
    E2.all_le_r(te, de, mx, Equal.trans(Bool, S.all_le(S.app(te, de), mx), S.all_le(E, mx), True{},
      Equal.cong(List<&2, R.Item>, Bool, xs => S.all_le(xs, mx), S.app(te, de), E, etd), hle)),
    hkb2, hb2, EL.alt_ins(ity, b, Nat.add(mx, R.Opts.w(op)), hinp, hK),
    S.or_true_l(Nat.is_lt(0n, Nat.add(mx, R.Opts.w(op))), Nat.is_eq(1n+n, 0n), E2.lt_pos(inpos, Nat.add(mx, R.Opts.w(op)), hinp)),
    hp_step(Px, te, de, E, P0, etd, hP), hq_step(te, de, E, q, Q0, etd, hde, hE, hQ), hg2)

def ds1.ar(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hkb: {SD.keys_ge(b, l) == True{} : Bool}, +hb: {G.allreal(b) == True{} : Bool}, +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}, +hv: {Nat.is_le(l, key) == True{} : Bool},
  +ebx: {R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b))) == S.app(E, SD.items_shift(d, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b))) : List<&2, R.Item>}, +ar: Bool, +ear: {S.all_ready(E, R.Opts.w(op), inpos) == ar : Bool},
  hg: {G.Good(c0, se, sc, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}, ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}:
  match ar:
    case True{}:
      ds1_all.f(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, k2, E, q, Px, inpos, ln, ch, ps, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b))), R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b), R.flush(R.take_ready(R.Opts.w(op), inpos, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), {==},
        hs, hP, hQ, EL.allreal_ins(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b, hit, hb), ear, ebx, hg, hg1)
    case False{}:
      ds1_part(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hP, hQ, hK, EL.allreal_ins(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b, hit, hb), EL.kge_ins(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b, l, hv, hkb), ear, ebx, hg1, ih)

def ds1.v(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hkb: {SD.keys_ge(b, l) == True{} : Bool}, +hb: {G.allreal(b) == True{} : Bool}, +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}, +v: Bool, +ev: {Nat.is_le(l, key) == v : Bool},
  hg: {G.Good(c0, se, sc, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}, ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}:
  match v:
    case False{}:
      +nb = E2.good1_notbad(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})), hg1)
      +bd = ds1_low(rest, fa, op, c0, l, n, h, b, k2, R.Opts.w(op), key, inpos, ln, ch, ps, text, hkb, ev)
      Empty.absurd({L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}, P.true_ne_false(Equal.trans(Bool, True{}, G.Bad(l, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))), False{},
        Equal.sym(Bool, G.Bad(l, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))), True{}, bd), nb)))
    case True{}:
      +ity = {R.Item{key, inpos, B.At{ln, ch, ps}, text} : R.Item}
      +hle2 = S.all_le_mono(E, mx, key, hle, Q.le_trans(mx, l, key, hml, ev))
      +ebx = Equal.trans(List<&2, R.Item>, R.insert(SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), S.app(E, SD.items_shift(d, b))), S.app(E, R.insert(SD.item_shift(d, ity), SD.items_shift(d, b))), S.app(E, SD.items_shift(d, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b))),
        S.insert_app(SD.item_shift(d, ity), E, SD.items_shift(d, b), hle2),
        Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => S.app(E, xs), R.insert(SD.item_shift(d, ity), SD.items_shift(d, b)), SD.items_shift(d, R.insert(R.Item{key, inpos, B.At{ln, ch, ps}, text}, b)), EL.ins_sh(d, ity, b)))
      ds1.ar(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hkb, hb, hK, hP, hQ, hit, ev, ebx, S.all_ready(E, R.Opts.w(op), inpos), {==}, hg, hg1, ih)

# A line in c0 (same_run), phase 1.
law ds1:
  for +d: Nat
  for +sh: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +l: Nat
  for +mx: Nat
  for +P0: String
  for +Q0: Maybe<&2, R.Item>
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == True{} : Bool}
  for +hml: {Nat.is_le(mx, l) == True{} : Bool}
  for +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}
  for +rest: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +n: Nat
  for +h: String
  for +b: List<&2, R.Item>
  for +k2: R.Cnt
  for +E: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +Px: String
  for +key: Nat
  for +inpos: Nat
  for +ln: Nat
  for +ch: String
  for +ps: String
  for +text: String
  for +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}
  for +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}
  for +hle: {S.all_le(E, mx) == True{} : Bool}
  for +hkb: {SD.keys_ge(b, l) == True{} : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool}
  for +hP: {String.append(Px, SD.texts(E)) == P0 : String}
  for +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}
  for +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}
  for hg: {G.Good(c0, se, sc, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}
  for hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}
  for ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)
  {L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}

def ds1(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hkb, hb, hK, hP, hQ, hit, hg, hg1, ih):
  ds1.v(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hkb, hb, hK, hP, hQ, hit, Nat.is_le(l, key), {==}, hg, hg1, ih)

def dn1.k(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +o2: String, +l2: Maybe<&2, R.Item>, +hP: {String.append(Px, SD.texts(E)) == P0 : String},
  +e3: {R.flush(S.app(E, SD.items_shift(d, b)), q) == R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)} : R.Flush},
  +eh: {R.has(ch, se) == False{} : Bool},
  pr: {R.same_run(R.RunSt{Nat.add(1n+n, d), True{}, sh, Some{ch}, List.append(&2, String, R.push_cur(Some{c0}, Nil{}), se), G.img(Q0, None{}, d), SD.items_shift(d, Nil{}), SD.cnt_add(sk, k2), String.append(P0, String.append("", o2)), sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, se, P0, sk, sns, Q0, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(Q0, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}) ->
  {L.run.go(rest, fa, op, R.new_run.go(R.flush(S.app(E, SD.items_shift(d, b)), q), R.has(ch, se), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}:
  match pr:
    case (e1, iv):
      %Equal.sym(R.Flush, R.flush(S.app(E, SD.items_shift(d, b)), q), R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)}, e3) :
        {L.run.go(rest, fa, op, R.new_run.go(_, R.has(ch, se), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}
      %Equal.sym(Bool, R.has(ch, se), False{}, eh) :
        {L.run.go(rest, fa, op, R.new_run.go(R.Flushed{String.append(L.texts(E), o2), G.img(Q0, l2, d)}, _, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}
      %Equal.sym(String, String.append(Px, String.append(L.texts(E), o2)), String.append(P0, o2), out_eq(Px, E, o2, P0, hP)) :
        {L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{ch}, R.push_cur(Some{c0}, se), None{}, Nil{}, SD.cnt_add(sk, k2), _, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}
      %Equal.sym(R.RunSt, R.same_run(R.RunSt{Nat.add(1n+n, d), True{}, sh, Some{ch}, List.append(&2, String, R.push_cur(Some{c0}, Nil{}), se), G.img(Q0, None{}, d), SD.items_shift(d, Nil{}), SD.cnt_add(sk, k2), String.append(P0, String.append("", o2)), sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})), G.lift(d, sh, se, P0, sk, sns, Q0, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})), e1) :
        {L.run.go(rest, fa, op, _) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}
      +gd = P.and_true_l(G.Good(c0, se, sc, L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))), G.G1(l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))), hg1)
      EP.par(d, sh, se, P0, sk, sns, Q0, c0, se, sc, rest, fa, op, True{}, {==}, h1, h2, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}), iv, gd)

# A line that leaves c0 (new_run), phase 1: X writes E, then both start the
# same new CHROM run; phase 2 takes over.
def dn1.f(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +hb: {G.allreal(b) == True{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}, +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}, f: R.Flush, +ef: {R.flush(b, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}) == f : R.Flush},
  +hg: {G.Good(c0, se, sc, R.new_run.go(f, False{}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.new_run.go(f, False{}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool}) ->
  {L.run.go(rest, fa, op, R.new_run.go(R.flush(S.app(E, SD.items_shift(d, b)), q), R.has(ch, se), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.new_run.go(f, False{}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}:
  match f:
    case R.Broke{o3, bad, prev}:
      Empty.absurd({L.run.go(rest, fa, op, R.new_run.go(R.flush(S.app(E, SD.items_shift(d, b)), q), R.has(ch, se), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.new_run.go(R.Broke{o3, bad, prev}, False{}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}, P.false_ne_true(hg))
    case R.Flushed{+o2, +l2}:
      +e3 = fx_eq(d, l, c0, Q0, E, b, q, o2, l2, hs, hQ, hQ0, hb, ef)
      +hm = P.and_true_r(Bool.not(G.halt(R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}))), G.M(c0, se, sc, R.same_run(R.RunSt{1n+n, True{}, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text})), hg)
      +cond = EM.nr_cond(c0, se, sc, 1n+n, True{}, h, ch, Some{c0}, Nil{}, k2, String.append("", o2), Nil{}, False{}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}, hm)
      +eh = EP.zfree(ch, c0, se, sc, True{}, se, {==}, h1, h2, cond)
      dn1.k(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, o2, l2, hP, e3, eh,
        EP.sr2(d, sh, se, P0, sk, sns, Q0, c0, se, sc, 1n+n, h, Some{ch}, R.push_cur(Some{c0}, Nil{}), None{}, Nil{}, k2, String.append("", o2), R.Opts.w(op), key, inpos, ln, ch, ps, text, {==}, {==}, hit, hg),
        hg1)

def dk1.g(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hkb: {SD.keys_ge(b, l) == True{} : Bool}, +hb: {G.allreal(b) == True{} : Bool}, +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}, +g: Bool,
  +hg: {G.Good(c0, se, sc, R.keyed.go(g, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.keyed.go(g, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == True{} : Bool},
  ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.keyed.go(g, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, sns, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.keyed.go(g, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k2, "", Nil{}, False{}}, R.Opts.w(op), ch, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) : R.RunSt}:
  match g:
    case True{}:
      ds1(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hkb, hb, hK, hP, hQ, hit, hg, hg1, ih)
    case False{}:
      dn1.f(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hb, hs, hP, hQ, hit, R.flush(b, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}), {==}, hg, hg1)

def dk1(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +n: Nat, +h: String, +b: List<&2, R.Item>, +k: R.Cnt, +k2: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hkb: {SD.keys_ge(b, l) == True{} : Bool}, +hb: {G.allreal(b) == True{} : Bool}, +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool},
  +hg: {G.Good(c0, se, sc, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2))) == True{} : Bool}, ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, R.Opts.w(op), SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), Nil{}, SD.cnt_add(sk, k2))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2))) : R.RunSt}:
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, sns, Nil{}), sns, P.append_nil(B.Note, sns)) : {L.run.go(rest, fa, op, R.keyed.go(R.is_cur(Some{c0}, ch), R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k2), Px, _, False{}}, R.Opts.w(op), ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}))) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2))) : R.RunSt}
  dk1.g(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k2, E, q, Px, key, inpos, ln, ch, ps, text, hE, hs, hle, hkb, hb, hK, hP, hQ, hit, R.is_cur(Some{c0}, ch), hg, hg1, ih)

def bl1.r(+d: Nat, +sh: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mx: Nat, +P0: String, +Q0: Maybe<&2, R.Item>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == True{} : Bool}, +hml: {Nat.is_le(mx, l) == True{} : Bool}, +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}, +rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +n: Nat, +h: String, +b: List<&2, R.Item>, +k: R.Cnt,
  +E: List<&2, R.Item>, +q: Maybe<&2, R.Item>, +Px: String, r: B.Res, +op: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat,
  +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}, +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}, +hle: {S.all_le(E, mx) == True{} : Bool},
  +hkb: {SD.keys_ge(b, l) == True{} : Bool}, +hb: {G.allreal(b) == True{} : Bool}, +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool},
  +hP: {String.append(Px, SD.texts(E)) == P0 : String}, +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>},
  +hg: {G.Good(c0, se, sc, R.body_line(r, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, hg1: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(rest, fa, op, R.body_line(r, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos))) == True{} : Bool}, ih: DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)) ->
  {L.run.go(rest, fa, op, R.body_line(r, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.body_line(r, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}:
  match r:
    case B.Res{B.Broken{}, k1, t, s}:
      Empty.absurd({L.run.go(rest, fa, op, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}, P.false_ne_true(hg))
    case B.Res{B.NoContig{}, k1, t, s}:
      Empty.absurd({L.run.go(rest, fa, op, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}, P.false_ne_true(hg))
    case B.Res{B.Problem{+cd}, k1, t, s}:
      match op:
        case B.Opts{+st, +w, +a}:
          match st:
            case True{}:
              Empty.absurd({L.run.go(rest, fa, B.Opts{True{}, w, a}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, B.Opts{True{}, w, a}, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, B.Opts{True{}, w, a}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, B.Opts{True{}, w, a}, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}, P.false_ne_true(hg))
            case False{}:
              Empty.absurd({L.run.go(rest, fa, B.Opts{False{}, w, a}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, B.Opts{False{}, w, a}, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, B.Opts{False{}, w, a}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, B.Opts{False{}, w, a}, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{}))), hg))))
    case B.Res{B.Skipped{}, k1, t, s}:
      %EL.cnt_bump(sk, k, False{}, True{}, False{}) : {L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{1n+Nat.add(n, d), f0, f1}, B.Line.text(li)}, Nil{}, _)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(k, False{}, True{}, False{})))) : R.RunSt}
      dk1(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k, R.bump(k, False{}, True{}, False{}), E, q, Px, pos, pos, 1n+n, f0, f1, B.Line.text(li), hE, hs, hle, hkb, hb, hK, hP, hQ, {==}, hg, hg1, ih)
    case B.Res{B.Normalized{}, +k1, +t, +s}:
      match s:
        case True{}:
          Empty.absurd({L.run.go(rest, fa, op, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos))) : R.RunSt}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))), hg))))
        case False{}:
          %EL.cnt_bump(sk, k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}) : {L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+Nat.add(n, d), f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, _)) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(rest, fa, op, R.keyed(R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{})))) : R.RunSt}
          dk1(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n, h, b, k, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), E, q, Px, k1, pos, 1n+n, f0, f1, String.append(t, B.Line.term(li)), hE, hs, hle, hkb, hb, hK, hP, hQ, {==}, hg, hg1, ih)

# At the end of the lines in phase 1: segok's mlow is refused (every Y item
# came while E was not all ready, so below max(E) + w).
law dend:
  for +d: Nat
  for +sh: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +l: Nat
  for +mx: Nat
  for +P0: String
  for +Q0: Maybe<&2, R.Item>
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == True{} : Bool}
  for +hml: {Nat.is_le(mx, l) == True{} : Bool}
  for +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +n: Nat
  for +h: String
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +E: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +Px: String
  for +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}
  for +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}
  for +hle: {S.all_le(E, mx) == True{} : Bool}
  for +hkb: {SD.keys_ge(b, l) == True{} : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool}
  for +hK0: {(Nat.is_lt(0n, Nat.add(mx, R.Opts.w(op))) || Nat.is_eq(n, 0n)) == True{} : Bool}
  for +hP: {String.append(Px, SD.texts(E)) == P0 : String}
  for +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}
  for +hg: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}) == True{} : Bool}
  {R.RunSt{Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}} == G.lift(d, sh, se, P0, sk, sns, Q0, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}) : R.RunSt}

def dend(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, fa, op, n, h, b, k, E, q, Px, hE, hs, hle, hkb, hb, hK, hK0, hP, hQ, hg):
  +mb = Nat.add(mx, R.Opts.w(op))
  +lb = Nat.is_le(mb, SD.max_inpos(b, 0n))
  +g1 = P.and_true_r(G.Good(c0, se, sc, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}), G.G1(l, Nat.add(mx, R.Opts.w(op)), R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}), hg)
  +g2 = P.and_true_r(Nat.is_lt(0n, n), Bool.and(SD.keys_ge(b, l), lb), g1)
  +n0 = P.and_true_l(Nat.is_lt(0n, n), Bool.and(SD.keys_ge(b, l), lb), g1)
  +le = P.and_true_r(SD.keys_ge(b, l), lb, g2)
  +mbp = E2.or_l_true(Nat.is_lt(0n, mb), Nat.is_eq(n, 0n), hK0, E2.eq0_false(n, n0))
  Empty.absurd({R.RunSt{Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}} == G.lift(d, sh, se, P0, sk, sns, Q0, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}) : R.RunSt}, E2.le_lt_absurd(mb, SD.max_inpos(b, 0n), le, E2.max_inpos_lt(b, 0n, mb, hK, mbp)))

# Phase 1: S's CHROM is c0 and E (S's buffer not written yet) is not empty.
law drain:
  for +d: Nat
  for +sh: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +l: Nat
  for +mx: Nat
  for +P0: String
  for +Q0: Maybe<&2, R.Item>
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == True{} : Bool}
  for +hml: {Nat.is_le(mx, l) == True{} : Bool}
  for +hQ0: {Nat.is_le(S.lkey(Q0), l) == True{} : Bool}
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +n: Nat
  for +h: String
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +E: List<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +Px: String
  for +hE: {List.is_empty(&2, R.Item, E) == False{} : Bool}
  for +hs: {S.sorted_from(E, S.lkey(q)) == True{} : Bool}
  for +hle: {S.all_le(E, mx) == True{} : Bool}
  for +hkb: {SD.keys_ge(b, l) == True{} : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hK: {G.all_lt(b, Nat.add(mx, R.Opts.w(op))) == True{} : Bool}
  for +hK0: {(Nat.is_lt(0n, Nat.add(mx, R.Opts.w(op))) || Nat.is_eq(n, 0n)) == True{} : Bool}
  for +hP: {String.append(Px, SD.texts(E)) == P0 : String}
  for +hQ: {Maybe.or(&2, R.Item, SD.last_item(E), q) == Q0 : Maybe<&2, R.Item>}
  for +hg: {G.Good1(c0, se, sc, l, Nat.add(mx, R.Opts.w(op)), L.run.go(ls, fa, op, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}})) == True{} : Bool}
  {L.run.go(ls, fa, op, R.RunSt{Nat.add(n, d), True{}, sh, Some{c0}, se, q, S.app(E, SD.items_shift(d, b)), SD.cnt_add(sk, k), Px, sns, False{}}) == G.lift(d, sh, se, P0, sk, sns, Q0, L.run.go(ls, fa, op, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}})) : R.RunSt}

def drain(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, ls, fa, op, n, h, b, k, E, q, Px, hE, hs, hle, hkb, hb, hK, hK0, hP, hQ, hg):
  match ls:
    case Nil{}:
      dend(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, fa, op, n, h, b, k, E, q, Px, hE, hs, hle, hkb, hb, hK, hK0, hP, hQ, hg)
    case +li <> +rest:
      +y1 = L.line_step(fa, op, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, b, k, "", Nil{}, False{}}, li)
      +fin = L.run.go(rest, fa, op, y1)
      +hgood = EM.good_back(c0, se, sc, rest, fa, op, y1, P.and_true_l(G.Good(c0, se, sc, fin), G.G1(l, Nat.add(mx, R.Opts.w(op)), fin), hg))
      +fs = B.Rec.fields(B.Line.body(li))
      ih = {(n2 => hx2 => b2 => k2 => ee => qq => px2 => a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => g2 =>
        drain(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op, n2, hx2, b2, k2, ee, qq, px2, a1, a2, a3, a4, a5, a6, a7, a8, a9, g2)) : DrainIH(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, op)}
      bl1.r(d, sh, sk, sns, c0, se, sc, l, mx, P0, Q0, h1, h2, hml, hQ0, rest, fa, n, h, b, k, E, q, Px, L.judge(fa, B.Line.body(li)), op, li, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.pos(fs),
        hE, hs, hle, hkb, hb, hK, hP, hQ, hgood, hg, ih)
