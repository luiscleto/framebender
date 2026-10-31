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
import ./proof_e_seg_mono.bend as EM

# Phase E, area "seg", phase 2: once S's buffer is written, the true run X
# is G.lift of T's run Y, line by line (Y not stopping, without messages,
# its new CHROMs not among z).

law or_f_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_f_r(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.true_ne_false(e))

law has_app_f:
  for +x: String
  for +a: List<&2, String>
  for +b: List<&2, String>
  for +ea: {R.has(x, a) == False{} : Bool}
  for +eb: {R.has(x, b) == False{} : Bool}
  {R.has(x, List.append(&2, String, a, b)) == False{} : Bool}

def has_app_f(x, a, b, ea, eb):
  match a:
    case Nil{}:
      eb
    case +y <> +t:
      +e1 = P.or_false_inv(String.eq(x, y), R.has(x, t), ea)
      +e2 = or_f_r(String.eq(x, y), R.has(x, t), ea)
      S.or_false_intro(String.eq(x, y), R.has(x, List.append(&2, String, t, b)), e1, has_app_f(x, t, b, e2, eb))

# The write step: X writes what Y writes.
law emit_eq:
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +dr: List<&2, R.Item>
  for +atX: B.At
  for +atY: B.At
  for +F: R.Flush
  for +rest: List<&2, R.Item>
  for e3: {F == R.Flushed{o2, G.img(q, l2, d)} : R.Flush}
  for er: {rest == SD.items_shift(d, dr) : List<&2, R.Item>}
  {R.emit.ready(F, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), Nil{}, SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, rest, atX)
    == G.lift(d, sh, z, p, sk, sns, q, R.emit.ready(R.Flushed{o2, l2}, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, dr, atY)) : R.RunSt}

def emit_eq(d, sh, z, p, sk, sns, q, n, h, c, e, ly, k, o, o2, l2, dr, atX, atY, F, rest, e3, er):
  %Equal.sym(R.Flush, F, R.Flushed{o2, G.img(q, l2, d)}, e3) :
    {R.emit.ready(_, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), Nil{}, SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, rest, atX)
      == G.lift(d, sh, z, p, sk, sns, q, R.emit.ready(R.Flushed{o2, l2}, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, dr, atY)) : R.RunSt}
  %Equal.sym(List<&2, R.Item>, rest, SD.items_shift(d, dr), er) :
    {R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, l2, d), _, SD.cnt_add(sk, k), String.append(String.append(p, o), o2), sns, False{}}
      == G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, True{}, h, c, e, l2, dr, k, String.append(o, o2), Nil{}, False{}}) : R.RunSt}
  %Q.s_append_assoc(p, o, o2) :
    {R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, l2, d), SD.items_shift(d, dr), SD.cnt_add(sk, k), String.append(String.append(p, o), o2), sns, False{}}
      == R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, l2, d), SD.items_shift(d, dr), SD.cnt_add(sk, k), _, sns, False{}} : R.RunSt}
  {==}

law flushed_is:
  for +fl: R.Flush
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for e: {fl == R.Flushed{o2, l2} : R.Flush}
  {G.is_flushed(fl) == True{} : Bool}

def flushed_is(fl, o2, l2, e):
  %Equal.sym(R.Flush, fl, R.Flushed{o2, l2}, e) : {G.is_flushed(_) == True{} : Bool}
  {==}

# X's flush of the moved items, from Y's flush.
law fl2_eq:
  for +ys: List<&2, R.Item>
  for +ly: Maybe<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +d: Nat
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +ha: {G.allreal(ys) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +ef: {R.flush(ys, ly) == R.Flushed{o2, l2} : R.Flush}
  {R.flush(SD.items_shift(d, ys), G.img(q, ly, d)) == R.Flushed{o2, G.img(q, l2, d)} : R.Flush}

def fl2_eq(ys, ly, q, d, o2, l2, ha, hq, ef):
  +e1 = EL.fl2(ys, ly, q, d, ha, hq, flushed_is(R.flush(ys, ly), o2, l2, ef))
  %Equal.sym(R.Flush, R.flush(SD.items_shift(d, ys), G.img(q, ly, d)), G.fmap(q, d, R.flush(ys, ly)), e1) : {_ == R.Flushed{o2, G.img(q, l2, d)} : R.Flush}
  %Equal.sym(R.Flush, R.flush(ys, ly), R.Flushed{o2, l2}, ef) : {G.fmap(q, d, _) == R.Flushed{o2, G.img(q, l2, d)} : R.Flush}
  {==}

# Y's last after a flush that passes keeps qok.
law qok_l2:
  for +ys: List<&2, R.Item>
  for +ly: Maybe<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +ha: {G.allreal(ys) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +ef: {R.flush(ys, ly) == R.Flushed{o2, l2} : R.Flush}
  {G.qok(q, l2) == True{} : Bool}

def qok_l2(ys, ly, q, o2, l2, ha, hq, ef):
  +el = S.flushed_last(ys, ly, o2, l2, S.flush_ok_sorted(ys, ly, o2, l2, ef), ef)
  %Equal.sym(Maybe<&2, R.Item>, l2, S.flast(ys, ly), el) : {G.qok(q, _) == True{} : Bool}
  EL.qok_flast(ys, ly, q, ha, hq)

def sr2.f(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +k: R.Cnt, +o: String, +w: Nat, +inpos: Nat, +atX: B.At, +atY: B.At, +bx: List<&2, R.Item>, +b2: List<&2, R.Item>, f: R.Flush,
  +ef: {R.flush(R.take_ready(w, inpos, b2), ly) == f : R.Flush},
  +hb2: {G.allreal(b2) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool},
  +etr: {R.take_ready(w, inpos, bx) == SD.items_shift(d, R.take_ready(w, inpos, b2)) : List<&2, R.Item>},
  +edr: {R.drop_ready(w, inpos, bx) == SD.items_shift(d, R.drop_ready(w, inpos, b2)) : List<&2, R.Item>},
  hg: {G.Good(c0, se, sc, R.emit.ready(f, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, R.drop_ready(w, inpos, b2), atY)) == True{} : Bool}) ->
  {R.emit.ready(R.flush(R.take_ready(w, inpos, bx), G.img(q, ly, d)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), Nil{}, SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.drop_ready(w, inpos, bx), atX) == G.lift(d, sh, z, p, sk, sns, q, R.emit.ready(f, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, R.drop_ready(w, inpos, b2), atY)) : R.RunSt} & {G.inv2(q, R.emit.ready(f, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, R.drop_ready(w, inpos, b2), atY)) == True{} : Bool}:
  match f:
    case R.Broke{o3, bad, prev}:
      Empty.absurd({R.emit.ready(R.flush(R.take_ready(w, inpos, bx), G.img(q, ly, d)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), Nil{}, SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.drop_ready(w, inpos, bx), atX) == G.lift(d, sh, z, p, sk, sns, q, R.emit.ready(R.Broke{o3, bad, prev}, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, R.drop_ready(w, inpos, b2), atY)) : R.RunSt} & {G.inv2(q, R.emit.ready(R.Broke{o3, bad, prev}, R.RunSt{n, True{}, h, c, e, ly, Nil{}, k, o, Nil{}, False{}}, R.drop_ready(w, inpos, b2), atY)) == True{} : Bool}, P.false_ne_true(hg))
    case R.Flushed{+o2, +l2}:
      +tr2 = R.take_ready(w, inpos, b2)
      +htr = EL.allreal_tr(w, inpos, b2, hb2)
      +e3 = Equal.trans(R.Flush, R.flush(R.take_ready(w, inpos, bx), G.img(q, ly, d)), R.flush(SD.items_shift(d, tr2), G.img(q, ly, d)), R.Flushed{o2, G.img(q, l2, d)},
        Equal.cong(List<&2, R.Item>, R.Flush, xs => R.flush(xs, G.img(q, ly, d)), R.take_ready(w, inpos, bx), SD.items_shift(d, tr2), etr),
        fl2_eq(tr2, ly, q, d, o2, l2, htr, hq, ef))
      +eq = emit_eq(d, sh, z, p, sk, sns, q, n, h, c, e, ly, k, o, o2, l2, R.drop_ready(w, inpos, b2), atX, atY,
        R.flush(R.take_ready(w, inpos, bx), G.img(q, ly, d)), R.drop_ready(w, inpos, bx), e3, edr)
      +iv = S.and_intro(G.allreal(R.drop_ready(w, inpos, b2)), G.qok(q, l2), EL.allreal_dr(w, inpos, b2, hb2), qok_l2(tr2, ly, q, o2, l2, htr, hq, ef))
      (eq, iv)

# same_run keeps X = lift(Y).
law sr2:
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +w: Nat
  for +key: Nat
  for +inpos: Nat
  for +ln: Nat
  for +ch: String
  for +ps: String
  for +text: String
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}
  for hg: {G.Good(c0, se, sc, R.same_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}
  {R.same_run(R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.same_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt}
    & {G.inv2(q, R.same_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}

def sr2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, w, key, inpos, ln, ch, ps, text, hb, hq, hit, hg):
  +ity = {R.Item{key, inpos, B.At{ln, ch, ps}, text} : R.Item}
  +b2 = R.insert(ity, b)
  +bx = R.insert(SD.item_shift(d, ity), SD.items_shift(d, b))
  +ei = EL.ins_sh(d, ity, b)
  +etr = Equal.trans(List<&2, R.Item>, R.take_ready(w, inpos, bx), R.take_ready(w, inpos, SD.items_shift(d, b2)), SD.items_shift(d, R.take_ready(w, inpos, b2)),
    Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.take_ready(w, inpos, xs), bx, SD.items_shift(d, b2), ei), EL.tr_sh(w, inpos, d, b2))
  +edr = Equal.trans(List<&2, R.Item>, R.drop_ready(w, inpos, bx), R.drop_ready(w, inpos, SD.items_shift(d, b2)), SD.items_shift(d, R.drop_ready(w, inpos, b2)),
    Equal.cong(List<&2, R.Item>, List<&2, R.Item>, xs => R.drop_ready(w, inpos, xs), bx, SD.items_shift(d, b2), ei), EL.dr_sh(w, inpos, d, b2))
  sr2.f(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, k, o, w, inpos, B.At{Nat.add(ln, d), ch, ps}, B.At{ln, ch, ps}, bx, b2, R.flush(R.take_ready(w, inpos, b2), ly), {==},
    EL.allreal_ins(ity, b, hit, hb), hq, etr, edr, hg)

def zf_c0(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +same: Bool,
  +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool}) ->
  {R.has(c0, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))) == False{} : Bool}:
  match sc same:
    case _ True{}:
      h1
    case None{} False{}:
      h1
    case Some{+s} False{}:
          S.or_false_intro(String.eq(c0, s), R.has(c0, se), Equal.trans(Bool, String.eq(c0, s), String.eq(s, c0), False{}, Q.str_eq_sym(s, c0), h2), h1)

def zf_x(+x: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +same: Bool,
  +h3: {R.has(x, se) == False{} : Bool}, +h4: {R.is_cur(sc, x) == False{} : Bool}) ->
  {R.has(x, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))) == False{} : Bool}:
  match sc same:
    case _ True{}:
      h3
    case None{} False{}:
      h3
    case Some{+s} False{}:
          S.or_false_intro(String.eq(x, s), R.has(x, se), Equal.trans(Bool, String.eq(x, s), String.eq(s, x), False{}, Q.str_eq_sym(s, x), h4), h3)

def zfree.go(+x: String, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +same: Bool, +v: Bool,
  +ev: {String.eq(x, c0) == v : Bool},
  +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hc: {(v || (Bool.not(R.has(x, se)) && Bool.not(R.is_cur(sc, x)))) == True{} : Bool}) ->
  {R.has(x, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))) == False{} : Bool}:
  match v:
    case True{}:
      +exc = Q.str_eq_sound(x, c0, ev)
      %Equal.sym(String, x, c0, exc) : {R.has(_, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))) == False{} : Bool}
      zf_c0(c0, se, sc, same, h1, h2)
    case False{}:
      +a = Bool.not(R.has(x, se))
      +b = Bool.not(R.is_cur(sc, x))
      zf_x(x, se, sc, same, P.not_true(R.has(x, se), P.and_true_l(a, b, hc)), P.not_true(R.is_cur(sc, x), P.and_true_r(a, b, hc)))

# A CHROM T starts is neither in S's ended list nor S's CHROM (or it is
# c0, which is not either): it is not in z.
law zfree:
  for +x: String
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +same: Bool
  for +z: List<&2, String>
  for +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == same : Bool}
  for +hc: {(String.eq(x, c0) || (Bool.not(R.has(x, se)) && Bool.not(R.is_cur(sc, x)))) == True{} : Bool}
  {R.has(x, z) == False{} : Bool}

def zfree(x, c0, se, sc, same, z, ez, h1, h2, hc):
  %ez : {R.has(x, _) == False{} : Bool}
  zfree.go(x, c0, se, sc, same, String.eq(x, c0), {==}, h1, h2, hc)

law pc_app:
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +z: List<&2, String>
  {List.append(&2, String, R.push_cur(c, e), z) == R.push_cur(c, List.append(&2, String, e, z)) : List<&2, String>}

def pc_app(c, e, z):
  match c:
    case None{}:
      {==}
    case Some{+s}:
      {==}

law nr2_eq:
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +n: Nat
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +o2: String
  for +l2: Maybe<&2, R.Item>
  for +w: Nat
  for +chrom: String
  for +itx: R.Item
  for +F: R.Flush
  for +H: Bool
  for +rhs: R.RunSt
  for e3: {F == R.Flushed{o2, G.img(q, l2, d)} : R.Flush}
  for eh: {H == False{} : Bool}
  for e1: {R.same_run(R.RunSt{Nat.add(n, d), True{}, sh, Some{chrom}, List.append(&2, String, R.push_cur(c, e), z), None{}, Nil{}, SD.cnt_add(sk, k), String.append(p, String.append(o, o2)), sns, False{}}, w, itx) == rhs : R.RunSt}
  {R.new_run.go(F, H, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, itx) == rhs : R.RunSt}

def nr2_eq(d, sh, z, p, sk, sns, q, n, c, e, ly, b, k, o, o2, l2, w, chrom, itx, F, H, rhs, e3, eh, e1):
  %Equal.sym(R.Flush, F, R.Flushed{o2, G.img(q, l2, d)}, e3) : {R.new_run.go(_, H, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, itx) == rhs : R.RunSt}
  %Equal.sym(Bool, H, False{}, eh) : {R.new_run.go(R.Flushed{o2, G.img(q, l2, d)}, _, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, itx) == rhs : R.RunSt}
  %pc_app(c, e, z) : {R.same_run(R.RunSt{Nat.add(n, d), True{}, sh, Some{chrom}, _, None{}, Nil{}, SD.cnt_add(sk, k), String.append(String.append(p, o), o2), sns, False{}}, w, itx) == rhs : R.RunSt}
  %Equal.sym(String, String.append(String.append(p, o), o2), String.append(p, String.append(o, o2)), Q.s_append_assoc(p, o, o2)) :
    {R.same_run(R.RunSt{Nat.add(n, d), True{}, sh, Some{chrom}, List.append(&2, String, R.push_cur(c, e), z), None{}, Nil{}, SD.cnt_add(sk, k), _, sns, False{}}, w, itx) == rhs : R.RunSt}
  e1

def nr2.k(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +w: Nat, +chrom: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +o2: String, +l2: Maybe<&2, R.Item>,
  e3: {R.flush(SD.items_shift(d, b), G.img(q, ly, d)) == R.Flushed{o2, G.img(q, l2, d)} : R.Flush},
  eh: {R.has(chrom, List.append(&2, String, e, z)) == False{} : Bool},
  pr: {R.same_run(R.RunSt{Nat.add(n, d), True{}, sh, Some{chrom}, List.append(&2, String, R.push_cur(c, e), z), None{}, Nil{}, SD.cnt_add(sk, k), String.append(p, String.append(o, o2)), sns, False{}}, w, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}) ->
  {R.new_run.go(R.flush(SD.items_shift(d, b), G.img(q, ly, d)), R.has(chrom, List.append(&2, String, e, z)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}:
  match pr:
    case (e1, iv):
      (nr2_eq(d, sh, z, p, sk, sns, q, n, c, e, ly, b, k, o, o2, l2, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}),
        R.flush(SD.items_shift(d, b), G.img(q, ly, d)), R.has(chrom, List.append(&2, String, e, z)), G.lift(d, sh, z, p, sk, sns, q, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})), e3, eh, e1), iv)

def nr2.f(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +w: Nat, +chrom: String, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool}, +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool},
  f: R.Flush, +ef: {R.flush(b, ly) == f : R.Flush}, g: Bool, +eg: {R.has(chrom, e) == g : Bool},
  +hg: {G.Good(c0, se, sc, R.new_run.go(f, g, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}) ->
  {R.new_run.go(R.flush(SD.items_shift(d, b), G.img(q, ly, d)), R.has(chrom, List.append(&2, String, e, z)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.new_run.go(f, g, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.new_run.go(f, g, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}:
  match f g:
    case R.Broke{o3, bad, prev} _:
      Empty.absurd({R.new_run.go(R.flush(SD.items_shift(d, b), G.img(q, ly, d)), R.has(chrom, List.append(&2, String, e, z)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.new_run.go(R.Broke{o3, bad, prev}, g, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.new_run.go(R.Broke{o3, bad, prev}, g, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, P.false_ne_true(hg))
    case R.Flushed{o2, l2} True{}:
      Empty.absurd({R.new_run.go(R.flush(SD.items_shift(d, b), G.img(q, ly, d)), R.has(chrom, List.append(&2, String, e, z)), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.new_run.go(R.Flushed{o2, l2}, True{}, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.new_run.go(R.Flushed{o2, l2}, True{}, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}, P.false_ne_true(hg))
    case R.Flushed{+o2, +l2} False{}:
      +hm = P.and_true_r(Bool.not(G.halt(R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}))), G.M(c0, se, sc, R.same_run(R.RunSt{n, True{}, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text})), hg)
      +cond = EM.nr_cond(c0, se, sc, n, True{}, h, chrom, c, e, k, String.append(o, o2), Nil{}, False{}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, hm)
      +eh = has_app_f(chrom, e, z, eg, zfree(chrom, c0, se, sc, same, z, ez, h1, h2, cond))
      +e3 = fl2_eq(b, ly, q, d, o2, l2, hb, hq, ef)
      nr2.k(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, w, chrom, key, inpos, ln, ch, ps, text, o2, l2, e3, eh,
        sr2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), w, key, inpos, ln, ch, ps, text, {==}, {==}, hit, hg))

# new_run keeps X = lift(Y).
law nr2:
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +w: Nat
  for +chrom: String
  for +key: Nat
  for +inpos: Nat
  for +ln: Nat
  for +ch: String
  for +ps: String
  for +text: String
  for +same: Bool
  for +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == same : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}
  for hg: {G.Good(c0, se, sc, R.new_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}
  {R.new_run(R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, chrom, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.new_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.new_run(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, chrom, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}

def nr2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, w, chrom, key, inpos, ln, ch, ps, text, same, ez, h1, h2, hb, hq, hit, hg):
  nr2.f(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, w, chrom, key, inpos, ln, ch, ps, text, same, ez, h1, h2, hb, hq, hit, R.flush(b, ly), {==}, R.has(chrom, e), {==}, hg)

def kd2.g(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k2: R.Cnt, +o: String,
  +w: Nat, +key: Nat, +inpos: Nat, +ln: Nat, +ch: String, +ps: String, +text: String, +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool}, +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool},
  +g: Bool, hg: {G.Good(c0, se, sc, R.keyed.go(g, R.RunSt{n, True{}, h, c, e, ly, b, k2, o, Nil{}, False{}}, w, ch, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}) ->
  {R.keyed.go(g, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k2), String.append(p, o), sns, False{}}, w, ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.keyed.go(g, R.RunSt{n, True{}, h, c, e, ly, b, k2, o, Nil{}, False{}}, w, ch, R.Item{key, inpos, B.At{ln, ch, ps}, text})) : R.RunSt} & {G.inv2(q, R.keyed.go(g, R.RunSt{n, True{}, h, c, e, ly, b, k2, o, Nil{}, False{}}, w, ch, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == True{} : Bool}:
  match g:
    case True{}:
      sr2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k2, o, w, key, inpos, ln, ch, ps, text, hb, hq, hit, hg)
    case False{}:
      nr2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k2, o, w, ch, key, inpos, ln, ch, ps, text, same, ez, h1, h2, hb, hq, hit, hg)

# keyed (a line without messages) keeps X = lift(Y).
law kd2:
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +w: Nat
  for +key: Nat
  for +inpos: Nat
  for +ln: Nat
  for +ch: String
  for +ps: String
  for +text: String
  for +k2: R.Cnt
  for +same: Bool
  for +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == same : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +hit: {SD.is_phantom(R.Item{key, inpos, B.At{ln, ch, ps}, text}) == False{} : Bool}
  for hg: {G.Good(c0, se, sc, R.keyed(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) == True{} : Bool}
  {R.keyed(R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, w, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text}), Nil{}, SD.cnt_add(sk, k2)) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) == True{} : Bool}

def kd2(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, w, key, inpos, ln, ch, ps, text, k2, same, ez, h1, h2, hb, hq, hit, hg):
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, sns, Nil{}), sns, P.append_nil(B.Note, sns)) :
    {R.keyed.go(R.is_cur(c, ch), R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k2), String.append(p, o), _, False{}}, w, ch, SD.item_shift(d, R.Item{key, inpos, B.At{ln, ch, ps}, text})) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{key, inpos, B.At{ln, ch, ps}, text}, Nil{}, k2)) == True{} : Bool}
  kd2.g(d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k2, o, w, key, inpos, ln, ch, ps, text, same, ez, h1, h2, hb, hq, hit, R.is_cur(c, ch), hg)

def bl2.r(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  r: B.Res, +op: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat, +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool},
  hg: {G.Good(c0, se, sc, R.body_line(r, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}) ->
  {R.body_line(r, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(r, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(r, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}:
  match r:
    case B.Res{B.Broken{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.NoContig{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.Problem{+cd}, k1, t, s}:
      match op:
        case B.Opts{+st, +w, +om_m, +om_z, +a}:
          match st:
            case True{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
            case False{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n+n, f0, f1}}], R.bump(k, False{}, False{}, True{}))), hg))))
    case B.Res{B.Skipped{}, k1, t, s}:
      %EL.cnt_bump(sk, k, False{}, True{}, False{}) : {R.keyed(R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{1n+Nat.add(n, d), f0, f1}, B.Line.text(li)}, Nil{}, _) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(k, False{}, True{}, False{}))) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{1n+n, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(k, False{}, True{}, False{}))) == True{} : Bool}
      kd2(d, sh, z, p, sk, sns, q, c0, se, sc, 1n+n, h, c, e, ly, b, k, o, R.Opts.w(op), pos, pos, 1n+n, f0, f1, B.Line.text(li), R.bump(k, False{}, True{}, False{}), same, ez, h1, h2, hb, hq, {==}, hg)
    case B.Res{B.Normalized{}, +k1, +t, +s}:
      match s:
        case True{}:
          Empty.absurd({R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{1n+Nat.add(n, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{1n+n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n+n, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))), hg))))
        case False{}:
          %EL.cnt_bump(sk, k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}) : {R.keyed(R.RunSt{1n+Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+Nat.add(n, d), f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, _) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{1n+n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{1n+n, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) == True{} : Bool}
          kd2(d, sh, z, p, sk, sns, q, c0, se, sc, 1n+n, h, c, e, ly, b, k, o, R.Opts.w(op), k1, pos, 1n+n, f0, f1, String.append(t, B.Line.term(li)), R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), same, ez, h1, h2, hb, hq, {==}, hg)

def bl2.rg(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +m: Nat, +an: Nat, +han: {Nat.is_eq(an, 0n) == False{} : Bool}, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  r: B.Res, +op: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat, +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool},
  hg: {G.Good(c0, se, sc, R.body_line(r, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) == True{} : Bool}) ->
  {R.body_line(r, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(r, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(r, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) == True{} : Bool}:
  match r:
    case B.Res{B.Broken{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.NoContig{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.Problem{+cd}, k1, t, s}:
      match op:
        case B.Opts{+st, +w, +om_m, +om_z, +a}:
          match st:
            case True{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
            case False{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}, w, R.Item{pos, pos, B.At{an, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{an, f0, f1}}], R.bump(k, False{}, False{}, True{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{pos, pos, B.At{an, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{an, f0, f1}}], R.bump(k, False{}, False{}, True{})))), G.M(c0, se, sc, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, w, R.Item{pos, pos, B.At{an, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{an, f0, f1}}], R.bump(k, False{}, False{}, True{}))), hg))))
    case B.Res{B.Skipped{}, k1, t, s}:
      %EL.cnt_bump(sk, k, False{}, True{}, False{}) : {R.keyed(R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{Nat.add(an, d), f0, f1}, B.Line.text(li)}, Nil{}, _) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{an, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(k, False{}, True{}, False{}))) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{pos, pos, B.At{an, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(k, False{}, True{}, False{}))) == True{} : Bool}
      kd2(d, sh, z, p, sk, sns, q, c0, se, sc, m, h, c, e, ly, b, k, o, R.Opts.w(op), pos, pos, an, f0, f1, B.Line.text(li), R.bump(k, False{}, True{}, False{}), same, ez, h1, h2, hb, hq, han, hg)
    case B.Res{B.Normalized{}, +k1, +t, +s}:
      match s:
        case True{}:
          Empty.absurd({R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) : R.RunSt} & {G.inv2(q, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}, R.Opts.w(op), R.Item{k1, pos, B.At{an, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{an, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{an, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{an, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{})))), G.M(c0, se, sc, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{an, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{an, f0, f1}}], R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))), hg))))
        case False{}:
          %EL.cnt_bump(sk, k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}) : {R.keyed(R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{Nat.add(an, d), f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, _) == G.lift(d, sh, z, p, sk, sns, q, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{an, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) : R.RunSt} & {G.inv2(q, R.keyed(R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), R.Item{k1, pos, B.At{an, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) == True{} : Bool}
          kd2(d, sh, z, p, sk, sns, q, c0, se, sc, m, h, c, e, ly, b, k, o, R.Opts.w(op), k1, pos, an, f0, f1, String.append(t, B.Line.term(li)), R.bump(k, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), same, ez, h1, h2, hb, hq, han, hg)

def bl2_un(+bb: Bool, +cd: B.Code, +d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +m: Nat, +an: Nat, +han: {Nat.is_eq(an, 0n) == False{} : Bool}, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +fa: List<&2, B.Contig>, +op: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat,
  +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool},
  +hg: {G.Good(c0, se, sc, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos), R.problem_line(R.Opts.strict(op), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), cd, li, B.At{an, f0, f1}, pos))) == True{} : Bool}) ->
  {Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, li, B.At{Nat.add(an, d), f0, f1}, pos), R.problem_line(R.Opts.strict(op), R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, R.Opts.w(op), cd, li, B.At{Nat.add(an, d), f0, f1}, pos))
     == G.lift(d, sh, z, p, sk, sns, q, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos), R.problem_line(R.Opts.strict(op), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), cd, li, B.At{an, f0, f1}, pos))) : R.RunSt}
    & {G.inv2(q, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, li, B.At{an, f0, f1}, pos), R.problem_line(R.Opts.strict(op), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, R.Opts.w(op), cd, li, B.At{an, f0, f1}, pos))) == True{} : Bool}:
  match bb:
    case True{}:
      bl2.rg(d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, L.judge(fa, B.Line.body(li)), op, li, f0, f1, pos, same, ez, h1, h2, hb, hq, hg)
    case False{}:
      bl2.rg(d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, B.Res{B.Problem{cd}, 0n, "", False{}}, op, li, f0, f1, pos, same, ez, h1, h2, hb, hq, hg)

# With -m: Good at the end of a split line's records is Good before them.
def good_pin(+ps: List<&2, String>, +fa: List<&2, B.Contig>, +op: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +pos: Nat, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>,
  +hg: {G.Good(c0, se, sc, L.pieces_in(ps, fa, op, st, term, at, pos)) == True{} : Bool}) ->
  {G.Good(c0, se, sc, st) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      %EM.pin_halted(ps, fa, op, n, i, h, c, e, l, b, k, o, ns, term, at, pos) : {G.Good(c0, se, sc, _) == True{} : Bool}
      hg
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      EM.pieces_m(c0, se, sc, fa, op, ps, R.RunSt{n, i, h, c, e, l, b, k, o, ns, False{}}, term, at, pos,
        P.and_true_r(Bool.not(G.halt(L.pieces_in(ps, fa, op, R.RunSt{n, i, h, c, e, l, b, k, o, ns, False{}}, term, at, pos))), G.M(c0, se, sc, L.pieces_in(ps, fa, op, R.RunSt{n, i, h, c, e, l, b, k, o, ns, False{}}, term, at, pos)), hg))

# A split line's records keep X = lift(Y), record by record.
def pieces_lift(+ps: List<&2, String>, +d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +st: R.RunSt, +fa: List<&2, B.Contig>, +op: B.Opts, +term: String, +an: Nat, +han: {Nat.is_eq(an, 0n) == False{} : Bool}, +f0: String, +f1: String, +pos: Nat,
  +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hi: {G.inv2(q, st) == True{} : Bool},
  +hg: {G.Good(c0, se, sc, L.pieces_in(ps, fa, op, st, term, B.At{an, f0, f1}, pos)) == True{} : Bool}) ->
  {L.pieces_in(ps, fa, op, G.lift(d, sh, z, p, sk, sns, q, st), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(ps, fa, op, st, term, B.At{an, f0, f1}, pos)) : R.RunSt}
    & {G.inv2(q, L.pieces_in(ps, fa, op, st, term, B.At{an, f0, f1}, pos)) == True{} : Bool}:
  match ps:
    case Nil{}:
      ({==}, hi)
    case Con{+px, +ps2}:
      match st:
        case R.RunSt{+m, False{}, +h, +c, +e, +ly, +b, +k, +o, +ns, +x}:
          Empty.absurd({L.pieces_in(Con{px, ps2}, fa, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{m, False{}, h, c, e, ly, b, k, o, ns, x}), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, False{}, h, c, e, ly, b, k, o, ns, x}, term, B.At{an, f0, f1}, pos)) : R.RunSt}
            & {G.inv2(q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, False{}, h, c, e, ly, b, k, o, ns, x}, term, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hi))
        case R.RunSt{+m, True{}, +h, +c, +e, +ly, +b, +k, +o, +ns, True{}}:
          Empty.absurd({L.pieces_in(Con{px, ps2}, fa, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{m, True{}, h, c, e, ly, b, k, o, ns, True{}}), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, ns, True{}}, term, B.At{an, f0, f1}, pos)) : R.RunSt}
            & {G.inv2(q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, ns, True{}}, term, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hi))
        case R.RunSt{+m, True{}, +h, +c, +e, +ly, +b, +k, +o, Con{+y, +ys}, False{}}:
          Empty.absurd({L.pieces_in(Con{px, ps2}, fa, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Con{y, ys}, False{}}), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Con{y, ys}, False{}}, term, B.At{an, f0, f1}, pos)) : R.RunSt}
            & {G.inv2(q, L.pieces_in(Con{px, ps2}, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Con{y, ys}, False{}}, term, B.At{an, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hi))
        case R.RunSt{+m, True{}, +h, +c, +e, +ly, +b, +k, +o, Nil{}, False{}}:
          +s1 = R.body_line(L.judge(fa, px), R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, op, B.Line{px, term}, B.At{an, f0, f1}, pos)
          +s1l = R.body_line(L.judge(fa, px), R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, op, B.Line{px, term}, B.At{Nat.add(an, d), f0, f1}, pos)
          +hb = P.and_true_l(G.allreal(b), G.qok(q, ly), hi)
          +hq = P.and_true_r(G.allreal(b), G.qok(q, ly), hi)
          +g1 = good_pin(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos, c0, se, sc, hg)
          +eq1 = Pair.fst({s1l == G.lift(d, sh, z, p, sk, sns, q, s1) : R.RunSt}, {G.inv2(q, s1) == True{} : Bool}, bl2.rg(d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, L.judge(fa, px), op, B.Line{px, term}, f0, f1, pos, same, ez, h1, h2, hb, hq, g1))
          +iv1 = Pair.snd({s1l == G.lift(d, sh, z, p, sk, sns, q, s1) : R.RunSt}, {G.inv2(q, s1) == True{} : Bool}, bl2.rg(d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, L.judge(fa, px), op, B.Line{px, term}, f0, f1, pos, same, ez, h1, h2, hb, hq, g1))
          (Equal.trans(R.RunSt, L.pieces_in(ps2, fa, op, s1l, term, B.At{Nat.add(an, d), f0, f1}, pos), L.pieces_in(ps2, fa, op, G.lift(d, sh, z, p, sk, sns, q, s1), term, B.At{Nat.add(an, d), f0, f1}, pos), G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos)),
            Equal.cong(R.RunSt, R.RunSt, zz => L.pieces_in(ps2, fa, op, zz, term, B.At{Nat.add(an, d), f0, f1}, pos), s1l, G.lift(d, sh, z, p, sk, sns, q, s1), eq1),
            Pair.fst({L.pieces_in(ps2, fa, op, G.lift(d, sh, z, p, sk, sns, q, s1), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos)) : R.RunSt}, {G.inv2(q, L.pieces_in(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos)) == True{} : Bool}, pieces_lift(ps2, d, sh, z, p, sk, sns, q, c0, se, sc, s1, fa, op, term, an, han, f0, f1, pos, same, ez, h1, h2, iv1, hg))),
           Pair.snd({L.pieces_in(ps2, fa, op, G.lift(d, sh, z, p, sk, sns, q, s1), term, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.pieces_in(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos)) : R.RunSt}, {G.inv2(q, L.pieces_in(ps2, fa, op, s1, term, B.At{an, f0, f1}, pos)) == True{} : Bool}, pieces_lift(ps2, d, sh, z, p, sk, sns, q, c0, se, sc, s1, fa, op, term, an, han, f0, f1, pos, same, ez, h1, h2, iv1, hg)))

# What -m does with a line keeps X = lift(Y).
def bl2_body(+pt: B.Parts, +d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +m: Nat, +an: Nat, +han: {Nat.is_eq(an, 0n) == False{} : Bool}, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +fa: List<&2, B.Contig>, +op: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat,
  +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hb: {G.allreal(b) == True{} : Bool}, +hq: {G.qok(q, ly) == True{} : Bool},
  +hg: {G.Good(c0, se, sc, L.body_in(pt, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li, B.At{an, f0, f1}, pos)) == True{} : Bool}) ->
  {L.body_in(pt, fa, op, R.RunSt{Nat.add(m, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, li, B.At{Nat.add(an, d), f0, f1}, pos) == G.lift(d, sh, z, p, sk, sns, q, L.body_in(pt, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li, B.At{an, f0, f1}, pos)) : R.RunSt}
    & {G.inv2(q, L.body_in(pt, fa, op, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li, B.At{an, f0, f1}, pos)) == True{} : Bool}:
  match pt:
    case B.Whole{}:
      bl2.rg(d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, L.judge(fa, B.Line.body(li)), op, li, f0, f1, pos, same, ez, h1, h2, hb, hq, hg)
    case B.Pieces{+ps}:
      pieces_lift(ps, d, sh, z, p, sk, sns, q, c0, se, sc, R.RunSt{m, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, fa, op, B.Line.term(li), an, han, f0, f1, pos, same, ez, h1, h2, S.and_intro(G.allreal(b), G.qok(q, ly), hb, hq), hg)
    case B.Unsplit{+cd}:
      bl2_un(L.stops(L.judge(fa, B.Line.body(li)), R.Opts.strict(op)), cd, d, sh, z, p, sk, sns, q, c0, se, sc, m, an, han, h, c, e, ly, b, k, o, fa, op, li, f0, f1, pos, same, ez, h1, h2, hb, hq, hg)

# One body line keeps X = lift(Y).
law bl2:
  for +dfs: B.Defs
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +ly: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +li: B.Line
  for +same: Bool
  for +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == same : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for hg: {G.Good(c0, se, sc, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)) == True{} : Bool}
  {L.line_step(fa, dfs, op, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, li) == G.lift(d, sh, z, p, sk, sns, q, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)) : R.RunSt} & {G.inv2(q, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)) == True{} : Bool}

def bl2(dfs,d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, fa, op, li, same, ez, h1, h2, hb, hq, hg):
  +fs = B.Rec.fields(B.Line.body(li))
  bl2_body(B.Rec.parts(dfs, op, B.Line.body(li)), d, sh, z, p, sk, sns, q, c0, se, sc, 1n+n, 1n+n, {==}, h, c, e, ly, b, k, o, fa, op, li, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.pos(fs), same, ez, h1, h2, hb, hq, hg)


def par.k(+dfs: B.Defs, +d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +li: B.Line,
  hg: {G.Good(c0, se, sc, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li))) == True{} : Bool},
  ih: @st2: R.RunSt -> {G.inv2(q, st2) == True{} : Bool} -> {G.Good(c0, se, sc, L.run.go(t, fa, dfs, op, st2)) == True{} : Bool} -> {L.run.go(t, fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, st2)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, st2)) : R.RunSt},
  pr: {L.line_step(fa, dfs, op, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, li) == G.lift(d, sh, z, p, sk, sns, q, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)) : R.RunSt} & {G.inv2(q, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)) == True{} : Bool}) ->
  {L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}), li)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li))) : R.RunSt}:
  match pr:
    case (es, iv):
      %Equal.sym(R.RunSt, L.line_step(fa, dfs, op, R.RunSt{Nat.add(n, d), True{}, sh, c, List.append(&2, String, e, z), G.img(q, ly, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), sns, False{}}, li), G.lift(d, sh, z, p, sk, sns, q, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li)), es) :
        {L.run.go(t, fa, dfs, op, _) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li))) : R.RunSt}
      ih(L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li), iv, hg)

def par.go(+dfs: B.Defs, +d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +ly: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String,
  +ns: List<&2, B.Note>, +x: Bool, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +op: B.Opts, +li: B.Line, +same: Bool, +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == same : Bool},
  +hi: {G.inv2(q, R.RunSt{n, i, h, c, e, ly, b, k, o, ns, x}) == True{} : Bool},
  +hg: {G.Good(c0, se, sc, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, i, h, c, e, ly, b, k, o, ns, x}, li))) == True{} : Bool},
  ih: @st2: R.RunSt -> {G.inv2(q, st2) == True{} : Bool} -> {G.Good(c0, se, sc, L.run.go(t, fa, dfs, op, st2)) == True{} : Bool} -> {L.run.go(t, fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, st2)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, st2)) : R.RunSt}) ->
  {L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, i, h, c, e, ly, b, k, o, ns, x}), li)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, i, h, c, e, ly, b, k, o, ns, x}, li))) : R.RunSt}:
  match i ns x:
    case False{} _ _:
      Empty.absurd({L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, False{}, h, c, e, ly, b, k, o, ns, x}), li)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, False{}, h, c, e, ly, b, k, o, ns, x}, li))) : R.RunSt}, P.false_ne_true(hi))
    case True{} _ True{}:
      Empty.absurd({L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, True{}, h, c, e, ly, b, k, o, ns, True{}}), li)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, ns, True{}}, li))) : R.RunSt}, P.false_ne_true(hi))
    case True{} y <> ys False{}:
      Empty.absurd({L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, R.RunSt{n, True{}, h, c, e, ly, b, k, o, y <> ys, False{}}), li)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(t, fa, dfs, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, y <> ys, False{}}, li))) : R.RunSt}, P.false_ne_true(hi))
    case True{} Nil{} False{}:
      +hb = P.and_true_l(G.allreal(b), G.qok(q, ly), hi)
      +hq = P.and_true_r(G.allreal(b), G.qok(q, ly), hi)
      +hg1 = EM.good_back(dfs, c0, se, sc, t, fa, op, L.line_step(fa, dfs, op, R.RunSt{n, True{}, h, c, e, ly, b, k, o, Nil{}, False{}}, li), hg)
      par.k(dfs, d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, t, fa, op, li, hg, ih, bl2(dfs, d, sh, z, p, sk, sns, q, c0, se, sc, n, h, c, e, ly, b, k, o, fa, op, li, same, ez, h1, h2, hb, hq, hg1))

# Phase 2: along the rest of the lines, the true run is lift of T's.
law par:
  for +dfs: B.Defs
  for +d: Nat
  for +sh: String
  for +z: List<&2, String>
  for +p: String
  for +sk: R.Cnt
  for +sns: List<&2, B.Note>
  for +q: Maybe<&2, R.Item>
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +op: B.Opts
  for +same: Bool
  for +ez: {Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se)) == z : List<&2, String>}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == same : Bool}
  for +st: R.RunSt
  for +hi: {G.inv2(q, st) == True{} : Bool}
  for hg: {G.Good(c0, se, sc, L.run.go(ls, fa, dfs, op, st)) == True{} : Bool}
  {L.run.go(ls, fa, dfs, op, G.lift(d, sh, z, p, sk, sns, q, st)) == G.lift(d, sh, z, p, sk, sns, q, L.run.go(ls, fa, dfs, op, st)) : R.RunSt}

def par(dfs,d, sh, z, p, sk, sns, q, c0, se, sc, ls, fa, op, same, ez, h1, h2, st, hi, hg):
  match ls:
    case Nil{}:
      {==}
    case +li <> +t:
      match st:
        case R.RunSt{+n, +i, +h, +c, +e, +ly, +b, +k, +o, +ns, +x}:
          par.go(dfs, d, sh, z, p, sk, sns, q, c0, se, sc, n, i, h, c, e, ly, b, k, o, ns, x, t, fa, op, li, same, ez, h1, h2, hi, hg,
            st2 => hi2 => hg2 => par(dfs, d, sh, z, p, sk, sns, q, c0, se, sc, t, fa, op, same, ez, h1, h2, st2, hi2, hg2))
