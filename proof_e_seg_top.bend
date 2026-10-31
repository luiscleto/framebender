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
import ./proof_b_adv_msx.bend as MSX
import ./proof_s_site.bend as SITE
import ./proof_s_one.bend as OI

# Phase E, area "seg": the facts the assembly needs (a run in the body stays
# in it, the keys of S's buffer, its order) and the last item at the end.

# In the body
# ===========

law sr_ib:
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  {R.RunSt.inbody(R.same_run(R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, x}, w, it)) == True{} : Bool}

def sr_ib(n, h, c, e, l, b, k, o, ns, x, w, it):
  ST.SR(s => {R.RunSt.inbody(s) == True{} : Bool}, n, True{}, h, c, e, l, b, k, o, ns, x, w, it,
    o3 => bad => prev => ef => {==}, o2 => l2 => ef => {==})

law nr_ib:
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.inbody(R.new_run(R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, x}, w, chrom, it)) == True{} : Bool}

def nr_ib(n, h, c, e, l, b, k, o, ns, x, w, chrom, it):
  ST.NR(s => {R.RunSt.inbody(s) == True{} : Bool}, n, True{}, h, c, e, l, b, k, o, ns, x, w, chrom, it,
    o3 => bad => prev => ef => {==}, o2 => l2 => ef => eg => {==},
    o2 => l2 => ef => eg => sr_ib(n, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, x, w, it))

def kd_ib.go(+g: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt,
  +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat, +chrom: String, +it: R.Item) ->
  {R.RunSt.inbody(R.keyed.go(g, R.RunSt{n, True{}, h, c, e, l, b, k, o, ns, x}, w, chrom, it)) == True{} : Bool}:
  match g:
    case True{}:
      sr_ib(n, h, c, e, l, b, k, o, ns, x, w, it)
    case False{}:
      nr_ib(n, h, c, e, l, b, k, o, ns, x, w, chrom, it)

law ib_step:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +li: B.Line
  for +st: R.RunSt
  for +h: {R.RunSt.inbody(st) == True{} : Bool}
  {R.RunSt.inbody(L.line_step(fa, dfs, o, st, li)) == True{} : Bool}

def ib_step.go(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +li: B.Line, +n: Nat, +i: Bool, +hh: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +x: Bool,
  +h: {i == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, i, hh, c, e, l, b, k, out, ns, x}, li)) == True{} : Bool}:
  MSX.ib_step.k(dfs, x, i, fa, o, n, hh, c, e, l, b, k, out, ns, li, h)


def ib_step(dfs,fa, o, li, st, h):
  match st:
    case R.RunSt{+n, +i, +hh, +c, +e, +l, +b, +k, +out, +ns, +x}:
      ib_step.go(dfs, fa, o, li, n, i, hh, c, e, l, b, k, out, ns, x, h)

# A run in the body stays in the body.
law ib_go:
  for +dfs: B.Defs
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +h: {R.RunSt.inbody(st) == True{} : Bool}
  {R.RunSt.inbody(L.run.go(ls, fa, dfs, o, st)) == True{} : Bool}

def ib_go(dfs,ls, fa, o, st, h):
  match ls:
    case Nil{}:
      h
    case +li <> +t:
      ib_go(dfs, t, fa, o, L.line_step(fa, dfs, o, st, li), ib_step(dfs, fa, o, li, st, h))

# S's buffer: its keys, its order
# ===============================

law le_max_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}

def le_max_l(a, b):
  match a b:
    case 0n _:
      P.le_zero_l(b)
    case 1n+ap 0n:
      P.le_refl(1n+ap)
    case 1n+ap 1n+bp:
      le_max_l(ap, bp)

law le_max_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}

def le_max_r(a, b):
  match a b:
    case 0n _:
      P.le_refl(b)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      le_max_r(ap, bp)

law maxkey_base:
  for +xs: List<&2, R.Item>
  for +m: Nat
  {Nat.is_le(m, SD.maxkey(xs, m)) == True{} : Bool}

def maxkey_base(xs, m):
  match xs:
    case Nil{}:
      P.le_refl(m)
    case +x <> +t:
      Q.le_trans(m, Nat.max(m, R.Item.key(x)), SD.maxkey(t, Nat.max(m, R.Item.key(x))), le_max_l(m, R.Item.key(x)), maxkey_base(t, Nat.max(m, R.Item.key(x))))

law maxkey_all:
  for +xs: List<&2, R.Item>
  for +m: Nat
  {S.all_le(xs, SD.maxkey(xs, m)) == True{} : Bool}

def maxkey_all(xs, m):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +m2 = Nat.max(m, R.Item.key(x))
      S.and_intro(Nat.is_le(R.Item.key(x), SD.maxkey(t, m2)), S.all_le(t, SD.maxkey(t, m2)),
        Q.le_trans(R.Item.key(x), m2, SD.maxkey(t, m2), le_max_r(m, R.Item.key(x)), maxkey_base(t, m2)), maxkey_all(t, m2))

law lkey_ko:
  for +m: Maybe<&2, R.Item>
  {S.lkey(m) == SD.key_or(m, 0n) : Nat}

def lkey_ko(m):
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def last_le_all.go(+x: R.Item, +t: List<&2, R.Item>, +m: Nat, +hx: {Nat.is_le(R.Item.key(x), m) == True{} : Bool},
  ih: {List.is_empty(&2, R.Item, t) == False{} : Bool} -> {Nat.is_le(S.lkey(SD.last_item(t)), m) == True{} : Bool}) ->
  {Nat.is_le(S.lkey(Maybe.or(&2, R.Item, SD.last_item(t), Some{x})), m) == True{} : Bool}:
  match t:
    case Nil{}:
      hx
    case +y <> +u:
      %Equal.sym(Maybe<&2, R.Item>, Maybe.or(&2, R.Item, SD.last_item(y <> u), Some{x}), SD.last_item(y <> u), E2.last_or_ne(y <> u, Some{x}, {==})) :
        {Nat.is_le(S.lkey(_), m) == True{} : Bool}
      ih({==})

# The last item of a nonempty list has a key at most any bound of all keys.
law last_le_all:
  for +xs: List<&2, R.Item>
  for +m: Nat
  for +h: {S.all_le(xs, m) == True{} : Bool}
  for +hne: {List.is_empty(&2, R.Item, xs) == False{} : Bool}
  {Nat.is_le(S.lkey(SD.last_item(xs)), m) == True{} : Bool}

def last_le_all(xs, m, h, hne):
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_le(0n, m) == True{} : Bool}, P.true_ne_false(hne))
    case +x <> +t:
      +ht = P.and_true_r(Nat.is_le(R.Item.key(x), m), S.all_le(t, m), h)
      last_le_all.go(x, t, m, P.and_true_l(Nat.is_le(R.Item.key(x), m), S.all_le(t, m), h), hne2 => last_le_all(t, m, ht, hne2))

law sorted_go_eq:
  for +xs: List<&2, R.Item>
  for +k: Nat
  {SD.sorted.go(xs, k) == S.sorted_from(xs, k) : Bool}

def sorted_go_eq(xs, k):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %sorted_go_eq(t, R.Item.key(x)) : {Bool.and(Nat.is_le(k, R.Item.key(x)), SD.sorted.go(t, R.Item.key(x))) == Bool.and(Nat.is_le(k, R.Item.key(x)), _) : Bool}
      {==}

def sorted_conv.k(+x: R.Item, +t: List<&2, R.Item>, +sl: Maybe<&2, R.Item>,
  +h1: {S.sorted_from(t, R.Item.key(x)) == True{} : Bool}, +h2: {SD.last_le(sl, R.Item.key(x)) == True{} : Bool}) ->
  {S.sorted_from(x <> t, S.lkey(sl)) == True{} : Bool}:
  match sl:
    case None{}:
      S.and_intro(Nat.is_le(0n, R.Item.key(x)), S.sorted_from(t, R.Item.key(x)), P.le_zero_l(R.Item.key(x)), h1)
    case Some{+y}:
      S.and_intro(Nat.is_le(R.Item.key(y), R.Item.key(x)), S.sorted_from(t, R.Item.key(x)), h2, h1)

# segok's order of S's buffer, as flush needs it.
law sorted_conv:
  for +sb: List<&2, R.Item>
  for +sl: Maybe<&2, R.Item>
  for +h1: {SD.sorted(sb) == True{} : Bool}
  for +h2: {(List.is_empty(&2, R.Item, sb) || SD.last_le(sl, SD.key_or(SD.first_item(sb), 0n))) == True{} : Bool}
  {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}

def sorted_conv(sb, sl, h1, h2):
  match sb:
    case Nil{}:
      {==}
    case +x <> +t:
      sorted_conv.k(x, t, sl, Equal.trans(Bool, S.sorted_from(t, R.Item.key(x)), SD.sorted.go(t, R.Item.key(x)), True{},
        Equal.sym(Bool, SD.sorted.go(t, R.Item.key(x)), S.sorted_from(t, R.Item.key(x)), sorted_go_eq(t, R.Item.key(x))), h1), h2)

# T's last item as the true run's
# ===============================

law img_ls:
  for +same: Bool
  for +sl: Maybe<&2, R.Item>
  for +elast: Maybe<&2, R.Item>
  for +tl: Maybe<&2, R.Item>
  for +d: Nat
  {G.img(Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), tl, d) == SD.last_shift(tl, same, sl, elast, d) : Maybe<&2, R.Item>}

def img_ls.k(+ph: Bool, +same: Bool, +sl: Maybe<&2, R.Item>, +elast: Maybe<&2, R.Item>, +x: R.Item, +d: Nat) ->
  {G.img.k(ph, Bool.pick(Maybe<&2, R.Item>, same, Maybe.or(&2, R.Item, elast, sl), None{}), x, d) == SD.last_shift.k(ph, x, same, sl, elast, d) : Maybe<&2, R.Item>}:
  match ph same:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

def img_ls(same, sl, elast, tl, d):
  match tl:
    case None{}:
      {==}
    case Some{+x}:
      img_ls.k(SD.is_phantom(x), same, sl, elast, x, d)

# The first line when S's CHROM is not c0
# =======================================

law bump0:
  for +sk: R.Cnt
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {SD.cnt_add(sk, R.bump(R.Cnt{0n, 0n, 0n, 0n}, a, b, c)) == R.bump(sk, a, b, c) : R.Cnt}

def bump0(sk, a, b, c):
  %EL.cnt_zero(sk) : {SD.cnt_add(sk, R.bump(R.Cnt{0n, 0n, 0n, 0n}, a, b, c)) == R.bump(_, a, b, c) : R.Cnt}
  EL.cnt_bump(sk, R.Cnt{0n, 0n, 0n, 0n}, a, b, c)

def kd0.g(+fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, +w: Nat, +key: Nat, +inpos: Nat, +f0: String, +f1: String, +text: String, +k2: R.Cnt,
  +ef0: {f0 == c0 : String}, +gX: Bool, +gY: Bool, +hX: {gX == False{} : Bool}, +hY: {gY == True{} : Bool},
  hg: {G.Good(c0, se, sc, R.keyed.go(gY, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}) ->
  {R.keyed.go(gX, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, sns, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed.go(gY, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.keyed.go(gY, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}:
  match gX gY:
    case True{} _:
      Empty.absurd({R.keyed.go(True{}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, sns, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed.go(gY, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.keyed.go(gY, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}, P.true_ne_false(hX))
    case False{} False{}:
      Empty.absurd({R.keyed.go(False{}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, sns, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed.go(False{}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.keyed.go(False{}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, f0, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}, P.false_ne_true(hY))
    case False{} True{}:
      +eh = Equal.trans(Bool, R.has(f0, se), R.has(c0, se), False{}, Equal.cong(String, Bool, x => R.has(x, se), f0, c0, ef0), h1)
      %Equal.sym(R.Flush, R.flush(sb, sl), R.Flushed{L.texts(sb), S.flast(sb, sl)}, S.flush_sorted(sb, sl, hs)) : {R.new_run.go(_, R.has(f0, se), R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, sns, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}
      %Equal.sym(Bool, R.has(f0, se), False{}, eh) : {R.new_run.go(R.Flushed{L.texts(sb), S.flast(sb, sl)}, _, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, sns, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}
      %Equal.sym(String, f0, c0, ef0) : {R.same_run(R.RunSt{1n+sn, True{}, sh, Some{_}, R.push_cur(sc, se), None{}, Nil{}, SD.cnt_add(sk, k2), String.append(so, L.texts(sb)), sns, False{}}, w, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}
      %Q.s_append_nil(String.append(so, L.texts(sb))) : {R.same_run(R.RunSt{1n+sn, True{}, sh, Some{c0}, R.push_cur(sc, se), None{}, Nil{}, SD.cnt_add(sk, k2), _, sns, False{}}, w, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) : R.RunSt} & {G.inv2(None{}, R.same_run(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text})) == True{} : Bool}
      EP.sr2(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, c0, se, sc, 1n, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k2, "",
        w, key, inpos, 1n, f0, f1, text, {==}, P.le_zero_l(l), {==}, hg)

def kd0(+fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, +w: Nat, +key: Nat, +inpos: Nat, +f0: String, +f1: String, +text: String, +k2: R.Cnt,
  +ef0: {f0 == c0 : String}, hg: {G.Good(c0, se, sc, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text}, Nil{}, k2)) == True{} : Bool}) ->
  {R.keyed(R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, w, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}, Nil{}, SD.cnt_add(sk, k2)) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text}, Nil{}, k2)) : R.RunSt} & {G.inv2(None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text}, Nil{}, k2)) == True{} : Bool}:
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, sns, Nil{}), sns, P.append_nil(B.Note, sns)) :
    {R.keyed.go(R.is_cur(sc, f0), R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, SD.cnt_add(sk, k2), so, _, False{}}, w, f0, R.Item{key, inpos, B.At{1n+sn, f0, f1}, text}) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text}, Nil{}, k2)) : R.RunSt} & {G.inv2(None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{key, inpos, B.At{1n, f0, f1}, text}, Nil{}, k2)) == True{} : Bool}
  +hX = Equal.trans(Bool, R.is_cur(sc, f0), R.is_cur(sc, c0), False{}, Equal.cong(String, Bool, x => R.is_cur(sc, x), f0, c0, ef0), h2)
  +hY = Equal.trans(Bool, String.eq(c0, f0), String.eq(c0, c0), True{}, Equal.cong(String, Bool, x => String.eq(c0, x), f0, c0, ef0), Q.str_eq_refl(c0))
  kd0.g(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, w, key, inpos, f0, f1, text, k2, ef0, R.is_cur(sc, f0), R.is_cur(Some{c0}, f0), hX, hY, hg)

def bl0.r(+fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, r: B.Res, +o: B.Opts, +li: B.Line, +f0: String, +f1: String, +pos: Nat, +ef0: {f0 == c0 : String},
  hg: {G.Good(c0, se, sc, R.body_line(r, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}) ->
  {R.body_line(r, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(r, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(r, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}:
  match r:
    case B.Res{B.Broken{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(B.Res{B.Broken{}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.NoContig{}, k1, t, s}:
      Empty.absurd({R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(B.Res{B.NoContig{}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
    case B.Res{B.Problem{+cd}, k1, t, s}:
      match o:
        case B.Opts{+st, +w, +om_m, +om_z, +a}:
          match st:
            case True{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, B.Opts{True{}, w, om_m, om_z, a}, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(hg))
            case False{}:
              Empty.absurd({R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(B.Res{B.Problem{cd}, k1, t, s}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, B.Opts{False{}, w, om_m, om_z, a}, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}, w, R.Item{pos, pos, B.At{1n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, False{}, True{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, False{}, True{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, w, R.Item{pos, pos, B.At{1n, f0, f1}, B.Line.text(li)}, [B.Warning{cd, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, False{}, True{}))), hg))))
    case B.Res{B.Skipped{}, k1, t, s}:
      %bump0(sk, False{}, True{}, False{}) : {R.keyed(R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, R.Opts.w(o), R.Item{pos, pos, B.At{1n+sn, f0, f1}, B.Line.text(li)}, Nil{}, _) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{pos, pos, B.At{1n, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, True{}, False{}))) : R.RunSt} & {G.inv2(None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{pos, pos, B.At{1n, f0, f1}, B.Line.text(li)}, Nil{}, R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, True{}, False{}))) == True{} : Bool}
      kd0(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, R.Opts.w(o), pos, pos, f0, f1, B.Line.text(li), R.bump(R.Cnt{0n, 0n, 0n, 0n}, False{}, True{}, False{}), ef0, hg)
    case B.Res{B.Normalized{}, +k1, +t, +s}:
      match s:
        case True{}:
          Empty.absurd({R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) : R.RunSt} & {G.inv2(None{}, R.body_line(B.Res{B.Normalized{}, k1, t, True{}}, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.false_ne_true(EM.keyed_m(c0, se, sc, 1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}, R.Opts.w(o), R.Item{k1, pos, B.At{1n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), P.and_true_r(Bool.not(G.halt(R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{k1, pos, B.At{1n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{})))), G.M(c0, se, sc, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{k1, pos, B.At{1n, f0, f1}, String.append(t, B.Line.term(li))}, [B.Warning{B.Stale{}, B.At{1n, f0, f1}}], R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))), hg))))
        case False{}:
          %bump0(sk, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}) : {R.keyed(R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, R.Opts.w(o), R.Item{k1, pos, B.At{1n+sn, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, _) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{k1, pos, B.At{1n, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) : R.RunSt} & {G.inv2(None{}, R.keyed(R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), R.Item{k1, pos, B.At{1n, f0, f1}, String.append(t, B.Line.term(li))}, Nil{}, R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}))) == True{} : Bool}
          kd0(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, R.Opts.w(o), k1, pos, f0, f1, String.append(t, B.Line.term(li)), R.bump(R.Cnt{0n, 0n, 0n, 0n}, Bool.not(String.eq(t, B.Line.body(li))), False{}, False{}), ef0, hg)

# The first line when S's CHROM is not c0: X writes S's buffer and starts
# c0; from there X is lift of T (no phantom image: q = None).
# With -m: a split line has a record.
def pieces_ne(+dfs: B.Defs, +o: B.Opts, +body: String, +hp: {B.Rec.parts(dfs, o, body) == B.Pieces{Nil{}} : B.Parts}) -> Empty:
  +ea = SITE.split_alts(dfs, o, body, Nil{}, hp)
  OI.one_not_pieces(dfs, o, body, Nil{},
    {%ea : {Nat.is_lt(List.length(&2, String, _), 2n) == True{} : Bool}; {==} : {Nat.is_lt(L.n_alts(body), 2n) == True{} : Bool}}, hp)

# The first line of a segment by what -m does with it: its first record as
# bl0.r says, the others as EP.pieces_lift.
def first_ps(+fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, +o: B.Opts, +ps: List<&2, String>, +term: String, +f0: String, +f1: String, +pos: Nat, +ef0: {f0 == c0 : String},
  +hne: {List.is_empty(&2, String, ps) == False{} : Bool},
  +hg: {G.Good(c0, se, sc, L.pieces_in(ps, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, term, B.At{1n, f0, f1}, pos)) == True{} : Bool}) ->
  {L.pieces_in(ps, fa, o, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, term, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.pieces_in(ps, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, term, B.At{1n, f0, f1}, pos)) : R.RunSt}
    & {G.inv2(None{}, L.pieces_in(ps, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, term, B.At{1n, f0, f1}, pos)) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({L.pieces_in(Nil{}, fa, o, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, term, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.pieces_in(Nil{}, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, term, B.At{1n, f0, f1}, pos)) : R.RunSt}
        & {G.inv2(None{}, L.pieces_in(Nil{}, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, term, B.At{1n, f0, f1}, pos)) == True{} : Bool}, P.true_ne_false(hne))
    case Con{+p1, +rest}:
      +s1 = R.body_line(L.judge(fa, p1), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, B.Line{p1, term}, B.At{1n, f0, f1}, pos)
      +s1l = R.body_line(L.judge(fa, p1), R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, B.Line{p1, term}, B.At{1n+sn, f0, f1}, pos)
      +g1 = EP.good_pin(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos, c0, se, sc, hg)
      +eq1 = Pair.fst({s1l == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1) : R.RunSt}, {G.inv2(None{}, s1) == True{} : Bool}, bl0.r(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, L.judge(fa, p1), o, B.Line{p1, term}, f0, f1, pos, ef0, g1))
      +iv1 = Pair.snd({s1l == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1) : R.RunSt}, {G.inv2(None{}, s1) == True{} : Bool}, bl0.r(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, L.judge(fa, p1), o, B.Line{p1, term}, f0, f1, pos, ef0, g1))
      (Equal.trans(R.RunSt, L.pieces_in(rest, fa, o, s1l, term, B.At{1n+sn, f0, f1}, pos), L.pieces_in(rest, fa, o, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1), term, B.At{1n+sn, f0, f1}, pos), G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.pieces_in(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos)),
        Equal.cong(R.RunSt, R.RunSt, zz => L.pieces_in(rest, fa, o, zz, term, B.At{1n+sn, f0, f1}, pos), s1l, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1), eq1),
        Pair.fst({L.pieces_in(rest, fa, o, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1), term, B.At{Nat.add(1n, sn), f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.pieces_in(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos)) : R.RunSt},
          {G.inv2(None{}, L.pieces_in(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos)) == True{} : Bool},
          EP.pieces_lift(rest, sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, c0, se, sc, s1, fa, o, term, 1n, {==}, f0, f1, pos, False{}, {==}, h1, h2, iv1, hg))),
       Pair.snd({L.pieces_in(rest, fa, o, G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, s1), term, B.At{Nat.add(1n, sn), f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.pieces_in(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos)) : R.RunSt},
          {G.inv2(None{}, L.pieces_in(rest, fa, o, s1, term, B.At{1n, f0, f1}, pos)) == True{} : Bool},
          EP.pieces_lift(rest, sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, c0, se, sc, s1, fa, o, term, 1n, {==}, f0, f1, pos, False{}, {==}, h1, h2, iv1, hg)))

def ne_of(+ps: List<&2, String>, +dfs: B.Defs, +o: B.Opts, +body: String, +hp: {B.Rec.parts(dfs, o, body) == B.Pieces{ps} : B.Parts}) -> {List.is_empty(&2, String, ps) == False{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, String, Nil{}) == False{} : Bool}, pieces_ne(dfs, o, body, hp))
    case Con{+x, +t}:
      {==}

def first_un(+fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, +o: B.Opts, +bb: Bool, +cd: B.Code, +li: B.Line, +f0: String, +f1: String, +pos: Nat, +ef0: {f0 == c0 : String},
  +hg: {G.Good(c0, se, sc, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos), R.problem_line(R.Opts.strict(o), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), cd, li, B.At{1n, f0, f1}, pos))) == True{} : Bool}) ->
  {Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, o, li, B.At{1n+sn, f0, f1}, pos), R.problem_line(R.Opts.strict(o), R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, R.Opts.w(o), cd, li, B.At{1n+sn, f0, f1}, pos))
     == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos), R.problem_line(R.Opts.strict(o), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), cd, li, B.At{1n, f0, f1}, pos))) : R.RunSt}
    & {G.inv2(None{}, Bool.pick(R.RunSt, bb, R.body_line(L.judge(fa, B.Line.body(li)), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, o, li, B.At{1n, f0, f1}, pos), R.problem_line(R.Opts.strict(o), R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, R.Opts.w(o), cd, li, B.At{1n, f0, f1}, pos))) == True{} : Bool}:
  match bb:
    case True{}:
      bl0.r(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, L.judge(fa, B.Line.body(li)), o, li, f0, f1, pos, ef0, hg)
    case False{}:
      bl0.r(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, B.Res{B.Problem{cd}, 0n, "", False{}}, o, li, f0, f1, pos, ef0, hg)

def first_pt(+dfs: B.Defs, +fa: List<&2, B.Contig>, +c0: String, +l: Nat, +sn: Nat, +sh: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +sk: R.Cnt, +so: String, +sns: List<&2, B.Note>, +h1: {R.has(c0, se) == False{} : Bool}, +h2: {R.is_cur(sc, c0) == False{} : Bool}, +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}, +o: B.Opts, +pt: B.Parts, +li: B.Line, +f0: String, +f1: String, +pos: Nat, +ef0: {f0 == c0 : String},
  +hpt: {B.Rec.parts(dfs, o, B.Line.body(li)) == pt : B.Parts},
  +hg: {G.Good(c0, se, sc, L.body_in(pt, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}) ->
  {L.body_in(pt, fa, o, R.RunSt{1n+sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, li, B.At{1n+sn, f0, f1}, pos) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.body_in(pt, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, li, B.At{1n, f0, f1}, pos)) : R.RunSt}
    & {G.inv2(None{}, L.body_in(pt, fa, o, R.RunSt{1n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}, li, B.At{1n, f0, f1}, pos)) == True{} : Bool}:
  match pt:
    case B.Whole{}:
      bl0.r(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, L.judge(fa, B.Line.body(li)), o, li, f0, f1, pos, ef0, hg)
    case B.Pieces{+ps}:
      first_ps(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, o, ps, B.Line.term(li), f0, f1, pos, ef0, ne_of(ps, dfs, o, B.Line.body(li), hpt), hg)
    case B.Unsplit{+cd}:
      first_un(fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, o, L.stops(L.judge(fa, B.Line.body(li)), R.Opts.strict(o)), cd, li, f0, f1, pos, ef0, hg)

law first:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +sn: Nat
  for +sh: String
  for +sc: Maybe<&2, String>
  for +se: List<&2, String>
  for +sl: Maybe<&2, R.Item>
  for +sb: List<&2, R.Item>
  for +sk: R.Cnt
  for +so: String
  for +sns: List<&2, B.Note>
  for +li: B.Line
  for +ef0: {B.Rec.field(B.Rec.fields(B.Line.body(li)), 0n) == c0 : String}
  for +h1: {R.has(c0, se) == False{} : Bool}
  for +h2: {R.is_cur(sc, c0) == False{} : Bool}
  for +hs: {S.sorted_from(sb, S.lkey(sl)) == True{} : Bool}
  for hg: {G.Good(c0, se, sc, L.line_step(fa, dfs, o, SD.rs0(c0, l), li)) == True{} : Bool}
  {L.line_step(fa, dfs, o, R.RunSt{sn, True{}, sh, sc, se, sl, sb, sk, so, sns, False{}}, li) == G.lift(sn, sh, R.push_cur(sc, se), String.append(so, L.texts(sb)), sk, sns, None{}, L.line_step(fa, dfs, o, SD.rs0(c0, l), li)) : R.RunSt} & {G.inv2(None{}, L.line_step(fa, dfs, o, SD.rs0(c0, l), li)) == True{} : Bool}

def first(dfs,fa, o, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, li, ef0, h1, h2, hs, hg):
  +fs = B.Rec.fields(B.Line.body(li))
  first_pt(dfs, fa, c0, l, sn, sh, sc, se, sl, sb, sk, so, sns, h1, h2, hs, o, B.Rec.parts(dfs, o, B.Line.body(li)), li, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.pos(fs), ef0, {==}, hg)

