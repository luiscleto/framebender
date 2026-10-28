import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as P

# Phase E (the parallel machine, norm_par.bend): the spec-level definitions
# of the segment lemma (notes/parallel_proofs.md). A task runs a piece's
# lines from rs0, a phantom state; when segok holds, the true run over the
# same lines is shiftS of the two. Each definition mirrors norm_par.bend's
# merge.ok and merge.if on run.bend's states.

# A task's start (norm_par.bend's task.run0 as run.bend's state): in the
# body, CHROM c0, nothing buffered or written, and the phantom as the last
# item written: key and input POS l, line 0.
def rs0(+c0: String, +l: Nat) -> R.RunSt:
  R.RunSt{0n, True{}, "", Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}

# The CHROM of the first line (field 0 of its body, as L.line_in reads it).
def first_chrom(ls: List<&2, B.Line>) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      None{}
    case l <> t:
      Some{B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n)}

# ---------------------------------------------------------------------------
# Items
# ---------------------------------------------------------------------------

def item_shift(+d: Nat, it: R.Item) -> R.Item:
  match it:
    case R.Item{k, p, B.At{ln, c, s}, t}:
      R.Item{k, p, B.At{Nat.add(ln, d), c, s}, t}

# Items with their line numbers moved on by d.
def items_shift(+d: Nat, xs: List<&2, R.Item>) -> List<&2, R.Item>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      item_shift(d, x) <> items_shift(d, t)

# The items' texts, in order.
def texts(xs: List<&2, R.Item>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      String.append(R.Item.text(x), texts(t))

def item_line(it: R.Item) -> Nat:
  match it:
    case R.Item{k, p, B.At{ln, c, s}, t}:
      ln

# The phantom: line 0 (a real item has its line's number, from 1).
def is_phantom(+it: R.Item) -> Bool:
  Nat.is_eq(item_line(it), 0n)

def first_item(xs: List<&2, R.Item>) -> Maybe<&2, R.Item>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      Some{x}

def last_item(xs: List<&2, R.Item>) -> Maybe<&2, R.Item>:
  match xs:
    case Nil{}:
      None{}
    case +x <> t:
      Maybe.or(&2, R.Item, last_item(t), Some{x})

def key_or(m: Maybe<&2, R.Item>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{x}:
      R.Item.key(x)

# The largest key, or m if larger.
def maxkey(xs: List<&2, R.Item>, +m: Nat) -> Nat:
  match xs:
    case Nil{}:
      m
    case +x <> t:
      maxkey(t, Nat.max(m, R.Item.key(x)))

# The largest input POS, or m if larger.
def max_inpos(xs: List<&2, R.Item>, +m: Nat) -> Nat:
  match xs:
    case Nil{}:
      m
    case +x <> t:
      max_inpos(t, Nat.max(m, R.Item.inpos(x)))

def real_inpos.k(ph: Bool, +x: R.Item) -> Nat:
  match ph:
    case True{}:
      0n
    case False{}:
      R.Item.inpos(x)

# The input POS of the last item written (0 for none or the phantom).
def real_inpos(m: Maybe<&2, R.Item>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{+x}:
      real_inpos.k(is_phantom(x), x)

# Every key is at least l.
def keys_ge(xs: List<&2, R.Item>, +l: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(l, R.Item.key(x)) && keys_ge(t, l)

def sorted.go(xs: List<&2, R.Item>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Nat.is_le(k, R.Item.key(x)) && sorted.go(t, R.Item.key(x))

# The keys never go down.
def sorted(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      sorted.go(t, R.Item.key(x))

# No last item, or its key is at most k.
def last_le(m: Maybe<&2, R.Item>, +k: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_le(R.Item.key(x), k)

# ---------------------------------------------------------------------------
# The two runs
# ---------------------------------------------------------------------------

# The CHROMs xs other than c0 are neither among se nor sc.
def chroms_ok(xs: List<&2, String>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      (String.eq(x, c0) || (Bool.not(R.has(x, se)) && Bool.not(R.is_cur(sc, x)))) && chroms_ok(t, c0, se, sc)

def cur_list(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{c}:
      [c]

def cnt_add(a: R.Cnt, b: R.Cnt) -> R.Cnt:
  match a b:
    case R.Cnt{a1, a2, a3, a4} R.Cnt{b1, b2, b3, b4}:
      R.Cnt{Nat.add(a1, b1), Nat.add(a2, b2), Nat.add(a3, b3), Nat.add(a4, b4)}

def last_shift.k(ph: Bool, +x: R.Item, +same: Bool, +sl: Maybe<&2, R.Item>, +elast: Maybe<&2, R.Item>, +d: Nat) -> Maybe<&2, R.Item>:
  match ph same:
    case False{} _:
      Some{item_shift(d, x)}
    case True{} True{}:
      Maybe.or(&2, R.Item, elast, sl)
    case True{} False{}:
      None{}

# T's last item as the true run's: a real one, its line moved on by d; the
# phantom (nothing written in T's first CHROM run) stands for what the true
# run wrote last: the last of S's buffer (all written) or S's last in the
# same CHROM run, nothing after a new one.
def last_shift(+tl: Maybe<&2, R.Item>, +same: Bool, +sl: Maybe<&2, R.Item>, +elast: Maybe<&2, R.Item>, +d: Nat) -> Maybe<&2, R.Item>:
  match tl:
    case None{}:
      None{}
    case Some{+x}:
      last_shift.k(is_phantom(x), x, same, sl, elast, d)

# The true run S followed by T, T run on the same lines from rs0(c0, l): S's
# buffer written first, then T's state, its line numbers moved on by S's;
# ended T's then S's (S's CHROM pushed when T's first line started a new
# CHROM run); the counts added.
def shiftS(+c0: String, +S: R.RunSt, +T: R.RunSt) -> R.RunSt:
  match S T:
    case R.RunSt{+sn, si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, sx} R.RunSt{+tn, ti, th, +tc, +te, +tl, +tb, +tk, +to, tns, tx}:
      +same = R.is_cur(sc, c0)
      R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))), last_shift(tl, same, sl, last_item(sb), sn), items_shift(sn, tb), cnt_add(sk, tk), String.append(so, String.append(texts(sb), to)), sns, False{}}

def segok.k(+w: Nat, +c0: String, +l: Nat, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, R.Item>, +sb: List<&2, R.Item>, +si: Bool, +sx: Bool, +tn: Nat, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, R.Item>, +tb: List<&2, R.Item>, +tns: List<&2, B.Note>, +tx: Bool) -> Bool:
  +same = R.is_cur(sc, c0)
  +eempty = List.is_empty(&2, R.Item, sb)
  +maxe = maxkey(sb, key_or(sl, 0n))
  +changed = Bool.not(List.is_empty(&2, String, te))
  +mlow = max_inpos(tb, Bool.pick(Nat, changed, 0n, real_inpos(tl)))
  si && Bool.not(sx) && Bool.not(tx) && List.is_empty(&2, B.Note, tns) && Nat.is_lt(0n, tn) && Bool.not(R.has(c0, se)) && chroms_ok(List.append(&2, String, cur_list(tc), te), c0, se, sc) && sorted(sb) && (eempty || last_le(sl, key_or(first_item(sb), 0n))) && (Bool.not(same) || (Nat.is_le(maxe, l) && (changed || (keys_ge(tb, l) && (eempty || Nat.is_le(Nat.add(maxe, w), mlow))))))

# When the segment lemma applies (norm_par.bend's merge.ok on run.bend's
# states; S: the true run, T: the task's).
def segok(+w: Nat, +c0: String, +l: Nat, +S: R.RunSt, +T: R.RunSt) -> Bool:
  match S T:
    case R.RunSt{sn, +si, sh, +sc, +se, +sl, +sb, sk, so, sns, +sx} R.RunSt{+tn, ti, th, +tc, +te, +tl, +tb, tk, to, +tns, +tx}:
      segok.k(w, c0, l, sc, se, sl, sb, si, sx, tn, tc, te, tl, tb, tns, tx)
