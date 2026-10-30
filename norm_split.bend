import Base
import ./types.bend as B
import ./norm_run.bend as NR
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-fields@0.1.0.0/fields.bend as FC

# framebender: splitting a multiallelic record on its bytes (code, not spec).
# With -m, a body line whose ALT field has a comma is split here without
# decoding it: one record per ALT, as types.bend's B.Rec.parts writes them,
# each followed by the line's terminator, in a buffer of their own. The
# machine reads that buffer as lines (norm_seq.bend). Any doubt (a line
# B.Rec.parts would refuse or leave Whole, a size past the buffers' bounds)
# gives None, and the line takes the String path, which calls B.Rec.parts
# itself. notes/split.md has the design and the refinement argument.
#
# One pass over the line cuts its fields and reads what does not depend on
# the ALT: the ALTs, each INFO entry's and each FORMAT key's Number
# (B.Tags.find on the key's text). Then each record is written from the
# line's bytes: CHROM .. REF, its ALT, QUAL and FILTER, INFO with each
# per-allele value cut (B.Vals.split), FORMAT, and each sample with its
# genotype rewritten (B.Gt.split) and its per-allele values cut.
#
# Loops: a step (not recursive) on a state, driven by a fuel loop that stops
# when the state says it is done (fuel: one more than the bytes scanned).

# ---------------------------------------------------------------------------
# Ranges
# ---------------------------------------------------------------------------

# Bytes a .. z-1 of the line.
type Rg is Data:
  Rg{a: U32, z: U32}

def Rg.a(x: Rg) -> U32:
  match x:
    case Rg{a, z}:
      a

def Rg.z(x: Rg) -> U32:
  match x:
    case Rg{a, z}:
      z

def fuel(x: Rg) -> Nat:
  match x:
    case Rg{+a, +z}:
      1n+U32.to_nat((z - a : U32))

def rev_rg(xs: List<&2, Rg>, acc: List<&2, Rg>) -> List<&2, Rg>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_rg(t, x <> acc)

# ---------------------------------------------------------------------------
# Cutting at a separator (String.split on bytes)
# ---------------------------------------------------------------------------

# lawful-fields' cut (FC.cut: the end offsets of the first n pieces of
# from .. to-1 split at sep) with fast.bend's find, which is the same function
# on a well-formed buffer (proof_s_cut.bend).
def cut.next(want: Bool, b: D.Bytes, +from: U32, +to: U32, +sep: U32) -> D.Bytes & U32:
  match want:
    case True{}:
      F.find(b, from, to, sep)
    case False{}:
      (b, to)

def cut.go(+n: Nat, more: Bool, r: D.Bytes & U32, +to: U32, +sep: U32) -> D.Bytes & List<&2, U32>:
  match n more:
    case 0n _:
      (b, e) = r
      (b, Nil{})
    case 1n+m False{}:
      (b, e) = r
      (b, Nil{})
    case 1n+m True{}:
      (b, +e) = r
      +go = U32.is_lt(e, to)
      FC.cut.cons(e, cut.go(m, go, cut.next(go && Bool.not(Nat.is_eq(m, 0n)), b, (e + 1 : U32), to, sep), to, sep))

def cut.ends(b: D.Bytes, +from: U32, +to: U32, +sep: U32, +n: Nat) -> D.Bytes & List<&2, U32>:
  cut.go(n, True{}, cut.next(Bool.not(Nat.is_eq(n, 0n)), b, from, to, sep), to, sep)

# The ranges between ends es, the first starting at a.
def rgs(es: List<&2, U32>, +a: U32) -> List<&2, Rg>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Rg{a, e} <> rgs(t, (e + 1 : U32))

def cut.k(+a: U32, r: D.Bytes & List<&2, U32>) -> D.Bytes & List<&2, Rg>:
  (b, es) = r
  (b, rgs(es, a))

# The ranges between the bytes c in x (one more than the c's in it).
def cut(b: D.Bytes, x: Rg, +c: U32) -> D.Bytes & List<&2, Rg>:
  match x:
    case Rg{+a, +z}:
      cut.k(a, cut.ends(b, a, z, c, 1n+U32.to_nat((z - a : U32))))

# How many bytes c in x.
type Cn is Type:
  Cn{b: D.Bytes, a: U32, z: U32, c: U32, k: Nat, done: Bool}

def count.if(end: Bool, b: D.Bytes, +j: U32, +z: U32, +c: U32, +k: Nat) -> Cn:
  match end:
    case True{}:
      Cn{b, j, z, c, k, True{}}
    case False{}:
      Cn{b, (j + 1 : U32), z, c, 1n+k, False{}}

def count.next(r: D.Bytes & U32, +z: U32, +c: U32, +k: Nat) -> Cn:
  (b, +j) = r
  count.if(U32.is_eq(j, z), b, j, z, c, k)

def count.loop(n: Nat, x: Cn) -> Cn:
  match n x:
    case 0n x:
      x
    case 1n+m Cn{b, a, z, c, k, True{}}:
      Cn{b, a, z, c, k, True{}}
    case 1n+m Cn{b, +a, +z, +c, +k, False{}}:
      count.loop(m, count.next(F.find(b, a, z, c), z, c, k))

def count.fin(x: Cn) -> D.Bytes & Nat:
  match x:
    case Cn{b, a, z, c, k, d}:
      (b, k)

def count(b: D.Bytes, x: Rg, +c: U32) -> D.Bytes & Nat:
  match x:
    case Rg{+a, +z}:
      count.fin(count.loop(1n+U32.to_nat((z - a : U32)), Cn{b, a, z, c, 0n, False{}}))

# ---------------------------------------------------------------------------
# Byte tests
# ---------------------------------------------------------------------------

# x is exactly the one byte c.
def is1.k(+c: U32, r: D.Bytes & U32) -> D.Bytes & Bool:
  (b, +x) = r
  (b, U32.is_eq(x, c))

def is1.if(one: Bool, b: D.Bytes, +a: U32, +c: U32) -> D.Bytes & Bool:
  match one:
    case True{}:
      is1.k(c, BY.at(b, a))
    case False{}:
      (b, False{})

def is1(b: D.Bytes, x: Rg, +c: U32) -> D.Bytes & Bool:
  match x:
    case Rg{+a, +z}:
      is1.if(U32.is_eq((z - a : U32), 1), b, a, c)

# A letter A-Z, a-z (as Char.is_letter).
def letter(+x: U32) -> Bool:
  (U32.is_ge(x, 65) && U32.is_le(x, 90)) || (U32.is_ge(x, 97) && U32.is_le(x, 122))

# Every byte of a .. z-1 so far is a letter.
type Ev is Type:
  Ev{b: D.Bytes, j: U32, z: U32, ok: Bool, done: Bool}

def letters.if(ok: Bool, b: D.Bytes, +j: U32, +z: U32) -> Ev:
  match ok:
    case True{}:
      Ev{b, (j + 1 : U32), z, True{}, U32.is_eq((j + 1 : U32), z)}
    case False{}:
      Ev{b, j, z, False{}, True{}}

def letters.next(r: D.Bytes & U32, +j: U32, +z: U32) -> Ev:
  (b, +x) = r
  letters.if(letter(x), b, j, z)

def letters.loop(n: Nat, x: Ev) -> Ev:
  match n x:
    case 0n x:
      x
    case 1n+m Ev{b, j, z, ok, True{}}:
      Ev{b, j, z, ok, True{}}
    case 1n+m Ev{b, +j, +z, ok, False{}}:
      letters.loop(m, letters.next(BY.at(b, j), j, z))

def letters.fin(x: Ev) -> D.Bytes & Bool:
  match x:
    case Ev{b, j, z, ok, d}:
      (b, ok)

# x is one or more letters (B.Text.is_letters).
def letters(b: D.Bytes, x: Rg) -> D.Bytes & Bool:
  match x:
    case Rg{+a, +z}:
      letters.fin(letters.loop(1n+U32.to_nat((z - a : U32)), Ev{b, a, z, U32.is_lt(a, z), U32.is_le(z, a)}))

# A byte in upper case (a-z as A-Z, as Char.to_upper).
def up(+x: U32) -> U32:
  Bool.pick(U32, U32.is_ge(x, 97) && U32.is_le(x, 122), (x - 32 : U32), x)

# Bytes i, j, i+1, j+1, ... equal in upper case for n more bytes.
type Sc is Type:
  Sc{b: D.Bytes, i: U32, j: U32, left: U32, ok: Bool}

def same_ci.next(r: D.Bytes & (U32 & U32), +i: U32, +j: U32, +left: U32) -> Sc:
  (b, q) = r
  (x, y) = q
  Sc{b, (i + 1 : U32), (j + 1 : U32), (left - 1 : U32), U32.is_eq(up(x), up(y))}

# Nothing left: done (ok stays True and the loop runs out with no change).
def same_ci.go(end: Bool, b: D.Bytes, +i: U32, +j: U32, +left: U32) -> Sc:
  match end:
    case True{}:
      Sc{b, i, j, left, True{}}
    case False{}:
      same_ci.next(BY.at2(b, i, j), i, j, left)

def same_ci.loop(n: Nat, x: Sc) -> Sc:
  match n x:
    case 0n x:
      x
    case 1n+m Sc{b, i, j, left, False{}}:
      Sc{b, i, j, left, False{}}
    case 1n+m Sc{b, +i, +j, +left, True{}}:
      same_ci.loop(m, same_ci.go(U32.is_zero(left), b, i, j, left))

def same_ci.fin(x: Sc) -> D.Bytes & Bool:
  match x:
    case Sc{b, i, j, left, ok}:
      (b, ok)

# Two ranges hold the same text up to case (String.eq of String.to_upper).
def same_ci(b: D.Bytes, x: Rg, y: Rg) -> D.Bytes & Bool:
  match x y:
    case Rg{+a, +z} Rg{+c, +e}:
      same_ci.fin(same_ci.loop(1n+U32.to_nat((z - a : U32)), Sc{b, a, c, (z - a : U32), U32.is_eq((z - a : U32), (e - c : U32))}))

def member_ci.if(hit: Bool, b: D.Bytes, +x: Rg, y: Rg) -> D.Bytes & Bool:
  match hit:
    case True{}:
      (b, True{})
    case False{}:
      same_ci(b, x, y)

def member_ci.step(r: D.Bytes & Bool, +x: Rg, y: Rg) -> D.Bytes & Bool:
  (b, hit) = r
  member_ci.if(hit, b, x, y)

def member_ci(xs: List<&2, Rg>, r: D.Bytes & Bool, +x: Rg) -> D.Bytes & Bool:
  match xs:
    case Nil{}:
      r
    case y <> t:
      member_ci(t, member_ci.step(r, x, y), x)

def distinct.k(ok: Bool, r: D.Bytes & Bool) -> D.Bytes & Bool:
  (b, hit) = r
  (b, ok && Bool.not(hit))

def distinct.step(r: D.Bytes & Bool, +x: Rg, t: List<&2, Rg>) -> D.Bytes & Bool:
  (b, ok) = r
  distinct.k(ok, member_ci(t, (b, False{}), x))

# No two ranges hold the same text up to case (B.Alts.distinct).
def distinct(xs: List<&2, Rg>, r: D.Bytes & Bool) -> D.Bytes & Bool:
  match xs:
    case Nil{}:
      r
    case +x <> +t:
      distinct(t, distinct.step(r, x, t))

# The bytes of x as text (one Char per byte).
def txt.k(r: D.Bytes & List<&2, U32>) -> D.Bytes & String:
  (b, xs) = r
  (b, NR.chars(xs))

def txt(b: D.Bytes, x: Rg) -> D.Bytes & String:
  match x:
    case Rg{+a, +z}:
      txt.k(BY.to_list(b, a, (z - a : U32)))

# ---------------------------------------------------------------------------
# What the line holds, read once
# ---------------------------------------------------------------------------

# An INFO entry x: kept as it is (a flag, an empty entry, a tag of Number
# Other), or its values v cut by Number num; Bad: B.Rec.parts refuses it.
type Ik is Data:
  IKeep{x: Rg}
  IVal{x: Rg, v: Rg, num: B.Num}
  IBad{}

# A FORMAT key: GT, kept, cut by Number num, or one B.Rec.parts refuses a
# value of.
type Fk is Data:
  KGt{}
  KKeep{}
  KVal{num: B.Num}
  KBad{}

def ikind.num(m: Maybe<&2, B.Num>, +x: Rg, +v: Rg) -> Ik:
  match m:
    case None{}:
      IBad{}
    case Some{B.NumUnknown{}}:
      IBad{}
    case Some{B.NumOther{}}:
      IKeep{x}
    case Some{num}:
      IVal{x, v, num}

def ikind.v(noval: Bool, +x: Rg, +j: U32, +m: Maybe<&2, B.Num>) -> Ik:
  match noval:
    case True{}:
      Bool.pick(Ik, B.Num.per_allele(m), IBad{}, IKeep{x})
    case False{}:
      ikind.num(m, x, Rg{(j + 1 : U32), Rg.z(x)})

def ikind.k(+x: Rg, +j: U32, r: D.Bytes & String, +tags: List<&2, B.Tag>) -> D.Bytes & Ik:
  (b, +k) = r
  (b, ikind.v(U32.is_eq(Rg.z(x), j), x, j, B.Tags.find(tags, k)))

def ikind.at(+x: Rg, r: D.Bytes & U32, +tags: List<&2, B.Tag>) -> D.Bytes & Ik:
  (b, +j) = r
  ikind.k(x, j, txt(b, Rg{Rg.a(x), j}), tags)

# An entry's kind: its key is the text before its first '=' (B.Info.key).
def ikind(b: D.Bytes, +x: Rg, +tags: List<&2, B.Tag>) -> D.Bytes & Ik:
  ikind.at(x, F.find(b, Rg.a(x), Rg.z(x), 61), tags)

def ikinds.cons(r: D.Bytes & Ik, acc: List<&2, Ik>) -> D.Bytes & List<&2, Ik>:
  (b, k) = r
  (b, k <> acc)

def ikinds.step(r: D.Bytes & List<&2, Ik>, +x: Rg, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Ik>:
  (b, acc) = r
  ikinds.cons(ikind(b, x, tags), acc)

def rev_ik(xs: List<&2, Ik>, acc: List<&2, Ik>) -> List<&2, Ik>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_ik(t, x <> acc)

# The kinds of entries xs (r: the kinds so far, last first).
def ikinds.go(xs: List<&2, Rg>, r: D.Bytes & List<&2, Ik>, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Ik>:
  match xs:
    case Nil{}:
      r
    case +x <> t:
      ikinds.go(t, ikinds.step(r, x, tags), tags)

def ikinds.fin(r: D.Bytes & List<&2, Ik>) -> D.Bytes & List<&2, Ik>:
  (b, acc) = r
  (b, rev_ik(acc, Nil{}))

def ikinds(xs: List<&2, Rg>, b: D.Bytes, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Ik>:
  ikinds.fin(ikinds.go(xs, (b, Nil{}), tags))

def fkind.num(m: Maybe<&2, B.Num>) -> Fk:
  match m:
    case None{}:
      KBad{}
    case Some{B.NumUnknown{}}:
      KBad{}
    case Some{B.NumOther{}}:
      KKeep{}
    case Some{num}:
      KVal{num}

def fkind.k(r: D.Bytes & String, +tags: List<&2, B.Tag>) -> D.Bytes & Fk:
  (b, +k) = r
  (b, Bool.pick(Fk, String.eq(k, "GT"), KGt{}, fkind.num(B.Tags.find(tags, k))))

def fkinds.cons(r: D.Bytes & Fk, acc: List<&2, Fk>) -> D.Bytes & List<&2, Fk>:
  (b, k) = r
  (b, k <> acc)

def fkinds.step(r: D.Bytes & List<&2, Fk>, +x: Rg, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Fk>:
  (b, acc) = r
  fkinds.cons(fkind.k(txt(b, x), tags), acc)

def rev_fk(xs: List<&2, Fk>, acc: List<&2, Fk>) -> List<&2, Fk>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_fk(t, x <> acc)

def fkinds.go(xs: List<&2, Rg>, r: D.Bytes & List<&2, Fk>, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Fk>:
  match xs:
    case Nil{}:
      r
    case +x <> t:
      fkinds.go(t, fkinds.step(r, x, tags), tags)

def fkinds.fin(r: D.Bytes & List<&2, Fk>) -> D.Bytes & List<&2, Fk>:
  (b, acc) = r
  (b, rev_fk(acc, Nil{}))

def fkinds(xs: List<&2, Rg>, b: D.Bytes, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Fk>:
  fkinds.fin(fkinds.go(xs, (b, Nil{}), tags))

# ---------------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------------

# The line, the records written so far (o, then the line's bytes p.a .. p.z-1
# not copied yet: copies that follow each other in the line are made as one),
# and whether all went well (once ok is False nothing more is written and
# the line takes the String path).
type Sw is Type:
  Sw{b: D.Bytes, o: D.Bytes, p: Rg, ok: Bool}

def Sw.fail(w: Sw) -> Sw:
  match w:
    case Sw{b, o, p, ok}:
      Sw{b, o, p, False{}}

def small.k(+k: U32, r: D.Bytes & U32) -> D.Bytes & Bool:
  (o, +l) = r
  (o, U32.is_le(l, 536870912) && U32.is_le(k, 268435456))

def flush.fin(r: D.Bytes & D.Bytes, +z: U32) -> Sw:
  (o, b) = r
  Sw{b, o, Rg{z, z}, True{}}

def flush.ok(ok: Bool, b: D.Bytes, o: D.Bytes, +a: U32, +z: U32) -> Sw:
  match ok:
    case True{}:
      flush.fin(NR.put_bytes(o, b, a, (z - a : U32)), z)
    case False{}:
      Sw{b, o, Rg{a, z}, False{}}

def flush.k(b: D.Bytes, +a: U32, +z: U32, r: D.Bytes & Bool) -> Sw:
  (o, ok) = r
  flush.ok(ok, b, o, a, z)

def flush.if(empty: Bool, b: D.Bytes, o: D.Bytes, +a: U32, +z: U32) -> Sw:
  match empty:
    case True{}:
      Sw{b, o, Rg{a, z}, True{}}
    case False{}:
      flush.k(b, a, z, small.k((z - a : U32), BY.len(o)))

# The bytes not copied yet are copied (while the output holds at most 2^29
# bytes and they are at most 2^28).
def flush(w: Sw) -> Sw:
  match w:
    case Sw{b, o, Rg{+a, +z}, True{}}:
      flush.if(U32.is_le(z, a), b, o, a, z)
    case Sw{b, o, p, False{}}:
      Sw{b, o, p, False{}}

def Sw.with_p(w: Sw, +x: Rg) -> Sw:
  match w:
    case Sw{b, o, p, ok}:
      Sw{b, o, x, ok}

def cpr.if(next: Bool, w: Sw, +a: U32, +x: Rg) -> Sw:
  match next:
    case True{}:
      Sw.with_p(w, Rg{a, Rg.z(x)})
    case False{}:
      Sw.with_p(flush(w), x)

# The line's bytes x added: they extend the bytes not copied yet if they
# follow them in the line.
def cpr(w: Sw, +x: Rg) -> Sw:
  match w:
    case Sw{b, o, Rg{+a, +z}, True{}}:
      cpr.if(U32.is_eq(Rg.a(x), z), Sw{b, o, Rg{a, z}, True{}}, a, x)
    case Sw{b, o, p, False{}}:
      Sw{b, o, p, False{}}

def push.ok(ok: Bool, b: D.Bytes, o: D.Bytes, +z: U32, +x: U32) -> Sw:
  match ok:
    case True{}:
      Sw{b, BY.push(NR.room(o, 1), x), Rg{z, z}, True{}}
    case False{}:
      Sw{b, o, Rg{z, z}, False{}}

def push.k(b: D.Bytes, +z: U32, +x: U32, r: D.Bytes & Bool) -> Sw:
  (o, ok) = r
  push.ok(ok, b, o, z, x)

def push(w: Sw, +x: U32) -> Sw:
  match w:
    case Sw{b, o, Rg{a, +z}, True{}}:
      push.k(b, z, x, small.k(1, BY.len(o)))
    case Sw{b, o, p, False{}}:
      Sw{b, o, p, False{}}

def ch.if(same: Bool, b: D.Bytes, o: D.Bytes, +a: U32, +z: U32, +x: U32) -> Sw:
  match same:
    case True{}:
      Sw{b, o, Rg{a, (z + 1 : U32)}, True{}}
    case False{}:
      push(flush(Sw{b, o, Rg{a, z}, True{}}), x)

def ch.at(r: D.Bytes & U32, o: D.Bytes, +a: U32, +z: U32, +x: U32) -> Sw:
  (b, +y) = r
  ch.if(U32.is_eq(y, x), b, o, a, z, x)

def ch.in(inside: Bool, b: D.Bytes, o: D.Bytes, +a: U32, +z: U32, +x: U32) -> Sw:
  match inside:
    case True{}:
      ch.at(BY.at(b, z), o, a, z, x)
    case False{}:
      push(flush(Sw{b, o, Rg{a, z}, True{}}), x)

def ch.len(r: D.Bytes & U32, o: D.Bytes, +a: U32, +z: U32, +x: U32) -> Sw:
  (b, +len) = r
  ch.in(U32.is_lt(z, len), b, o, a, z, x)

# One byte x added: if the line's next byte (after those not copied yet) is
# x, it is taken from the line.
def ch(w: Sw, +x: U32) -> Sw:
  match w:
    case Sw{b, o, Rg{+a, +z}, True{}}:
      ch.len(BY.len(b), o, a, z, x)
    case Sw{b, o, p, False{}}:
      Sw{b, o, p, False{}}

# A separator before every item but the first.
def sep(w: Sw, first: Bool, +x: U32) -> Sw:
  match first:
    case True{}:
      w
    case False{}:
      ch(w, x)

# ---------------------------------------------------------------------------
# Per-allele values (B.Vals.split)
# ---------------------------------------------------------------------------

# Looking for value j (0: the first) among the values of x, separated by ','.
type Nt is Type:
  Nt{b: D.Bytes, a: U32, z: U32, j: Nat, r: Rg, done: Bool}

def nth.next(r: D.Bytes & U32, +a: U32, +z: U32, j: Nat) -> Nt:
  (b, +e) = r
  match j:
    case 0n:
      Nt{b, a, z, 0n, Rg{a, e}, True{}}
    case 1n+k:
      Nt{b, (e + 1 : U32), z, k, Rg{a, e}, U32.is_eq(e, z)}

def nth.loop(n: Nat, x: Nt) -> Nt:
  match n x:
    case 0n x:
      x
    case 1n+m Nt{b, a, z, j, r, True{}}:
      Nt{b, a, z, j, r, True{}}
    case 1n+m Nt{b, +a, +z, j, r, False{}}:
      nth.loop(m, nth.next(F.find(b, a, z, 44), a, z, j))

def nth.fin(x: Nt) -> D.Bytes & Rg:
  match x:
    case Nt{b, a, z, j, r, d}:
      (b, r)

def nth(b: D.Bytes, x: Rg, +j: Nat) -> D.Bytes & Rg:
  match x:
    case Rg{+a, +z}:
      nth.fin(nth.loop(1n+U32.to_nat((z - a : U32)), Nt{b, a, z, j, Rg{a, a}, False{}}))

def pick.w(r: D.Bytes & Rg, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  (b, +y) = r
  cpr(Sw{b, o, p, ok}, y)

def pick.if(inside: Bool, w: Sw, +x: Rg, +j: Nat) -> Sw:
  match inside:
    case True{}:
      match w:
        case Sw{b, o, +p, ok}:
          pick.w(nth(b, x, j), o, p, ok)
    case False{}:
      Sw.fail(w)

# Value j of x (which has k + 1 values) added.
def pick(w: Sw, +x: Rg, +k: Nat, +j: Nat) -> Sw:
  pick.if(Nat.is_le(j, k), w, x, j)

# The values whose places are js, separated by ','.
def picks(js: List<&2, Nat>, w: Sw, +x: Rg, +k: Nat, first: Bool) -> Sw:
  match js:
    case Nil{}:
      w
    case +j <> t:
      picks(t, pick(sep(w, first, 44), x, k, j), x, k, False{})

def vals.fit(ok: Bool, w: Sw, js: List<&2, Nat>, +x: Rg, +k: Nat) -> Sw:
  match ok:
    case True{}:
      picks(js, w, x, k, True{})
    case False{}:
      Sw.fail(w)

def vals.c(+num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +x: Rg, r: D.Bytes & Nat, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  (b, +k) = r
  +q = B.Vals.copies(cp, n, 1n+k)
  vals.fit(B.Vals.fits(B.Vals.expected_count(num, n, q), 1n+k), Sw{b, o, p, ok}, B.Vals.idx(num, q, i), x, k)

def vals.dot(dot: Bool, +num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +x: Rg, b: D.Bytes, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  match dot:
    case True{}:
      ch(Sw{b, o, p, ok}, 46)
    case False{}:
      vals.c(num, n, cp, i, x, count(b, x, 44), o, p, ok)

def vals.k(+num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +x: Rg, r: D.Bytes & Bool, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  (b, dot) = r
  vals.dot(dot, num, n, cp, i, x, b, o, p, ok)

# A per-allele value x in the record for ALT i of n, for the copies cp
# (B.Vals.split: '.' stays '.'; else the count must fit, and the values of
# B.Vals.idx are kept).
def vals(w: Sw, +num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +x: Rg) -> Sw:
  match w:
    case Sw{b, o, +p, ok}:
      vals.k(num, n, cp, i, x, is1(b, x, 46), o, p, ok)

# ---------------------------------------------------------------------------
# Genotypes (B.Gt.split)
# ---------------------------------------------------------------------------

# The allele written: 48 '0', 49 '1', 46 '.' (B.Gt.show of B.Gt.rule).
def rule(+over0: Bool, +i: Nat, +a: U32) -> U32:
  Bool.pick(U32, U32.is_zero(a), 48,
  Bool.pick(U32, Nat.is_eq(U32.to_nat(a), i), 49,
  Bool.pick(U32, over0, 48, 46)))

def tok.le(le: Bool, +over0: Bool, +i: Nat, +v: U32, w: Sw) -> Sw:
  match le:
    case True{}:
      ch(w, rule(over0, i, v))
    case False{}:
      Sw.fail(w)

def tok.z(zero: Bool, +over0: Bool, +n: Nat, +i: Nat, +v: U32, w: Sw) -> Sw:
  match zero:
    case True{}:
      Sw.fail(w)
    case False{}:
      tok.le(Nat.is_le(U32.to_nat(v), n), over0, i, v, w)

def tok.m(m: Maybe<&2, U32>, zero: Bool, +over0: Bool, +n: Nat, +i: Nat, w: Sw) -> Sw:
  match m:
    case Some{+v}:
      tok.z(zero, over0, n, i, v, w)
    case None{}:
      Sw.fail(w)

def tok.d(r: D.Bytes & Maybe<&2, U32>, zero: Bool, +over0: Bool, +n: Nat, +i: Nat, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  (b, m) = r
  tok.m(m, zero, over0, n, i, Sw{b, o, p, ok})

def tok.digit(digit: Bool, +over0: Bool, +n: Nat, +i: Nat, +v: U32, w: Sw) -> Sw:
  match digit:
    case True{}:
      tok.le(Nat.is_le(U32.to_nat(v), n), over0, i, v, w)
    case False{}:
      Sw.fail(w)

def tok.one1(dot: Bool, digit: Bool, +over0: Bool, +n: Nat, +i: Nat, +x: U32, w: Sw) -> Sw:
  match dot:
    case True{}:
      ch(w, 46)
    case False{}:
      tok.digit(digit, over0, n, i, (x - 48 : U32), w)

# Two or more bytes: a number (below 2^32) whose first digit is not 0.
def tok.many(one: Bool, +over0: Bool, +n: Nat, +i: Nat, +a: U32, +z: U32, +x: U32, b: D.Bytes, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  match one:
    case True{}:
      tok.one1(U32.is_eq(x, 46), U32.is_ge(x, 48) && U32.is_le(x, 57), over0, n, i, x, Sw{b, o, p, ok})
    case False{}:
      tok.d(FC.num(b, a, z), U32.is_eq(x, 48), over0, n, i, o, p, ok)

def tok.x(+over0: Bool, +n: Nat, +i: Nat, +a: U32, +z: U32, r: D.Bytes & U32, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  (b, +x) = r
  tok.many(U32.is_eq((z - a : U32), 1), over0, n, i, a, z, x, b, o, p, ok)

def tok.e(empty: Bool, +over0: Bool, +n: Nat, +i: Nat, +a: U32, +z: U32, b: D.Bytes, o: D.Bytes, +p: Rg, ok: Bool) -> Sw:
  match empty:
    case True{}:
      Sw{b, o, p, False{}}
    case False{}:
      tok.x(over0, n, i, a, z, BY.at(b, a), o, p, ok)

# One allele a .. z-1 of a genotype (B.Gt.allele): '.' alone; else digits,
# no leading zero, a number at most n.
def tok(w: Sw, +over0: Bool, +n: Nat, +i: Nat, +a: U32, +z: U32) -> Sw:
  match w:
    case Sw{b, o, +p, ok}:
      tok.e(U32.is_le(z, a), over0, n, i, a, z, b, o, p, ok)

# A genotype being rewritten: the next allele starts at a.
type Gs is Type:
  Gs{w: Sw, a: U32, z: U32, done: Bool}

def gt.if(end: Bool, +over0: Bool, +n: Nat, +i: Nat, +a: U32, +e: U32, +z: U32, w: Sw) -> Gs:
  match end:
    case True{}:
      Gs{tok(w, over0, n, i, a, z), a, z, True{}}
    case False{}:
      Gs{cpr(tok(w, over0, n, i, a, e), Rg{e, (e + 1 : U32)}), (e + 1 : U32), z, False{}}

def gt.next(+over0: Bool, +n: Nat, +i: Nat, +a: U32, +z: U32, r: D.Bytes & U32, o: D.Bytes, +p: Rg, ok: Bool) -> Gs:
  (b, +e) = r
  gt.if(U32.is_eq(e, z), over0, n, i, a, e, z, Sw{b, o, p, ok})

def gt.step(+over0: Bool, +n: Nat, +i: Nat, w: Sw, +a: U32, +z: U32) -> Gs:
  match w:
    case Sw{b, o, +p, ok}:
      gt.next(over0, n, i, a, z, F.find2(b, a, z, 47, 124), o, p, ok)

def gt.loop(k: Nat, x: Gs, +over0: Bool, +n: Nat, +i: Nat) -> Gs:
  match k x:
    case 0n x:
      x
    case 1n+m Gs{w, a, z, True{}}:
      Gs{w, a, z, True{}}
    case 1n+m Gs{w, +a, +z, False{}}:
      gt.loop(m, gt.step(over0, n, i, w, a, z), over0, n, i)

def gt.fin(x: Gs) -> Sw:
  match x:
    case Gs{w, a, z, d}:
      w

# A genotype x in the record for ALT i of n: each allele between '/' and '|'
# rewritten (tok), the separators copied.
def gt(w: Sw, +over0: Bool, +n: Nat, +i: Nat, x: Rg) -> Sw:
  match x:
    case Rg{+a, +z}:
      gt.fin(gt.loop(1n+U32.to_nat((z - a : U32)), Gs{w, a, z, False{}}, over0, n, i))

# A sample's copies (B.Gt.copies of its first GT value, B.Fmt.gt): '.', None;
# else one plus its separators; Some{2} without a GT value.
def copies.n(+k: Nat, r: D.Bytes & Nat) -> D.Bytes & Maybe<&2, Nat>:
  (b, +l) = r
  (b, Some{1n+Nat.add(k, l)})

def copies.c(r: D.Bytes & Nat, +x: Rg) -> D.Bytes & Maybe<&2, Nat>:
  (b, +k) = r
  copies.n(k, count(b, x, 124))

def copies.dot(dot: Bool, b: D.Bytes, +x: Rg) -> D.Bytes & Maybe<&2, Nat>:
  match dot:
    case True{}:
      (b, None{})
    case False{}:
      copies.c(count(b, x, 47), x)

def copies.v(r: D.Bytes & Bool, +x: Rg) -> D.Bytes & Maybe<&2, Nat>:
  (b, dot) = r
  copies.dot(dot, b, x)

def copies(ks: List<&2, Fk>, vs: List<&2, Rg>, b: D.Bytes) -> D.Bytes & Maybe<&2, Nat>:
  match ks vs:
    case KGt{} <> kt +v <> vt:
      copies.v(is1(b, v, 46), v)
    case k <> kt v <> vt:
      copies(kt, vt, b)
    case _ _:
      (b, Some{2n})

# ---------------------------------------------------------------------------
# A record
# ---------------------------------------------------------------------------

def info.one(w: Sw, k: Ik, +n: Nat, +i: Nat) -> Sw:
  match k:
    case IKeep{+x}:
      cpr(w, x)
    case IVal{+x, +v, +num}:
      vals(cpr(w, Rg{Rg.a(x), Rg.a(v)}), num, n, Some{2n}, i, v)
    case IBad{}:
      Sw.fail(w)

def info.go(ks: List<&2, Ik>, w: Sw, +n: Nat, +i: Nat, first: Bool) -> Sw:
  match ks:
    case Nil{}:
      w
    case k <> t:
      info.go(t, info.one(sep(w, first, 59), k, n, i), n, i, False{})

def fmt.one(w: Sw, k: Fk, +over0: Bool, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +x: Rg) -> Sw:
  match k:
    case KGt{}:
      gt(w, over0, n, i, x)
    case KKeep{}:
      cpr(w, x)
    case KVal{num}:
      vals(w, num, n, cp, i, x)
    case KBad{}:
      Sw.fail(w)

def fmt.go(ks: List<&2, Fk>, vs: List<&2, Rg>, w: Sw, +over0: Bool, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, first: Bool) -> Sw:
  match ks vs:
    case _ Nil{}:
      w
    case k <> kt +v <> vt:
      fmt.go(kt, vt, fmt.one(sep(w, first, 58), k, over0, n, cp, i, v), over0, n, cp, i, False{})
    case Nil{} v <> vt:
      Sw.fail(w)

def sample.cp(+ks: List<&2, Fk>, +vs: List<&2, Rg>, r: D.Bytes & Maybe<&2, Nat>, o: D.Bytes, +p: Rg, ok: Bool, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  (b, +cp) = r
  fmt.go(ks, vs, Sw{b, o, p, ok}, over0, n, cp, i, True{})

def sample.k(+ks: List<&2, Fk>, r: D.Bytes & List<&2, Rg>, o: D.Bytes, +p: Rg, ok: Bool, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  (b, +vs) = r
  sample.cp(ks, vs, copies(ks, vs, b), o, p, ok, over0, n, i)

# One sample's column x in the record for ALT i (B.Fmt.split).
def sample(w: Sw, +ks: List<&2, Fk>, +x: Rg, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  match w:
    case Sw{b, o, +p, ok}:
      sample.k(ks, cut(b, x, 58), o, p, ok, over0, n, i)

# What one pass over the line found: its fields, its INFO entries' kinds
# (a missing INFO '.' is one entry), the FORMAT keys' kinds, the
# terminator's range.
type Ln is Data:
  Ln{fs: List<&2, Rg>, iks: List<&2, Ik>, fks: List<&2, Fk>, term: Rg}

# The sample columns, each after a tab (B.Fmt.split each).
def samples(cols: List<&2, Rg>, w: Sw, +ks: List<&2, Fk>, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  match cols:
    case Nil{}:
      w
    case +c <> t:
      samples(t, sample(ch(w, 9), ks, c, over0, n, i), ks, over0, n, i)

# FORMAT and the samples, if the line has them.
def rec.tail(rest: List<&2, Rg>, w: Sw, +fks: List<&2, Fk>, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  match rest:
    case Nil{}:
      w
    case +f <> cols:
      samples(cols, cpr(ch(w, 9), f), fks, over0, n, i)

# The record for ALT i (its range a) of n: its fields separated by tabs
# (B.Rec.piece): CHROM, POS, ID, REF, the ALT, QUAL, FILTER copied, INFO
# cut (info.w), FORMAT copied, the samples cut; then the line's terminator.
def record(w: Sw, +l: Ln, +over0: Bool, +n: Nat, +i: Nat, +a: Rg) -> Sw:
  match l:
    case Ln{f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> f7 <> rest, +iks, +fks, +term}:
      cpr(rec.tail(rest, info.go(iks, ch(cpr(ch(cpr(ch(cpr(ch(cpr(ch(cpr(ch(cpr(ch(cpr(w, f0), 9), f1), 9), f2), 9), f3), 9), a), 9), f5), 9), f6), 9), n, i, True{}), fks, over0, n, i), term)
    case Ln{fs, iks, fks, term}:
      Sw.fail(w)

def records(alts: List<&2, Rg>, w: Sw, +l: Ln, +over0: Bool, +n: Nat, +i: Nat) -> Sw:
  match alts:
    case Nil{}:
      w
    case +a <> t:
      records(t, record(w, l, over0, n, i, a), l, over0, n, 1n+i)

# ---------------------------------------------------------------------------
# The line
# ---------------------------------------------------------------------------

# The line handed back, with the records' bytes (Some) or None (the String
# path decides).
type Out is Type:
  Out{b: D.Bytes, r: Maybe<&1, D.Bytes>}

def out.of(w: Sw) -> Out:
  match w:
    case Sw{b, o, p, True{}}:
      Out{b, Some{o}}
    case Sw{b, o, p, False{}}:
      Out{b, None{}}

def go.write(+s: U32, +l: Ln, b: D.Bytes, +alts: List<&2, Rg>, +over0: Bool) -> Out:
  out.of(flush(records(alts, Sw{b, BY.empty(0n), Rg{s, s}, True{}}, l, over0, List.length(&2, Rg, alts), 1n)))

def go.ln(+s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, r: D.Bytes & List<&2, Ik>, +fks: List<&2, Fk>, +term: Rg) -> Out:
  (b, +iks) = r
  go.write(s, Ln{fs, iks, fks, term}, b, alts, over0)

def go.iks(r: D.Bytes & List<&2, Rg>, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Ik>:
  (b, xs) = r
  ikinds(xs, b, tags)

def go.fmt(+s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, +info: Rg, +term: Rg, +defs: B.Defs, r: D.Bytes & List<&2, Fk>) -> Out:
  (b, +fks) = r
  go.ln(s, fs, alts, over0, go.iks(cut(b, info, 59), B.Defs.info(defs)), fks, term)

def go.keys.k(r: D.Bytes & List<&2, Rg>, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Fk>:
  (b, xs) = r
  fkinds(xs, b, tags)

def go.keys(+f: Maybe<&2, Rg>, b: D.Bytes, +tags: List<&2, B.Tag>) -> D.Bytes & List<&2, Fk>:
  match f:
    case None{}:
      (b, Nil{})
    case Some{+x}:
      go.keys.k(cut(b, x, 58), tags)

def go.rest(rest: List<&2, Rg>, b: D.Bytes, +s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match rest:
    case +info <> Nil{}:
      go.fmt(s, fs, alts, over0, info, term, defs, go.keys(None{}, b, B.Defs.fmt(defs)))
    case +info <> +f <> cols:
      go.fmt(s, fs, alts, over0, info, term, defs, go.keys(Some{f}, b, B.Defs.fmt(defs)))
    case _:
      Out{b, None{}}

def go.alts.ok(ok: Bool, b: D.Bytes, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.rest(rest, b, s, fs, alts, over0, term, defs)
    case False{}:
      Out{b, None{}}

def go.alts.d(r: D.Bytes & Bool, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  (b, ok) = r
  go.alts.ok(ok, b, rest, s, fs, alts, over0, term, defs)

def nonempty(xs: List<&2, Rg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Rg{+a, +z} <> t:
      U32.is_lt(a, z) && nonempty(t)

def go.alts.n(ok: Bool, b: D.Bytes, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alts: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.alts.d(distinct(alts, (b, True{})), rest, s, fs, alts, over0, term, defs)
    case False{}:
      Out{b, None{}}

# The ALTs: two or more, none empty, no two equal up to case.
def go.alts(r: D.Bytes & List<&2, Rg>, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  (b, +alts) = r
  go.alts.n(Nat.is_le(2n, List.length(&2, Rg, alts)) && nonempty(alts), b, rest, s, fs, alts, over0, term, defs)

def go.ref.ok(ok: Bool, b: D.Bytes, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alt: Rg, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.alts(cut(b, alt, 44), rest, s, fs, over0, term, defs)
    case False{}:
      Out{b, None{}}

def go.ref.k(r: D.Bytes & Bool, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alt: Rg, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  (b, ok) = r
  go.ref.ok(ok, b, rest, s, fs, alt, over0, term, defs)

def go.pos.ok(ok: Bool, b: D.Bytes, +ref: Rg, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alt: Rg, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.ref.k(letters(b, ref), rest, s, fs, alt, over0, term, defs)
    case False{}:
      Out{b, None{}}

def go.pos.k(r: D.Bytes & Bool, +ref: Rg, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +alt: Rg, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  (b, ok) = r
  go.pos.ok(ok, b, ref, rest, s, fs, alt, over0, term, defs)

def go.chrom(ok: Bool, b: D.Bytes, +f1: Rg, +f3: Rg, +f4: Rg, +rest: List<&2, Rg>, +s: U32, +fs: List<&2, Rg>, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.pos.k(FC.digits(b, Rg.a(f1), Rg.z(f1)), f3, rest, s, fs, f4, over0, term, defs)
    case False{}:
      Out{b, None{}}

def go.fields.l(+fs: List<&2, Rg>, b: D.Bytes, +s: U32, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  match fs:
    case +f0 <> +f1 <> f2 <> +f3 <> +f4 <> f5 <> f6 <> +rest:
      go.chrom(U32.is_lt(Rg.a(f0), Rg.z(f0)), b, f1, f3, f4, rest, s, fs, over0, term, defs)
    case _:
      Out{b, None{}}

# Not MALFORMED (B.Rec.malformed): eight fields or more, CHROM not empty,
# POS digits, REF letters (the ALTs are tested in go.alts).
def go.fields(r: D.Bytes & List<&2, Rg>, +s: U32, +over0: Bool, +term: Rg, +defs: B.Defs) -> Out:
  (b, +fs) = r
  go.fields.l(fs, b, s, over0, term, defs)

def go.body(cr: Bool, b: D.Bytes, +s: U32, +lf: U32, +over0: Bool, +defs: B.Defs) -> Out:
  +be = Bool.pick(U32, cr, (lf - 1 : U32), lf)
  go.fields(cut(b, Rg{s, be}, 9), s, over0, Rg{be, (lf + 1 : U32)}, defs)

def go.cr(r: D.Bytes & U32, +s: U32, +lf: U32, +over0: Bool, +defs: B.Defs) -> Out:
  (b, +x) = r
  go.body(U32.is_lt(s, lf) && U32.is_eq(x, 13), b, s, lf, over0, defs)

def go.size(ok: Bool, b: D.Bytes, +s: U32, +lf: U32, +over0: Bool, +defs: B.Defs) -> Out:
  match ok:
    case True{}:
      go.cr(BY.at(b, Bool.pick(U32, U32.is_lt(s, lf), (lf - 1 : U32), lf)), s, lf, over0, defs)
    case False{}:
      Out{b, None{}}

# The line at s (its LF at lf) split into one record per ALT, as
# B.Rec.parts(defs, o, body) gives them with -m (over0: --multi-overlaps 0),
# each followed by the line's terminator (LF, or CR LF); None for a line
# B.Rec.parts would not split, and whenever this code does not decide (the
# String path then does). The line is at most 2^28 bytes.
def split(b: D.Bytes, +s: U32, +lf: U32, +over0: Bool, +defs: B.Defs) -> Out:
  go.size(U32.is_le(s, lf) && U32.is_le((lf - s : U32), 268435456), b, s, lf, over0, defs)

# ---------------------------------------------------------------------------
# Which lines to split
# ---------------------------------------------------------------------------

# Looking for the LF and the comma test: the line's first tabs, at most 5.
type Ml is Type:
  Ml{b: D.Bytes, j: U32, lf: U32, tabs: Nat, ok: Bool}

def multi.tab(r: D.Bytes & U32, +lf: U32, +k: Nat) -> Ml:
  (b, +t) = r
  Ml{b, (t + 1 : U32), lf, 1n+k, U32.is_lt(t, lf)}

def multi.loop(n: Nat, x: Ml) -> Ml:
  match n x:
    case 0n x:
      x
    case 1n+m Ml{b, j, lf, tabs, False{}}:
      Ml{b, j, lf, tabs, False{}}
    case 1n+m Ml{b, +j, +lf, +tabs, True{}}:
      multi.loop(m, multi.tab(F.find(b, j, lf, 9), lf, tabs))

def multi.comma(r: D.Bytes & U32, +e: U32, +lf: U32) -> D.Bytes & Maybe<&2, U32>:
  (b, +c) = r
  (b, Bool.pick(Maybe<&2, U32>, U32.is_lt(c, e), Some{lf}, None{}))

def multi.alt(r: D.Bytes & U32, +a: U32, +lf: U32) -> D.Bytes & Maybe<&2, U32>:
  (b, +e) = r
  multi.comma(F.find(b, a, e, 44), e, lf)

def multi.fin(x: Ml) -> D.Bytes & Maybe<&2, U32>:
  match x:
    case Ml{b, +j, +lf, tabs, True{}}:
      multi.alt(F.find(b, j, lf, 9), j, lf)
    case Ml{b, j, lf, tabs, False{}}:
      (b, None{})

def multi.lf.if(ok: Bool, b: D.Bytes, +s: U32, +lf: U32) -> D.Bytes & Maybe<&2, U32>:
  match ok:
    case True{}:
      multi.fin(multi.loop(4n, Ml{b, s, lf, 0n, True{}}))
    case False{}:
      (b, None{})

def multi.lf(+s: U32, r: D.Bytes & U32, +len: U32) -> D.Bytes & Maybe<&2, U32>:
  (b, +lf) = r
  multi.lf.if(U32.is_lt(lf, len), b, s, lf)

# The line at s is complete and its ALT field (after its 4th tab) has a
# comma: Some{its LF}. A cheap test before the fast path.
def multi(b: D.Bytes, +s: U32) -> D.Bytes & Maybe<&2, U32>:
  D.Bytes{+len, buf} = b
  multi.lf(s, F.find(D.Bytes{len, buf}, s, len, 10), len)
