import Base
import ./types.bend as B
import ./norm_fast.bend as NF
import ./norm_run.bend as NR
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/fast.bend as F

# framebender: rewriting a record on its bytes (code, not spec). A body line
# the fast path does not take (norm_fast.bend) may still be judged without
# decoding it: its alleles are A, C, G, T or N in either case, its INFO has
# no END entry and no entry the stale check reads, and the cached reference
# window holds its REF. Then Tan et al.'s algorithm (tan.bend's var_in) runs
# on the bytes of the line and of the window, and the rewritten line is
# written into a buffer of its own. norm.bend calls it for a line in the
# current CHROM run whose REF the window holds (its WHit); any doubt sends
# the line to the String path. notes/rewrite.md has the refinement argument.
#
# The alleles are kept as counters. After k shifts and tr trims on the right
# and d trims on the left, allele i (a_i: its L_i bytes in the line) is
#   drop(take(R_k ++ a_i, L_i - tr), d)       at position pos - k + d
# where R_k is the k reference letters before POS (contig indices
# pos-1-k .. pos-2): a shift puts the letter before the variant in front of
# every allele and drops its last base, a trim drops the last base.

# ---------------------------------------------------------------------------
# Bytes
# ---------------------------------------------------------------------------

# A, C, G, T or N in either case.
def isl(+x: U32) -> Bool:
  U32.is_eq(x, 65) || U32.is_eq(x, 67) || U32.is_eq(x, 71) || U32.is_eq(x, 84) || U32.is_eq(x, 78) || U32.is_eq(x, 97) || U32.is_eq(x, 99) || U32.is_eq(x, 103) || U32.is_eq(x, 116) || U32.is_eq(x, 110)

# A letter's base as a code 0-4 (A, C, G, T, N), as B.Base.of_fasta reads it
# (which agrees with B.Base.of_letter on A, C, G, T, N in either case).
def code(+x: U32) -> U32:
  +u = B.Char.code(Char.to_upper(Chr{x}))
  Bool.pick(U32, U32.is_eq(u, 65) || U32.is_eq(u, 82) || U32.is_eq(u, 77) || U32.is_eq(u, 87) || U32.is_eq(u, 68) || U32.is_eq(u, 72) || U32.is_eq(u, 86), 0,
  Bool.pick(U32, U32.is_eq(u, 67) || U32.is_eq(u, 89) || U32.is_eq(u, 83) || U32.is_eq(u, 66), 1,
  Bool.pick(U32, U32.is_eq(u, 71) || U32.is_eq(u, 75), 2,
  Bool.pick(U32, U32.is_eq(u, 84), 3,
  4))))

# The letter written for a code (B.Base.letter).
def letter(+c: U32) -> U32:
  Bool.pick(U32, U32.is_eq(c, 0), 65,
  Bool.pick(U32, U32.is_eq(c, 1), 67,
  Bool.pick(U32, U32.is_eq(c, 2), 71,
  Bool.pick(U32, U32.is_eq(c, 3), 84,
  78))))

# ---------------------------------------------------------------------------
# INFO has no entry with key CIGAR, HOMLEN, HOMSEQ or AA (the keys
# B.Rec.stale looks for; a key is the text before its entry's first '=')
# ---------------------------------------------------------------------------

def lit.eq(+k: U32, r: D.Bytes & U32) -> D.Bytes & Bool:
  (b, +x) = r
  (b, U32.is_eq(x, k))

def lit.one(ok: Bool, b: D.Bytes, +k: U32, +j: U32) -> D.Bytes & Bool:
  match ok:
    case True{}:
      lit.eq(k, BY.at(b, j))
    case False{}:
      (b, False{})

# r's flag, and bytes j, j+1, ... are ks.
def lit.go(ks: List<&2, U32>, r: D.Bytes & Bool, +j: U32) -> D.Bytes & Bool:
  match ks:
    case Nil{}:
      r
    case +k <> t:
      (b, ok) = r
      lit.go(t, lit.one(ok, b, k, j), (j + 1 : U32))

def key6(r: D.Bytes & Bool, +j: U32) -> D.Bytes & Bool:
  (b, hit) = r
  match hit:
    case True{}:
      (b, True{})
    case False{}:
      lit.go([72, 79, 77, 83, 69, 81], (b, True{}), j)

def key.if(two: Bool, five: Bool, six: Bool, b: D.Bytes, +j: U32) -> D.Bytes & Bool:
  match two five six:
    case True{} _ _:
      lit.go([65, 65], (b, True{}), j)
    case False{} True{} _:
      lit.go([67, 73, 71, 65, 82], (b, True{}), j)
    case False{} False{} True{}:
      key6(lit.go([72, 79, 77, 76, 69, 78], (b, True{}), j), j)
    case False{} False{} False{}:
      (b, False{})

# The n bytes from j are AA, CIGAR, HOMLEN or HOMSEQ.
def key(b: D.Bytes, +j: U32, +n: U32) -> D.Bytes & Bool:
  key.if(U32.is_eq(n, 2), U32.is_eq(n, 5), U32.is_eq(n, 6), b, j)

# At the entry starting at j: none of the keys so far; another entry to look
# at.
type Sk is Type:
  Sk{b: D.Bytes, j: U32, to: U32, ok: Bool, more: Bool}

def sk.w(+ok: Bool, end: Bool, b: D.Bytes, +sm: U32, +to: U32) -> Sk:
  match end:
    case True{}:
      Sk{b, sm, to, ok, False{}}
    case False{}:
      Sk{b, (sm + 1 : U32), to, ok, ok}

def sk.v(ok: Bool, +to: U32, r: D.Bytes & U32) -> Sk:
  (b, +sm) = r
  sk.w(ok, U32.is_eq(sm, to), b, sm, to)

def sk.e(+ok: Bool, end: Bool, semi: Bool, b: D.Bytes, +ke: U32, +to: U32) -> Sk:
  match end semi:
    case True{} _:
      Sk{b, ke, to, ok, False{}}
    case False{} True{}:
      Sk{b, (ke + 1 : U32), to, ok, ok}
    case False{} False{}:
      sk.v(ok, to, F.find(b, ke, to, 59))

def sk.n(ok: Bool, +ke: U32, +to: U32, r: D.Bytes & U32) -> Sk:
  (b, +y) = r
  sk.e(ok, U32.is_eq(ke, to), U32.is_eq(y, 59), b, ke, to)

def sk.h(+ke: U32, +to: U32, r: D.Bytes & Bool) -> Sk:
  (b, hit) = r
  sk.n(Bool.not(hit), ke, to, BY.at(b, ke))

def sk.k(+j: U32, +to: U32, r: D.Bytes & U32) -> Sk:
  (b, +ke) = r
  sk.h(ke, to, key(b, j, (ke - j : U32)))

# The entry at j: its key ends at the first '=' or ';' (or INFO's end); the
# next entry starts after the next ';'.
def sk.step(x: Sk) -> Sk:
  match x:
    case Sk{b, +j, +to, ok, m}:
      sk.k(j, to, F.find2(b, j, to, 61, 59))

def sk.go(n: Nat, x: Sk) -> D.Bytes & Bool:
  match n x:
    case 0n Sk{b, j, to, ok, m}:
      (b, False{})
    case 1n+k Sk{b, j, to, ok, False{}}:
      (b, ok)
    case 1n+k Sk{b, j, to, ok, True{}}:
      sk.go(k, sk.step(Sk{b, j, to, ok, True{}}))

# INFO (from .. to-1) has no entry with key CIGAR, HOMLEN, HOMSEQ or AA.
def nostale(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Bool:
  sk.go(U32.to_nat((to - from + 2 : U32)), Sk{b, from, to, True{}, True{}})

# ---------------------------------------------------------------------------
# The line's tests
# ---------------------------------------------------------------------------

# An allele's bytes in the line: ln bytes from st.
type Ap is Data:
  Ap{st: U32, ln: U32}

def Ap.st(a: Ap) -> U32:
  match a:
    case Ap{s, n}:
      s

def Ap.ln(a: Ap) -> U32:
  match a:
    case Ap{s, n}:
      n

# Fix: the line passed every test on its own bytes; pos: its POS; c: its cut
# (NF.Cut8); als: REF, then each ALT; up: every allele byte is upper case.
type Fp is Data:
  Fix{pos: U32, c: NF.Cut, als: List<&2, Ap>, up: Bool}
  No{}

type Fr is Type:
  Fr{b: D.Bytes, p: Fp}

# Letters from .. to-1: all A, C, G, T or N (either case); all upper case.
type Lv is Type:
  Lv{b: D.Bytes, ok: Bool, up: Bool}

def lets.go(n: Nat, r: D.Bytes & U32, +j: U32, ok: Bool, up: Bool) -> Lv:
  match n:
    case 0n:
      (b, y) = r
      Lv{b, ok, up}
    case 1n+m:
      (b, +y) = r
      lets.go(m, BY.at(b, (j + 1 : U32)), (j + 1 : U32), ok && isl(y), up && U32.is_lt(y, 97))

def lets(b: D.Bytes, +from: U32, +to: U32) -> Lv:
  lets.go(U32.to_nat((to - from : U32)), BY.at(b, from), from, True{}, True{})

def feq.go(n: Nat, r: D.Bytes & (U32 & U32), +i: U32, +j: U32, acc: Bool) -> D.Bytes & Bool:
  match n:
    case 0n:
      (b, q) = r
      (b, acc)
    case 1n+m:
      (b, q) = r
      (x, y) = q
      feq.go(m, BY.at2(b, (i + 1 : U32), (j + 1 : U32)), (i + 1 : U32), (j + 1 : U32), acc && U32.is_zero(((x .^. y : U32) .&. 223 : U32)))

def feq.if(same_len: Bool, b: D.Bytes, +i: U32, +j: U32, +n: U32) -> D.Bytes & Bool:
  match same_len:
    case True{}:
      feq.go(U32.to_nat(n), BY.at2(b, i, j), i, j, True{})
    case False{}:
      (b, False{})

# Two alleles are equal up to case.
def feq(b: D.Bytes, +x: Ap, +y: Ap) -> D.Bytes & Bool:
  feq.if(U32.is_eq(Ap.ln(x), Ap.ln(y)), b, Ap.st(x), Ap.st(y), Ap.ln(x))

def dis.neg(r: D.Bytes & Bool) -> D.Bytes & Bool:
  (b, eq) = r
  (b, Bool.not(eq))

def dis.one(ok: Bool, b: D.Bytes, +x: Ap, +p: Ap) -> D.Bytes & Bool:
  match ok:
    case True{}:
      dis.neg(feq(b, x, p))
    case False{}:
      (b, False{})

# r's flag: x differs, up to case, from every allele so far; then from every
# allele of ps.
def dis.go(ps: List<&2, Ap>, r: D.Bytes & Bool, +x: Ap) -> D.Bytes & Bool:
  match ps:
    case Nil{}:
      r
    case +p <> t:
      (b, ok) = r
      dis.go(t, dis.one(ok, b, x, p), x)

# The ALT alleles from a on (the ALT field ends at e): the alleles so far
# (newest first, REF last), all fine so far, all upper case so far, another
# one to read.
type Xs is Type:
  Xs{b: D.Bytes, a: U32, e: U32, ps: List<&2, Ap>, ok: Bool, up: Bool, more: Bool}

def alt.d(+ap: Ap, +c: U32, +e: U32, ps: List<&2, Ap>, ok: Bool, up: Bool, r: D.Bytes & Bool) -> Xs:
  (b, dd) = r
  +ok2 = ok && dd
  Xs{b, (c + 1 : U32), e, ap <> ps, ok2, up, ok2 && U32.is_lt(c, e)}

def alt.l(+a: U32, +c: U32, +e: U32, +ps: List<&2, Ap>, ok: Bool, up: Bool, v: Lv) -> Xs:
  match v:
    case Lv{b, lok, lup}:
      +ap = {Ap{a, (c - a : U32)} : Ap}
      alt.d(ap, c, e, ps, ok && lok && U32.is_lt(a, c), up && lup, dis.go(ps, (b, True{}), ap))

def alt.c(+a: U32, +e: U32, ps: List<&2, Ap>, ok: Bool, up: Bool, r: D.Bytes & U32) -> Xs:
  (b, +c) = r
  alt.l(a, c, e, ps, ok, up, lets(b, a, c))

# One ALT allele: up to the next comma, or the field's end.
def alt.step(x: Xs) -> Xs:
  match x:
    case Xs{b, +a, +e, ps, ok, up, m}:
      alt.c(a, e, ps, ok, up, F.find(b, a, e, 44))

# At most 16 ALT alleles (fuel 17, as NF.alts.go).
def alts.go(n: Nat, x: Xs) -> Xs:
  match n x:
    case 0n Xs{b, a, e, ps, ok, up, m}:
      Xs{b, a, e, ps, False{}, up, m}
    case 1n+k Xs{b, a, e, ps, ok, up, False{}}:
      Xs{b, a, e, ps, ok, up, False{}}
    case 1n+k Xs{b, a, e, ps, ok, up, True{}}:
      alts.go(k, alt.step(Xs{b, a, e, ps, ok, up, True{}}))

def rev_ap(xs: List<&2, Ap>, acc: List<&2, Ap>) -> List<&2, Ap>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_ap(t, x <> acc)

def Cut.e6(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      e6
    case _:
      0

def Cut.e7(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      e7
    case _:
      0

def Cut.lf(c: NF.Cut) -> U32:
  match c:
    case NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      lf
    case _:
      0

def fx.if(ok: Bool, b: D.Bytes, +p: Fp) -> Fr:
  match ok:
    case True{}:
      Fr{b, p}
    case False{}:
      Fr{b, No{}}

def fx.cr(+pos: U32, +c: NF.Cut, +als: List<&2, Ap>, up: Bool, r: D.Bytes & U32) -> Fr:
  (b, +x) = r
  fx.if(Bool.not(U32.is_eq(Cut.e7(c), Cut.lf(c)) && U32.is_eq(x, 13)), b, Fix{pos, c, als, up})

def fx.st(+pos: U32, +c: NF.Cut, +als: List<&2, Ap>, up: Bool, r: D.Bytes & Bool) -> Fr:
  (b, ok) = r
  match ok:
    case True{}:
      fx.cr(pos, c, als, up, BY.at(b, (Cut.lf(c) - 1 : U32)))
    case False{}:
      Fr{b, No{}}

def fx.info(+pos: U32, +c: NF.Cut, +als: List<&2, Ap>, up: Bool, r: D.Bytes & Bool) -> Fr:
  (b, ok) = r
  match ok:
    case True{}:
      fx.st(pos, c, als, up, nostale(b, (Cut.e6(c) + 1 : U32), Cut.e7(c)))
    case False{}:
      Fr{b, No{}}

def fx.alts(+pos: U32, +c: NF.Cut, x: Xs) -> Fr:
  match x:
    case Xs{b, a, e, ps, True{}, up, m}:
      fx.info(pos, c, rev_ap(ps, Nil{}), up, NF.noend(b, (Cut.e6(c) + 1 : U32), Cut.e7(c)))
    case Xs{b, a, e, ps, False{}, up, m}:
      Fr{b, No{}}

def fx.ref.if(ok: Bool, +pos: U32, +c: NF.Cut, b: D.Bytes, +s3: U32, +e3: U32, +e4: U32, up: Bool) -> Fr:
  match ok:
    case True{}:
      fx.alts(pos, c, alts.go(17n, Xs{b, (e3 + 1 : U32), e4, [Ap{s3, (e3 - s3 : U32)}], True{}, up, True{}}))
    case False{}:
      Fr{b, No{}}

def fx.ref(+pos: U32, +c: NF.Cut, v: Lv) -> Fr:
  match c v:
    case NF.Cut8{e0, e1, +e2, +e3, +e4, e5, e6, e7, lf} Lv{b, True{}, up}:
      fx.ref.if(U32.is_lt((e2 + 1 : U32), e3) && U32.is_lt((e3 + 1 : U32), e4), pos, c, b, (e2 + 1 : U32), e3, e4, up)
    case _ Lv{b, ok, up}:
      Fr{b, No{}}

def fx.pos(+c: NF.Cut, v: NF.Bv) -> Fr:
  match c v:
    case NF.Cut8{e0, e1, +e2, +e3, e4, e5, e6, e7, lf} NF.Bv{b, True{}, +pos}:
      fx.ref(pos, c, lets(b, (e2 + 1 : U32), e3))
    case _ NF.Bv{b, ok, pos}:
      Fr{b, No{}}

def fx.cut(r: NF.Cr) -> Fr:
  match r:
    case NF.Cr{b, NF.Cut8{+e0, +e1, e2, e3, e4, e5, e6, e7, lf}}:
      fx.pos(NF.Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, NF.num(b, (e0 + 1 : U32), e1))
    case NF.Cr{b, c}:
      Fr{b, No{}}

# The tests on the bytes of the line at s: 8 fields; POS as Nat.show writes
# it; REF and up to 16 ALTs, each one or more of A, C, G, T, N in either
# case, no two equal up to case; INFO without an END entry and without an
# entry nostale looks for; no CR before the LF when INFO is the last field.
def line(b: D.Bytes, +s: U32) -> Fr:
  fx.cut(NF.cut(b, s))

# ---------------------------------------------------------------------------
# Tan et al.'s algorithm on the bytes (tan.bend's right, then left)
# ---------------------------------------------------------------------------

# The line b and the window w (the reference letters from contig index offu,
# raw as the driver read them), handed back with a byte read.
type Rd is Type:
  Rd{b: D.Bytes, w: D.Bytes, x: U32}

def el.w(b: D.Bytes, r: D.Bytes & U32) -> Rd:
  (w, +x) = r
  Rd{b, w, x}

def el.l(w: D.Bytes, r: D.Bytes & U32) -> Rd:
  (b, +x) = r
  Rd{b, w, x}

def el.if(inw: Bool, b: D.Bytes, w: D.Bytes, +iw: U32, +il: U32) -> Rd:
  match inw:
    case True{}:
      el.w(b, BY.at(w, iw))
    case False{}:
      el.l(w, BY.at(b, il))

# Byte j of R_k ++ a (a: the allele's bytes in the line; p0: POS).
def el(b: D.Bytes, w: D.Bytes, +a: Ap, +k: U32, +j: U32, +p0: U32, +offu: U32) -> Rd:
  el.if(U32.is_lt(j, k), b, w, ((((p0 - 1 : U32) - k : U32) + j : U32) - offu : U32), ((Ap.st(a) + j : U32) - k : U32))

# What the alleles' last (or first) bases say: all equal to REF's, all
# alleles at least two long.
type Lt is Type:
  Lt{b: D.Bytes, w: D.Bytes, eq: Bool, long: Bool}

def ends.ix(last: Bool, +a: Ap, +tr: U32, +d: Nat) -> U32:
  match last:
    case True{}:
      ((Ap.ln(a) - tr : U32) - 1 : U32)
    case False{}:
      U32.from_nat(d)

def ends.r(+a: Ap, +z: U32, +tr: U32, +d: Nat, eq: Bool, long: Bool, r: Rd) -> Lt:
  match r:
    case Rd{b, w, +x}:
      Lt{b, w, eq && U32.is_eq(code(x), z), long && U32.is_le(2, ((Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32))}

# The ALTs' bases against REF's z: their last base (last) or their base d
# (the first after d left trims), with tr right trims done.
def ends.go(als: List<&2, Ap>, l: Lt, +z: U32, +k: U32, +tr: U32, +d: Nat, +last: Bool, +p0: U32, +offu: U32) -> Lt:
  match als:
    case Nil{}:
      l
    case +a <> t:
      match l:
        case Lt{b, w, eq, long}:
          ends.go(t, ends.r(a, z, tr, d, eq, long, el(b, w, a, k, ends.ix(last, a, tr, d), p0, offu)), z, k, tr, d, last, p0, offu)

def ends.ref(alts: List<&2, Ap>, +a: Ap, +k: U32, +tr: U32, +d: Nat, +last: Bool, +p0: U32, +offu: U32, r: Rd) -> Lt:
  match r:
    case Rd{b, w, +x}:
      ends.go(alts, Lt{b, w, True{}, U32.is_le(2, ((Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32))}, code(x), k, tr, d, last, p0, offu)

def ends(als: List<&2, Ap>, b: D.Bytes, w: D.Bytes, +k: U32, +tr: U32, +d: Nat, +last: Bool, +p0: U32, +offu: U32) -> Lt:
  match als:
    case Nil{}:
      Lt{b, w, False{}, True{}}
    case +a <> t:
      ends.ref(t, a, k, tr, d, last, p0, offu, el(b, w, a, k, ends.ix(last, a, tr, d), p0, offu))

# The next step on the right (tan.bend's next_act).
type Ak is Data:
  KStop{}
  KTrim{}
  KShift{}
  KNeed{}

type Na is Type:
  Na{b: D.Bytes, w: D.Bytes, a: Ak}

def act(eq: Bool, long: Bool, shift: Bool, have: Bool) -> Ak:
  match eq:
    case False{}:
      KStop{}
    case True{}:
      match long:
        case True{}:
          KTrim{}
        case False{}:
          match shift:
            case False{}:
              KStop{}
            case True{}:
              match have:
                case False{}:
                  KNeed{}
                case True{}:
                  KShift{}

def next.k(+k: U32, +p0: U32, +offu: U32, l: Lt) -> Na:
  match l:
    case Lt{b, w, eq, long}:
      +p = (p0 - k : U32)
      Na{b, w, act(eq, long, U32.is_le(2, p), U32.is_le(offu, (p - 2 : U32)))}

# When the alleles all end with the same base: trim it if all are at least
# two long, else shift (the base before the variant, contig index
# p0 - k - 2, must be in the window), unless the variant is at position 1.
def next(b: D.Bytes, w: D.Bytes, +als: List<&2, Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32) -> Na:
  next.k(k, p0, offu, ends(als, b, w, k, tr, 0n, True{}, p0, offu))

type Rr is Type:
  RDone{b: D.Bytes, w: D.Bytes, k: U32, tr: U32}
  RNeed{b: D.Bytes, w: D.Bytes}

def right(fuel: Nat, na: Na, +als: List<&2, Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32) -> Rr:
  match fuel na:
    case 0n Na{b, w, a}:
      RDone{b, w, k, tr}
    case 1n+f Na{b, w, KStop{}}:
      RDone{b, w, k, tr}
    case 1n+f Na{b, w, KNeed{}}:
      RNeed{b, w}
    case 1n+f Na{b, w, KTrim{}}:
      right(f, next(b, w, als, p0, offu, k, (tr + 1 : U32)), als, p0, offu, k, (tr + 1 : U32))
    case 1n+f Na{b, w, KShift{}}:
      right(f, next(b, w, als, p0, offu, (k + 1 : U32), tr), als, p0, offu, (k + 1 : U32), tr)

def left.k(l: Lt) -> Lt:
  match l:
    case Lt{b, w, eq, +long}:
      Lt{b, w, eq && long, long}

# All alleles start with the same base and are at least two long (after d
# left trims).
def firsts(b: D.Bytes, w: D.Bytes, +als: List<&2, Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> Lt:
  left.k(ends(als, b, w, k, tr, d, False{}, p0, offu))

type Lr is Type:
  Lr{b: D.Bytes, w: D.Bytes, d: Nat}

def left(fuel: Nat, g: Lt, +als: List<&2, Ap>, +p0: U32, +offu: U32, +k: U32, +tr: U32, +d: Nat) -> Lr:
  match fuel g:
    case 0n Lt{b, w, go, l}:
      Lr{b, w, d}
    case 1n+f Lt{b, w, False{}, l}:
      Lr{b, w, d}
    case 1n+f Lt{b, w, True{}, l}:
      left(f, firsts(b, w, als, p0, offu, k, tr, 1n+d), als, p0, offu, k, tr, 1n+d)

# The alleles' total length after tr right trims (tan.bend's total).
def tot(als: List<&2, Ap>, +tr: U32) -> Nat:
  match als:
    case Nil{}:
      0n
    case a <> t:
      Nat.add(U32.to_nat((Ap.ln(a) - tr : U32)), tot(t, tr))

# The normalized variant as counters (Nd), or Ng: it needs a letter before the
# window.
type Nr is Type:
  Nd{b: D.Bytes, w: D.Bytes, k: U32, tr: U32, d: Nat}
  Ng{b: D.Bytes, w: D.Bytes}

def norm.l(+k: U32, +tr: U32, r: Lr) -> Nr:
  match r:
    case Lr{b, w, d}:
      Nd{b, w, k, tr, d}

def norm.r(+als: List<&2, Ap>, +p0: U32, +offu: U32, r: Rr) -> Nr:
  match r:
    case RNeed{b, w}:
      Ng{b, w}
    case RDone{b, w, +k, +tr}:
      norm.l(k, tr, left(Nat.add(U32.to_nat((p0 - k : U32)), tot(als, tr)), firsts(b, w, als, p0, offu, k, tr, 0n), als, p0, offu, k, tr, 0n))

# tan.bend's var_in on the record's alleles (als in b, POS p0) and the window
# w (from contig index offu): the same fuel, the same steps.
def norm(b: D.Bytes, w: D.Bytes, +als: List<&2, Ap>, +p0: U32, +offu: U32) -> Nr:
  norm.r(als, p0, offu, right(Nat.add(U32.to_nat(p0), tot(als, 0)), next(b, w, als, p0, offu, 0, 0), als, p0, offu, 0, 0))

# ---------------------------------------------------------------------------
# The rewritten line
# ---------------------------------------------------------------------------

# The buffer being written, the line, the window, and whether every write so
# far was made. A write is made only while the buffer holds at most 2^29
# bytes and the piece has at most 2^28 (so no size comes near 2^31); else ok
# turns False, nothing more is written, and the line takes the String path.
type Wb is Type:
  Wb{o: D.Bytes, b: D.Bytes, w: D.Bytes, ok: Bool}

# s has at most w characters (norm.bend's len_le).
def len_le.go(s: String, z: Bool, +w: U32) -> Bool:
  match s z:
    case SNil{} _:
      True{}
    case SCon{h, t} True{}:
      False{}
    case SCon{h, t} False{}:
      len_le.go(t, U32.is_zero((w - 1 : U32)), (w - 1 : U32))

def len_le(s: String, +w: U32) -> Bool:
  len_le.go(s, U32.is_zero(w), w)

def small.k(+k: U32, r: D.Bytes & U32) -> D.Bytes & Bool:
  (o, +l) = r
  (o, U32.is_le(l, 536870912) && U32.is_le(k, 268435456))

# o holds at most 2^29 bytes and k is at most 2^28.
def small(o: D.Bytes, +k: U32) -> D.Bytes & Bool:
  small.k(k, BY.len(o))

def pb.fin(w: D.Bytes, r: D.Bytes & D.Bytes) -> Wb:
  (o, b) = r
  Wb{o, b, w, True{}}

def pb.ok(ok: Bool, o: D.Bytes, b: D.Bytes, w: D.Bytes, +s: U32, +n: U32) -> Wb:
  match ok:
    case True{}:
      pb.fin(w, NR.put_bytes(o, b, s, n))
    case False{}:
      Wb{o, b, w, False{}}

def pb.k(b: D.Bytes, w: D.Bytes, +s: U32, +n: U32, r: D.Bytes & Bool) -> Wb:
  (o, ok) = r
  pb.ok(ok, o, b, w, s, n)

# Bytes s .. s+n-1 of the line added.
def put_b(r: Wb, +s: U32, +n: U32) -> Wb:
  match r:
    case Wb{o, b, w, True{}}:
      pb.k(b, w, s, n, small(o, n))
    case Wb{o, b, w, False{}}:
      Wb{o, b, w, False{}}

def ps.ok(ok: Bool, o: D.Bytes, b: D.Bytes, w: D.Bytes, +t: String) -> Wb:
  match ok:
    case True{}:
      Wb{NR.put_str(o, t), b, w, True{}}
    case False{}:
      Wb{o, b, w, False{}}

def ps.k(b: D.Bytes, w: D.Bytes, +t: String, r: D.Bytes & U32) -> Wb:
  (o, +l) = r
  ps.ok(U32.is_le(l, 536870912) && len_le(t, 268435456), o, b, w, t)

# A text (one byte per Char) added.
def put_s(r: Wb, +t: String) -> Wb:
  match r:
    case Wb{o, b, w, True{}}:
      ps.k(b, w, t, BY.len(o))
    case Wb{o, b, w, False{}}:
      Wb{o, b, w, False{}}

def pc.ok(ok: Bool, o: D.Bytes, b: D.Bytes, w: D.Bytes, +x: U32) -> Wb:
  match ok:
    case True{}:
      Wb{BY.push(NR.room(o, 1), x), b, w, True{}}
    case False{}:
      Wb{o, b, w, False{}}

def pc.k(b: D.Bytes, w: D.Bytes, +x: U32, r: D.Bytes & Bool) -> Wb:
  (o, ok) = r
  pc.ok(ok, o, b, w, x)

# One byte added.
def put_c(r: Wb, +x: U32) -> Wb:
  match r:
    case Wb{o, b, w, True{}}:
      pc.k(b, w, x, small(o, 1))
    case Wb{o, b, w, False{}}:
      Wb{o, b, w, False{}}

# The line and the window, with a text read from them.
type Rs is Type:
  Rs{b: D.Bytes, w: D.Bytes, s: String}

def al.cons(+c: Char, r: Rs) -> Rs:
  match r:
    case Rs{b, w, t}:
      Rs{b, w, SCon{c, t}}

# n letters for the bases j, j+1, ... of R_k ++ a (r: the buffers, with
# byte j read).
def al.go(n: Nat, r: Rd, +a: Ap, +k: U32, +j: U32, +p0: U32, +offu: U32) -> Rs:
  match n r:
    case 0n Rd{b, w, x}:
      Rs{b, w, ""}
    case 1n+m Rd{b, w, +x}:
      al.cons(Chr{letter(code(x))}, al.go(m, el(b, w, a, k, (j + 1 : U32), p0, offu), a, k, (j + 1 : U32), p0, offu))

# The allele's bases d .. L - tr - 1 of R_k ++ a, as letters.
def al(b: D.Bytes, w: D.Bytes, +a: Ap, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32) -> Rs:
  al.go(U32.to_nat(((Ap.ln(a) - tr : U32) - U32.from_nat(d) : U32)), el(b, w, a, k, U32.from_nat(d), p0, offu), a, k, U32.from_nat(d), p0, offu)

def as.add(+acc: String, +sep: String, r: Rs) -> Rs:
  match r:
    case Rs{b, w, t}:
      Rs{b, w, String.append(acc, String.append(sep, t))}

# The ALT alleles' letters after acc, separated by commas (first: acc holds
# none yet).
def as.go(als: List<&2, Ap>, r: Rs, first: Bool, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32) -> Rs:
  match als:
    case Nil{}:
      r
    case +a <> t:
      match r:
        case Rs{b, w, +acc}:
          as.go(t, as.add(acc, Bool.pick(String, first, "", ","), al(b, w, a, k, tr, d, p0, offu)), False{}, k, tr, d, p0, offu)

# The new line is at most a byte longer than the line (the new POS may have
# one more digit; the alleles only lose bases), so its buffer is made with
# room for the line and 24 bytes more (NR.room never grows it).
def wr.fin(+s: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, +rs: String, r: Rs) -> Wb:
  match r:
    case Rs{b, w, +as}:
      put_b(put_s(put_c(put_s(put_b(put_s(put_b(Wb{BY.empty(NR.depth(((lf - s : U32) + 24 : U32))), b, w, True{}}, s, ((e0 + 1 : U32) - s : U32)), Nat.show(q)), e1, ((e2 + 1 : U32) - e1 : U32)), rs), 9), as), e4, ((lf + 1 : U32) - e4 : U32))

def wr.alts(+s: U32, +e0: U32, +e1: U32, +e2: U32, +e4: U32, +lf: U32, +q: Nat, alts: List<&2, Ap>, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32, r: Rs) -> Wb:
  match r:
    case Rs{b, w, +rs}:
      wr.fin(s, e0, e1, e2, e4, lf, q, rs, as.go(alts, Rs{b, w, ""}, True{}, k, tr, d, p0, offu))

# The line at s (cut c) rewritten for the counters, in a buffer of its own:
# CHROM and its tab, the new POS, the tab, ID and the tab after it, the new
# REF, a tab, the new ALTs, then the rest of the line from ALT's tab to the
# LF.
def write(b: D.Bytes, w: D.Bytes, +s: U32, +c: NF.Cut, +als: List<&2, Ap>, +k: U32, +tr: U32, +d: Nat, +p0: U32, +offu: U32) -> Wb:
  match c als:
    case NF.Cut8{+e0, +e1, +e2, e3, +e4, e5, e6, e7, +lf} +a <> t:
      wr.alts(s, e0, e1, e2, e4, lf, U32.to_nat(((p0 - k : U32) + U32.from_nat(d) : U32)), t, k, tr, d, p0, offu, al(b, w, a, k, tr, d, p0, offu))
    case _ _:
      Wb{BY.empty(0n), b, w, False{}}
