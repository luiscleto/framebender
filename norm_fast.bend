import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/fast.bend as F

# framebender: the fast path's tests on the bytes of one line (code, not
# spec). They decide, without decoding the line, that a body record is valid,
# in scope, already in normal form and written as Rec.rebuild would write it,
# with INFO's END, if any, as B.Info.end_ok asks (so J.fast gives Same, given
# the REF check and the CHROM run, which norm.bend tests). Any doubt answers
# Slow, and the String path (norm_line.bend) decides. notes/bytes.md has the
# refinement argument for each test.

# ---------------------------------------------------------------------------
# The first 8 fields: their ends
# ---------------------------------------------------------------------------

# The first tab or LF at or after s: j; part says there is none before the
# buffer's end (j is then its length); tab says it is a tab (else an LF).
type Tb is Type:
  Tb{b: D.Bytes, j: U32, part: Bool, tab: Bool}

# The ends of CHROM .. INFO (the tab after each, or the LF after INFO) and the
# line's LF. Short: an LF comes before the 7th tab (fewer than 8 fields).
# Part: no LF before the buffer's end (the line is not complete).
type Cut is Data:
  Cut8{e0: U32, e1: U32, e2: U32, e3: U32, e4: U32, e5: U32, e6: U32, e7: U32, lf: U32}
  Short{}
  Part{}

type Cr is Type:
  Cr{b: D.Bytes, c: Cut}

type Bv is Type:
  Bv{b: D.Bytes, ok: Bool, v: U32}

# ---------------------------------------------------------------------------
# The alleles: REF and every ALT upper-case A, C, G, T, N; not all ending
# with the same base; not all starting with the same base while all have two
# or more; no two equal (tan.bend's var_in then leaves the variant as it is)
# ---------------------------------------------------------------------------

# What is known of the alleles so far: the REF at s3 (l3 bytes, first f3,
# last z3), the ALT field from s4 to e4.
type Al is Data:
  Al{s3: U32, l3: U32, f3: U32, z3: U32, s4: U32, e4: U32}

type Ab is Type:
  Ab{b: D.Bytes, ok: Bool, lasts: Bool, firsts: Bool, long: Bool}

# ---------------------------------------------------------------------------
# INFO has no END entry (an entry whose key, the text before its first '=',
# is END): norm_fix.bend's test, and the fast path's quick one (then ends,
# below)
# ---------------------------------------------------------------------------

type B4 is Type:
  B4{b: D.Bytes, p: U32, n: U32, d: U32, q: U32}

# ---------------------------------------------------------------------------
# A record line, all tests on its own bytes
# ---------------------------------------------------------------------------

# Pass: the record passed every test on its own bytes; pos: its POS; e0 ..
# e7: the ends of CHROM .. INFO (field i is from e(i-1) + 1, CHROM from s, to
# ei - 1); lf: its LF. Skip: the record is out of scope and not malformed
# (given a CHROM that is not empty, which norm.bend tests), the same fields.
type Pre is Data:
  Pass{pos: U32, e0: U32, e1: U32, e2: U32, e3: U32, e4: U32, e5: U32, e6: U32, e7: U32, lf: U32}
  Slow{}
  Incomplete{}
  Skip{pos: U32, e0: U32, e1: U32, e2: U32, e3: U32, e4: U32, e5: U32, e6: U32, e7: U32, lf: U32}

type Pr is Type:
  Pr{b: D.Bytes, p: Pre}

# ---------------------------------------------------------------------------
# Loops: a state, one step (not recursive), and the loop over a fuel
# ---------------------------------------------------------------------------

# Looking for the allele at x (lx bytes) among the comma-separated alleles of
# a .. e-1: found it; more: there is another one to look at.
type Dp is Type:
  Dp{b: D.Bytes, x: U32, lx: U32, a: U32, e: U32, found: Bool, more: Bool}

# The ALT alleles from a on: ok so far, and the flags so far.
type As is Type:
  As{b: D.Bytes, al: Al, a: U32, ok: Bool, lasts: Bool, firsts: Bool, long: Bool, more: Bool}

# Looking for an END entry in INFO (from .. to-1) at each 'E' from x on.
type Ne is Type:
  Ne{b: D.Bytes, from: U32, to: U32, x: U32, ok: Bool, more: Bool}

def tab.fin(+j: U32, +len: U32, r: D.Bytes & U32) -> Tb:
  (b, +c) = r
  Tb{b, j, U32.is_eq(j, len), U32.is_eq(c, 9)}

def tab.k(+len: U32, r: D.Bytes & U32) -> Tb:
  (b, +j) = r
  tab.fin(j, len, BY.at(b, j))

def tab(b: D.Bytes, +s: U32) -> Tb:
  D.Bytes{+len, buf} = b
  tab.k(len, F.find2(D.Bytes{len, buf}, s, len, 9, 10))

def lf.k(+len: U32, r: D.Bytes & U32) -> Tb:
  (b, +j) = r
  Tb{b, j, U32.is_eq(j, len), False{}}

# The first LF at or after s (as tab, with tab False).
def lf(b: D.Bytes, +s: U32) -> Tb:
  D.Bytes{+len, buf} = b
  lf.k(len, F.find(D.Bytes{len, buf}, s, len, 10))

def k8(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, +j, False{}, x}:
      Cr{b, Cut8{e0, e1, e2, e3, e4, e5, e6, e7, j}}

def k7(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, +j, False{}, False{}}:
      Cr{b, Cut8{e0, e1, e2, e3, e4, e5, e6, j, j}}
    case Tb{b, +j, False{}, True{}}:
      k8(e0, e1, e2, e3, e4, e5, e6, j, lf(b, (j + 1 : U32)))

def k6(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k7(e0, e1, e2, e3, e4, e5, j, tab(b, (j + 1 : U32)))

def k5(+e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k6(e0, e1, e2, e3, e4, j, tab(b, (j + 1 : U32)))

def k4(+e0: U32, +e1: U32, +e2: U32, +e3: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k5(e0, e1, e2, e3, j, tab(b, (j + 1 : U32)))

def k3(+e0: U32, +e1: U32, +e2: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k4(e0, e1, e2, j, tab(b, (j + 1 : U32)))

def k2(+e0: U32, +e1: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k3(e0, e1, j, tab(b, (j + 1 : U32)))

def k1(+e0: U32, t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k2(e0, j, tab(b, (j + 1 : U32)))

def k0(t: Tb) -> Cr:
  match t:
    case Tb{b, j, True{}, x}:
      Cr{b, Part{}}
    case Tb{b, j, False{}, False{}}:
      Cr{b, Short{}}
    case Tb{b, +j, False{}, True{}}:
      k1(j, tab(b, (j + 1 : U32)))

# The line starting at s, cut into its first 8 fields.
def cut(b: D.Bytes, +s: U32) -> Cr:
  k0(tab(b, s))

# ---------------------------------------------------------------------------
# Byte tests
# ---------------------------------------------------------------------------

# An upper-case A, C, G, T or N.
def is_base(+x: U32) -> Bool:
  U32.is_eq(x, 65) || U32.is_eq(x, 67) || U32.is_eq(x, 71) || U32.is_eq(x, 84) || U32.is_eq(x, 78)

def is_digit(+x: U32) -> Bool:
  U32.is_ge(x, 48) && U32.is_le(x, 57)

def num.go(n: Nat, r: D.Bytes & U32, +j: U32, +acc: U32, ok: Bool) -> Bv:
  match n:
    case 0n:
      (b, x) = r
      Bv{b, ok, acc}
    case 1n+m:
      (b, +x) = r
      num.go(m, BY.at(b, (j + 1 : U32)), (j + 1 : U32), ((acc * 10 : U32) + (x - 48 : U32) : U32), ok && is_digit(x))

def num.k(+from: U32, +n: U32, r: D.Bytes & U32) -> Bv:
  (b, +x) = r
  num.go(U32.to_nat(U32.min(n, 10)), (b, x), from, 0, U32.is_le(1, n) && U32.is_le(n, 9) && Bool.not(U32.is_eq(x, 48)))

# Bytes from .. to-1 are a POS written as Nat.show writes it (1 to 9 digits,
# no leading zero), and its value.
def num(b: D.Bytes, +from: U32, +to: U32) -> Bv:
  num.k(from, (to - from : U32), BY.at(b, from))

# Bytes from .. to-1 are all upper-case A, C, G, T or N; v: the last one
# (x if there are none).
def bases.go(n: Nat, r: D.Bytes & U32, +j: U32, ok: Bool, +x: U32) -> Bv:
  match n:
    case 0n:
      (b, y) = r
      Bv{b, ok, x}
    case 1n+m:
      (b, +y) = r
      bases.go(m, BY.at(b, (j + 1 : U32)), (j + 1 : U32), ok && is_base(y), y)

def bases(b: D.Bytes, +from: U32, +to: U32) -> Bv:
  bases.go(U32.to_nat((to - from : U32)), BY.at(b, from), from, True{}, 0)

def eqa.if(same_len: Bool, b: D.Bytes, +i: U32, +j: U32, +n: U32) -> D.Bytes & Bool:
  match same_len:
    case True{}:
      BY.same1(b, i, j, n)
    case False{}:
      (b, False{})

# The alleles at i (n bytes) and j (m bytes) are equal.
def eqa(b: D.Bytes, +i: U32, +n: U32, +j: U32, +m: U32) -> D.Bytes & Bool:
  eqa.if(U32.is_eq(n, m), b, i, j, n)

def Al.f3(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      f3

def Al.z3(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      z3

def alt.fin(+al: Al, +a: U32, +c: U32, ok: Bool, +f: U32, +z: U32, lasts: Bool, firsts: Bool, long: Bool, r: D.Bytes & Bool) -> Ab:
  (b, dup) = r
  Ab{b, ok && Bool.not(dup), lasts && U32.is_eq(z, Al.z3(al)), firsts && U32.is_eq(f, Al.f3(al)), long && U32.is_le(2, (c - a : U32))}

def Al.s4(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      s4

def dup.eq(+x: U32, +lx: U32, +e: U32, +c: U32, r: D.Bytes & Bool) -> Dp:
  (b, +eq) = r
  Dp{b, x, lx, (c + 1 : U32), e, eq, Bool.not(eq) && U32.is_lt(c, e)}

def dup.c(+x: U32, +lx: U32, +a: U32, +e: U32, r: D.Bytes & U32) -> Dp:
  (b, +c) = r
  dup.eq(x, lx, e, c, eqa(b, x, lx, a, (c - a : U32)))

def dup.step(d: Dp) -> Dp:
  match d:
    case Dp{b, +x, +lx, +a, +e, f, m}:
      dup.c(x, lx, a, e, F.find(b, a, e, 44))

def dup.go(n: Nat, d: Dp) -> D.Bytes & Bool:
  match n d:
    case 0n Dp{b, x, lx, a, e, f, m}:
      (b, f)
    case 1n+k Dp{b, x, lx, a, e, f, False{}}:
      (b, f)
    case 1n+k Dp{b, x, lx, a, e, f, True{}}:
      dup.go(k, dup.step(Dp{b, x, lx, a, e, f, True{}}))

# Some comma-separated allele in a .. e-1 equals the one at x (lx bytes);
# more: a .. e-1 is not empty.
def dup(more: Bool, b: D.Bytes, +x: U32, +lx: U32, +a: U32, +e: U32) -> D.Bytes & Bool:
  dup.go(16n, Dp{b, x, lx, a, e, False{}, more})

def alt.dup(+al: Al, +a: U32, +c: U32, ok: Bool, +f: U32, +z: U32, lasts: Bool, firsts: Bool, long: Bool, r: D.Bytes & Bool) -> Ab:
  (b, +eqref) = r
  alt.fin(al, a, c, ok && Bool.not(eqref), f, z, lasts, firsts, long, dup(U32.is_lt(Al.s4(al), a), b, a, (c - a : U32), Al.s4(al), (a - 1 : U32)))

def Al.s3(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      s3

def Al.l3(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      l3

def alt.ref(+al: Al, +a: U32, +c: U32, ok: Bool, +f: U32, +z: U32, lasts: Bool, firsts: Bool, long: Bool, b: D.Bytes) -> Ab:
  alt.dup(al, a, c, ok, f, z, lasts, firsts, long, eqa(b, a, (c - a : U32), Al.s3(al), Al.l3(al)))

def alt.bases(+al: Al, +a: U32, +c: U32, +f: U32, lasts: Bool, firsts: Bool, long: Bool, v: Bv) -> Ab:
  match v:
    case Bv{b, ok, +z}:
      alt.ref(al, a, c, ok && U32.is_lt(a, c), f, z, lasts, firsts, long, b)

def alt.first(+al: Al, +a: U32, +c: U32, lasts: Bool, firsts: Bool, long: Bool, r: D.Bytes & U32) -> Ab:
  (b, +f) = r
  alt.bases(al, a, c, f, lasts, firsts, long, bases(b, a, c))

# One ALT allele, a .. c-1.
def alt(+al: Al, +a: U32, +c: U32, lasts: Bool, firsts: Bool, long: Bool, b: D.Bytes) -> Ab:
  alt.first(al, a, c, lasts, firsts, long, BY.at(b, a))

def Al.e4(al: Al) -> U32:
  match al:
    case Al{s3, l3, f3, z3, s4, e4}:
      e4

def alts.ab(+al: Al, +c: U32, ab: Ab) -> As:
  match ab:
    case Ab{b, +ok, lasts, firsts, long}:
      As{b, al, (c + 1 : U32), ok, lasts, firsts, long, ok && U32.is_lt(c, Al.e4(al))}

def alts.c(+al: Al, +a: U32, lasts: Bool, firsts: Bool, long: Bool, r: D.Bytes & U32) -> As:
  (b, +c) = r
  alts.ab(al, c, alt(al, a, c, lasts, firsts, long, b))

def alts.step(x: As) -> As:
  match x:
    case As{b, +al, +a, ok, lasts, firsts, long, m}:
      alts.c(al, a, lasts, firsts, long, F.find(b, a, Al.e4(al), 44))

def alts.go(n: Nat, x: As) -> D.Bytes & Bool:
  match n x:
    case 0n As{b, al, a, ok, lasts, firsts, long, m}:
      (b, False{})
    case 1n+k As{b, al, a, ok, lasts, firsts, long, False{}}:
      (b, ok && Bool.not(lasts) && Bool.not(firsts && long))
    case 1n+k As{b, al, a, ok, lasts, firsts, long, True{}}:
      alts.go(k, alts.step(As{b, al, a, ok, lasts, firsts, long, True{}}))

def alleles.k(+s3: U32, +e3: U32, +s4: U32, +e4: U32, +f3: U32, v: Bv) -> D.Bytes & Bool:
  match v:
    case Bv{b, ok, +z3}:
      +l3 = (e3 - s3 : U32)
      +go = ok && U32.is_lt(s3, e3) && U32.is_lt(s4, e4)
      alts.go(17n, As{b, Al{s3, l3, f3, z3, s4, e4}, s4, go, True{}, True{}, U32.is_le(2, l3), go})

def alleles.f(+s3: U32, +e3: U32, +s4: U32, +e4: U32, r: D.Bytes & U32) -> D.Bytes & Bool:
  (b, +f3) = r
  alleles.k(s3, e3, s4, e4, f3, bases(b, s3, e3))

# REF (s3 .. e3-1) and ALT (s4 .. e4-1) as the fast path needs them (at most
# 16 ALT alleles; more go the slow way).
def alleles(b: D.Bytes, +s3: U32, +e3: U32, +s4: U32, +e4: U32) -> D.Bytes & Bool:
  alleles.f(s3, e3, s4, e4, BY.at(b, s3))

def b4.q(+p: U32, +n: U32, +d: U32, r: D.Bytes & U32) -> B4:
  (b, +q) = r
  B4{b, p, n, d, q}

def b4.d(+p: U32, +n: U32, +j: U32, r: D.Bytes & U32) -> B4:
  (b, +d) = r
  b4.q(p, n, d, BY.at(b, (j + 3 : U32)))

def b4.n(+p: U32, +j: U32, r: D.Bytes & U32) -> B4:
  (b, +n) = r
  b4.d(p, n, j, BY.at(b, (j + 2 : U32)))

def b4.p(+j: U32, r: D.Bytes & U32) -> B4:
  (b, +p) = r
  b4.n(p, j, BY.at(b, (j + 1 : U32)))

# Bytes j-1, j+1, j+2, j+3.
def b4(b: D.Bytes, +j: U32) -> B4:
  b4.p(j, BY.at(b, (j - 1 : U32)))

def pre.if(ok: Bool, b: D.Bytes, +p: Pre) -> Pr:
  match ok:
    case True{}:
      Pr{b, p}
    case False{}:
      Pr{b, Slow{}}

def pre.cr(+pos: U32, +c: Cut, r: D.Bytes & U32) -> Pr:
  match c:
    case Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      (b, +x) = r
      pre.if(Bool.not(U32.is_eq(e7, lf) && U32.is_eq(x, 13)), b, Pass{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf})
    case _:
      (b, x) = r
      Pr{b, Slow{}}

def Cut.lf(c: Cut) -> U32:
  match c:
    case Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}:
      lf
    case _:
      0

def pre.info.if(ok: Bool, +pos: U32, +c: Cut, b: D.Bytes) -> Pr:
  match ok:
    case True{}:
      pre.cr(pos, c, BY.at(b, (Cut.lf(c) - 1 : U32)))
    case False{}:
      Pr{b, Slow{}}

def pre.info(+pos: U32, +c: Cut, r: D.Bytes & Bool) -> Pr:
  (b, ok) = r
  pre.info.if(ok, pos, c, b)

def noend.e(+from: U32, +to: U32, +j: U32, q: B4) -> Ne:
  match q:
    case B4{b, +p, +nn, +d, +qq}:
      +start = U32.is_eq(j, from) || U32.is_eq(p, 59)
      +key = U32.is_eq(nn, 78) && U32.is_eq(d, 68) && (U32.is_eq((j + 3 : U32), to) || U32.is_eq(qq, 61) || U32.is_eq(qq, 59))
      +end = start && key
      Ne{b, from, to, (j + 1 : U32), Bool.not(end), Bool.not(end)}

def noend.if(none: Bool, b: D.Bytes, +from: U32, +to: U32, +j: U32) -> Ne:
  match none:
    case True{}:
      Ne{b, from, to, j, True{}, False{}}
    case False{}:
      noend.e(from, to, j, b4(b, j))

def noend.k(+from: U32, +to: U32, r: D.Bytes & U32) -> Ne:
  (b, +j) = r
  noend.if(U32.is_eq(j, to), b, from, to, j)

def noend.step(x: Ne) -> Ne:
  match x:
    case Ne{b, +from, +to, +y, ok, m}:
      noend.k(from, to, F.find(b, y, to, 69))

def noend.go(n: Nat, x: Ne) -> D.Bytes & Bool:
  match n x:
    case 0n Ne{b, f, t, y, ok, m}:
      (b, False{})
    case 1n+k Ne{b, f, t, y, ok, False{}}:
      (b, ok)
    case 1n+k Ne{b, f, t, y, ok, True{}}:
      noend.go(k, noend.step(Ne{b, f, t, y, ok, True{}}))

# INFO (from .. to-1) has no END entry.
def noend(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Bool:
  noend.go(U32.to_nat((to - from + 2 : U32)), Ne{b, from, to, from, True{}, True{}})

# ---------------------------------------------------------------------------
# INFO's END entries: none, or exactly one, END=<digits> as num reads them
# (1 to 9 digits, no leading zero), with the value POS + len(REF) - 1
# (B.Info.end_ok). The entries are the pieces between ';'; an entry's key is
# the text before its first '=' (B.Info.key).
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

def key3.if(three: Bool, b: D.Bytes, +j: U32) -> D.Bytes & Bool:
  match three:
    case True{}:
      lit.go([69, 78, 68], (b, True{}), j)
    case False{}:
      (b, False{})

# The n bytes from j are END.
def key3(b: D.Bytes, +j: U32, +n: U32) -> D.Bytes & Bool:
  key3.if(U32.is_eq(n, 3), b, j)

# At the entry starting at j (INFO ends at to; pos: POS, rl: REF's length):
# every END entry so far had the value pos + rl - 1 (ok); one was seen
# (seen); another entry to look at (more).
type Ek is Type:
  Ek{b: D.Bytes, j: U32, to: U32, pos: U32, rl: U32, ok: Bool, seen: Bool, more: Bool}

# After an entry ending at sm (a ';', or INFO's end).
def ek.w(+ok: Bool, seen: Bool, end: Bool, b: D.Bytes, +sm: U32, +to: U32, +pos: U32, +rl: U32) -> Ek:
  match end:
    case True{}:
      Ek{b, sm, to, pos, rl, ok, seen, False{}}
    case False{}:
      Ek{b, (sm + 1 : U32), to, pos, rl, ok, seen, ok}

def ek.v(ok: Bool, seen: Bool, +to: U32, +pos: U32, +rl: U32, r: D.Bytes & U32) -> Ek:
  (b, +sm) = r
  ek.w(ok, seen, U32.is_eq(sm, to), b, sm, to, pos, rl)

# The END value v is pos + rl - 1 (as v - pos == rl - 1, with pos <= v and
# 1 <= rl: no word wraps).
def ek.val.k(ok: Bool, seen: Bool, +sm: U32, +to: U32, +pos: U32, +rl: U32, v: Bv) -> Ek:
  match v:
    case Bv{b, vok, +x}:
      +good = ok && Bool.not(seen) && vok && U32.is_le(pos, x) && U32.is_le(1, rl) && U32.is_eq((x - pos : U32), (rl - 1 : U32))
      ek.w(good, True{}, U32.is_eq(sm, to), b, sm, to, pos, rl)

# An END entry with its '=' at ke: its value is the bytes up to the next ';'.
def ek.val(ok: Bool, seen: Bool, +ke: U32, +to: U32, +pos: U32, +rl: U32, r: D.Bytes & U32) -> Ek:
  (b, +sm) = r
  ek.val.k(ok, seen, sm, to, pos, rl, num(b, (ke + 1 : U32), sm))

def ek.e(+ok: Bool, seen: Bool, isend: Bool, end: Bool, semi: Bool, b: D.Bytes, +ke: U32, +to: U32, +pos: U32, +rl: U32) -> Ek:
  match isend end semi:
    case False{} True{} _:
      Ek{b, ke, to, pos, rl, ok, seen, False{}}
    case False{} False{} True{}:
      Ek{b, (ke + 1 : U32), to, pos, rl, ok, seen, ok}
    case False{} False{} False{}:
      ek.v(ok, seen, to, pos, rl, F.find(b, ke, to, 59))
    case True{} False{} False{}:
      ek.val(ok, seen, ke, to, pos, rl, F.find(b, ke, to, 59))
    case True{} _ _:
      Ek{b, ke, to, pos, rl, False{}, seen, False{}}

def ek.n(ok: Bool, seen: Bool, isend: Bool, +ke: U32, +to: U32, +pos: U32, +rl: U32, r: D.Bytes & U32) -> Ek:
  (b, +y) = r
  ek.e(ok, seen, isend, U32.is_eq(ke, to), U32.is_eq(y, 59), b, ke, to, pos, rl)

def ek.h(ok: Bool, seen: Bool, +ke: U32, +to: U32, +pos: U32, +rl: U32, r: D.Bytes & Bool) -> Ek:
  (b, isend) = r
  ek.n(ok, seen, isend, ke, to, pos, rl, BY.at(b, ke))

def ek.k(+j: U32, +to: U32, ok: Bool, seen: Bool, +pos: U32, +rl: U32, r: D.Bytes & U32) -> Ek:
  (b, +ke) = r
  ek.h(ok, seen, ke, to, pos, rl, key3(b, j, (ke - j : U32)))

# The entry at j: its key ends at the first '=' or ';' (or INFO's end); the
# next entry starts after the next ';'.
def ek.step(x: Ek) -> Ek:
  match x:
    case Ek{b, +j, +to, +pos, +rl, ok, seen, m}:
      ek.k(j, to, ok, seen, pos, rl, F.find2(b, j, to, 61, 59))

def ek.go(n: Nat, x: Ek) -> D.Bytes & Bool:
  match n x:
    case 0n Ek{b, j, to, pos, rl, ok, seen, m}:
      (b, False{})
    case 1n+k Ek{b, j, to, pos, rl, ok, seen, False{}}:
      (b, ok)
    case 1n+k Ek{b, j, to, pos, rl, ok, seen, True{}}:
      ek.go(k, ek.step(Ek{b, j, to, pos, rl, ok, seen, True{}}))

# INFO's END entries (from .. to-1) as B.Info.end_ok asks for POS pos and a
# REF of rl bytes.
def ends(b: D.Bytes, +from: U32, +to: U32, +pos: U32, +rl: U32) -> D.Bytes & Bool:
  ek.go(U32.to_nat((to - from + 2 : U32)), Ek{b, from, to, pos, rl, True{}, False{}, True{}})

# ---------------------------------------------------------------------------
# Out of scope (B.Rec.out_of_scope), and not malformed (B.Rec.malformed) but
# for CHROM: REF is one or more letters, no ALT allele (the pieces between
# commas) is empty, and some ALT allele is not all letters
# ---------------------------------------------------------------------------

def alpha(+x: U32) -> Bool:
  Char.is_alpha(Chr{x})

def letters.go(n: Nat, r: D.Bytes & U32, +j: U32, ok: Bool) -> D.Bytes & Bool:
  match n:
    case 0n:
      (b, x) = r
      (b, ok)
    case 1n+m:
      (b, +x) = r
      letters.go(m, BY.at(b, (j + 1 : U32)), (j + 1 : U32), ok && alpha(x))

# Bytes from .. to-1 are all letters.
def letters(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Bool:
  letters.go(U32.to_nat((to - from : U32)), BY.at(b, from), from, True{})

# The ALT alleles from a on (the field ends at e): none empty so far (ok);
# one not all letters so far (odd); another one to read.
type Ks is Type:
  Ks{b: D.Bytes, a: U32, e: U32, ok: Bool, odd: Bool, more: Bool}

def ks.l(+c: U32, +e: U32, +a: U32, ok: Bool, odd: Bool, r: D.Bytes & Bool) -> Ks:
  (b, lets) = r
  +ok2 = ok && U32.is_lt(a, c)
  Ks{b, (c + 1 : U32), e, ok2, odd || Bool.not(lets), ok2 && U32.is_lt(c, e)}

def ks.c(+a: U32, +e: U32, ok: Bool, odd: Bool, r: D.Bytes & U32) -> Ks:
  (b, +c) = r
  ks.l(c, e, a, ok, odd, letters(b, a, c))

# One ALT allele: up to the next comma, or the field's end.
def ks.step(x: Ks) -> Ks:
  match x:
    case Ks{b, +a, +e, ok, odd, m}:
      ks.c(a, e, ok, odd, F.find(b, a, e, 44))

def ks.go(n: Nat, x: Ks) -> D.Bytes & Bool:
  match n x:
    case 0n Ks{b, a, e, ok, odd, m}:
      (b, False{})
    case 1n+k Ks{b, a, e, ok, odd, False{}}:
      (b, ok && odd)
    case 1n+k Ks{b, a, e, ok, odd, True{}}:
      ks.go(k, ks.step(Ks{b, a, e, ok, odd, True{}}))

# ALT (from .. to-1): no allele is empty, and some allele is not all letters.
def oos(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Bool:
  ks.go(U32.to_nat((to - from + 2 : U32)), Ks{b, from, to, True{}, False{}, True{}})

def sk.if(ok: Bool, b: D.Bytes, +p: Pre) -> Pr:
  match ok:
    case True{}:
      Pr{b, p}
    case False{}:
      Pr{b, Slow{}}

def sk.cr(+pos: U32, +c: Cut, r: D.Bytes & U32) -> Pr:
  match c:
    case Cut8{+e0, +e1, +e2, +e3, +e4, +e5, +e6, +e7, +lf}:
      (b, +x) = r
      sk.if(Bool.not(U32.is_eq(e7, lf) && U32.is_eq(x, 13)), b, Skip{pos, e0, e1, e2, e3, e4, e5, e6, e7, lf})
    case _:
      (b, x) = r
      Pr{b, Slow{}}

def sk.alt(+pos: U32, +c: Cut, r: D.Bytes & Bool) -> Pr:
  (b, ok) = r
  match ok:
    case True{}:
      sk.cr(pos, c, BY.at(b, (Cut.lf(c) - 1 : U32)))
    case False{}:
      Pr{b, Slow{}}

def sk.ref.if(ok: Bool, +pos: U32, +c: Cut, +s4: U32, +e4: U32, b: D.Bytes) -> Pr:
  match ok:
    case True{}:
      sk.alt(pos, c, oos(b, s4, e4))
    case False{}:
      Pr{b, Slow{}}

def sk.ref(+pos: U32, +c: Cut, +ne: Bool, +s4: U32, +e4: U32, r: D.Bytes & Bool) -> Pr:
  (b, lets) = r
  sk.ref.if(ne && lets, pos, c, s4, e4, b)

# INFO passes the END check: it has no END entry (noend, the quick test), or
# its END entries pass ends.
def pre.info.ne.k(none: Bool, +pos: U32, +c: Cut, b: D.Bytes) -> Pr:
  match none c:
    case True{} _:
      pre.info.if(True{}, pos, c, b)
    case False{} Cut8{e0, e1, +e2, +e3, e4, e5, +e6, +e7, lf}:
      pre.info(pos, c, ends(b, (e6 + 1 : U32), e7, pos, (e3 - e2 - 1 : U32)))
    case False{} _:
      Pr{b, Slow{}}

def pre.info.ne(+pos: U32, +c: Cut, r: D.Bytes & Bool) -> Pr:
  (b, none) = r
  pre.info.ne.k(none, pos, c, b)

def pre.al.if(ok: Bool, +pos: U32, +c: Cut, b: D.Bytes) -> Pr:
  match ok c:
    case True{} Cut8{e0, e1, e2, e3, e4, e5, +e6, +e7, lf}:
      pre.info.ne(pos, c, noend(b, (e6 + 1 : U32), e7))
    case False{} Cut8{e0, e1, +e2, +e3, +e4, e5, e6, e7, lf}:
      sk.ref(pos, c, U32.is_lt((e2 + 1 : U32), e3), (e3 + 1 : U32), e4, letters(b, (e2 + 1 : U32), e3))
    case _ _:
      Pr{b, Slow{}}

def pre.al(+pos: U32, +c: Cut, r: D.Bytes & Bool) -> Pr:
  (b, ok) = r
  pre.al.if(ok, pos, c, b)

def pre.pos(+c: Cut, v: Bv) -> Pr:
  match c v:
    case Cut8{e0, e1, +e2, +e3, +e4, e5, e6, e7, lf} Bv{b, True{}, +pos}:
      pre.al(pos, c, alleles(b, (e2 + 1 : U32), e3, (e3 + 1 : U32), e4))
    case _ Bv{b, _, pos}:
      Pr{b, Slow{}}

# The tests on a record's own bytes (the CHROM run and the reference are
# tested by norm.bend).
def pre(+s: U32, r: Cr) -> Pr:
  match r:
    case Cr{b, Cut8{+e0, +e1, e2, e3, e4, e5, e6, e7, lf}}:
      pre.pos(Cut8{e0, e1, e2, e3, e4, e5, e6, e7, lf}, num(b, (e0 + 1 : U32), e1))
    case Cr{b, Short{}}:
      Pr{b, Slow{}}
    case Cr{b, Part{}}:
      Pr{b, Incomplete{}}

# The line at s: cut, then tested.
def line(b: D.Bytes, +s: U32) -> Pr:
  pre(s, cut(b, s))

# ---------------------------------------------------------------------------
# Comparisons with other buffers
# ---------------------------------------------------------------------------

def same.if(eq_len: Bool, a: D.Bytes, +i: U32, c: D.Bytes, +n: U32) -> D.Bytes & (D.Bytes & Bool):
  match eq_len:
    case True{}:
      BY.same(a, i, c, 0, n)
    case False{}:
      (a, (c, False{}))

def same.k(a: D.Bytes, +i: U32, +n: U32, r: D.Bytes & U32) -> D.Bytes & (D.Bytes & Bool):
  (c, +m) = r
  same.if(U32.is_eq(n, m), a, i, c, n)

# Bytes i .. i+n-1 of a are all of c (c's length is n).
def same(a: D.Bytes, +i: U32, +n: U32, c: D.Bytes) -> D.Bytes & (D.Bytes & Bool):
  same.k(a, i, n, BY.len(c))

def refeq.k(n: Nat, +i: U32, +j: U32, acc: Bool, ra: D.Bytes & U32, rb: D.Bytes & U32) -> D.Bytes & (D.Bytes & Bool):
  match n:
    case 0n:
      (a, x) = ra
      (c, y) = rb
      (a, (c, acc))
    case 1n+m:
      (a, +x) = ra
      (c, +y) = rb
      refeq.k(m, (i + 1 : U32), (j + 1 : U32), acc && U32.is_zero(((x .^. y : U32) .&. 223 : U32)), BY.at(a, (i + 1 : U32)), BY.at(c, (j + 1 : U32)))

# REF (n upper-case letters from i in a) against the reference letters from
# j in c, either case.
def refeq(a: D.Bytes, +i: U32, c: D.Bytes, +j: U32, +n: U32) -> D.Bytes & (D.Bytes & Bool):
  refeq.k(U32.to_nat(n), i, j, True{}, BY.at(a, i), BY.at(c, j))
