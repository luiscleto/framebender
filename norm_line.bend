import Base
import ./types.bend as B
import ./protocol.bend as P
import ./tan.bend as V

# framebender: the result for one body line, reading the reference through a
# window (code, not spec). The normalizer is the spec's (tan.bend, V.var_in on
# the window).

# What the program knows of one reference read, as text (the machine decodes
# the packed answers it gets, protocol.bend's P.Ans, into this): the contig is
# not in the reference; or it has clen letters, and raw holds its letters as
# written from 0-based index off.
type Ans is Data:
  Unknown{}
  Known{clen: Nat, off: Nat, raw: String}

# ---------------------------------------------------------------------------
# INFO/END (B.Info.end_ok, without splitting INFO into its entries)
# ---------------------------------------------------------------------------

# The lazy copies below take an ok flag for the first character, so the copy
# stops there; a strict helper taking the recursive call would copy the rest.

def piece.ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Bool.not(Char.is_eq(h, ';'))

def piece.go(s: String, ok: Bool) -> String:
  match s ok:
    case SNil{} _:
      SNil{}
    case SCon{h, +t} True{}:
      SCon{h, piece.go(t, piece.ok(t))}
    case SCon{h, t} False{}:
      SNil{}

# The first INFO entry of s: the text before the first ';'.
def piece(+s: String) -> String:
  piece.go(s, piece.ok(s))

def ikey.ok2(semi: Bool, eq: Bool) -> Bool:
  match semi eq:
    case False{} False{}:
      True{}
    case False{} True{}:
      False{}
    case True{} _:
      False{}

def ikey.ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      ikey.ok2(Char.is_eq(h, ';'), Char.is_eq(h, '='))

def ikey.go(s: String, ok: Bool) -> String:
  match s ok:
    case SNil{} _:
      SNil{}
    case SCon{h, +t} True{}:
      SCon{h, ikey.go(t, ikey.ok(t))}
    case SCon{h, t} False{}:
      SNil{}

# The key of the first INFO entry of s (B.Info.key of piece(s)).
def ikey(+s: String) -> String:
  ikey.go(s, ikey.ok(s))

# What an entry adds to B.Info.ends: its value if it is an END entry.
def end_val(is_end: Bool, +s: String) -> Maybe<&2, Maybe<&2, Nat>>:
  match is_end:
    case True{}:
      Some{B.Pos.read(String.drop(piece(s), 4n))}
    case False{}:
      None{}

def scan.put(m: Maybe<&2, Maybe<&2, Nat>>, rest: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match m:
    case None{}:
      rest
    case Some{v}:
      v <> rest

# B.Info.ends of the entries of s, one character at a time; start: s begins
# an entry (else the rest of the current entry is skipped).
def scan(s: String, start: Bool) -> List<&2, Maybe<&2, Nat>>:
  match s start:
    case SNil{} _:
      Nil{}
    case SCon{+h, +t} True{}:
      scan.put(end_val(String.eq(ikey(SCon{h, t}), "END"), SCon{h, t}), scan(t, Char.is_eq(h, ';')))
    case SCon{h, t} False{}:
      scan(t, Char.is_eq(h, ';'))

# B.Info.end_ok, computed with scan.
def end_ok(info: String, +e: Nat) -> Bool:
  B.Info.end_ok.go(scan(info, True{}), e)

# ---------------------------------------------------------------------------
# One body line, reading the contig through what the reference answered
# ---------------------------------------------------------------------------

def mk(o: B.Outcome, +fs: List<&2, String>, body: String) -> B.Res:
  B.Res{o, B.Rec.pos(fs), body, False{}}

def found.norm(m: Maybe<&2, B.Var>, +fs: List<&2, String>, +v: B.Var) -> Maybe<&2, B.Res>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)}}

def ref_check.go(fits: Bool, covered: Bool, eq: Bool) -> Maybe<&2, Bool>:
  match fits covered:
    case False{} _:
      Some{False{}}
    case True{} False{}:
      None{}
    case True{} True{}:
      Some{eq}

# The REF check through the window: Some(True) matches, Some(False) does not
# (also when REF runs past the contig end), None: the window does not hold it.
def ref_check(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +start: Nat, +ref: List<&2, B.Base>) -> Maybe<&2, Bool>:
  +n = List.length(&2, B.Base, ref)
  +fits = Nat.is_le(Nat.add(start, n), clen)
  +covered = Nat.is_le(off, start) && Nat.is_le(Nat.add(start, n), Nat.add(off, List.length(&2, B.Base, bases)))
  ref_check.go(fits, covered, B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(start, off)), n), ref))

def found.ref(ok: Maybe<&2, Bool>, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match ok:
    case None{}:
      None{}
    case Some{False{}}:
      Some{mk(B.Problem{B.RefMismatch{}}, fs, body)}
    case Some{True{}}:
      found.norm(V.var_in(off, bases, v), fs, v)

def found.problem(zero: Bool, distinct: Bool, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match zero distinct:
    case True{} _:
      Some{mk(B.Problem{B.BadPos{}}, fs, body)}
    case False{} False{}:
      Some{mk(B.Problem{B.AltDup{}}, fs, body)}
    case False{} True{}:
      match v:
        case B.Var{+p, +r, +a}:
          found.ref(ref_check(clen, off, bases, Nat.sub(p, 1n), r), off, bases, fs, body, B.Var{p, r, a})

def found.var(+clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String, +v: B.Var) -> Maybe<&2, B.Res>:
  match v:
    case B.Var{+p, +r, +a}:
      found.problem(Nat.is_eq(p, 0n), B.Alleles.distinct(r <> a), clen, off, bases, fs, body, B.Var{p, r, a})

def found(end_ok: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match end_ok r a:
    case False{} _ _:
      Some{mk(B.Problem{B.BadEnd{}}, fs, body)}
    case True{} Some{ref} Some{alts}:
      found.var(clen, off, bases, fs, body, B.Var{B.Rec.pos(fs), ref, alts})
    case True{} _ _:
      Some{mk(B.Problem{B.NonAcgtn{}}, fs, body)}

# a: what the reference answered (None: nothing was read yet).
def judge_in.ans(a: Maybe<&2, Ans>, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match a:
    case None{}:
      None{}
    case Some{Unknown{}}:
      Some{mk(B.NoContig{}, fs, body)}
    case Some{Known{+clen, +off, raw}}:
      +bases = B.Bases.of_fasta(raw)
      +ref = B.Rec.field(fs, 3n)
      e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      found(end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, bases, fs, body)

def judge_in.go(bad: Bool, skip: Bool, a: Maybe<&2, Ans>, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match bad skip:
    case True{} _:
      Some{mk(B.Broken{}, fs, body)}
    case False{} True{}:
      Some{mk(B.Skipped{}, fs, body)}
    case False{} False{}:
      judge_in.ans(a, fs, body)

# judge_in with the line's fields already split (fs = B.Rec.fields(body)).
def judge_fs(a: Maybe<&2, Ans>, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  judge_in.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), a, fs, body)

# The result for one body line (its text without terminator), given what the
# reference answered for the line's CHROM (None: nothing read); None when the
# answer is not enough (the machine then asks for more).
def judge_in(a: Maybe<&2, Ans>, +body: String) -> Maybe<&2, B.Res>:
  judge_fs(a, B.Rec.fields(body), body)

# ---------------------------------------------------------------------------
# The first fields of a line (proof_fast.bend: as B.Rec.fields has them),
# cut without copying the rest of the line
# ---------------------------------------------------------------------------

# A line cut at its first tab: the field before it, the text after it, and
# whether there was a tab.
type Cut is Data:
  Cut{f: String, r: String, ok: Bool}

def cut.k(+h: Char, c: Cut) -> Cut:
  match c:
    case Cut{f, r, ok}:
      Cut{SCon{h, f}, r, ok}

# The cut of SCon{h, t}; tab: h is a tab. (h is passed apart so the copy
# stops at the tab: a strict helper taking the recursive call would cut the
# whole line.)
def cut.go(t: String, tab: Bool, +h: Char) -> Cut:
  match t tab:
    case SNil{} True{}:
      Cut{SNil{}, SNil{}, True{}}
    case SCon{c, t2} True{}:
      Cut{SNil{}, SCon{c, t2}, True{}}
    case SNil{} False{}:
      Cut{SCon{h, SNil{}}, SNil{}, False{}}
    case SCon{+c, t2} False{}:
      cut.k(h, cut.go(t2, Char.is_eq(c, '\t'), c))

def cut(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{SNil{}, SNil{}, False{}}
    case SCon{+h, t}:
      cut.go(t, Char.is_eq(h, '\t'), h)

def Cut.f(c: Cut) -> String:
  match c:
    case Cut{f, r, ok}:
      f

# CHROM to FILTER cut off a line, and the text after FILTER's tab (Short:
# the line has fewer than 8 fields).
type C7 is Data:
  Got{f0: String, f1: String, f2: String, f3: String, f4: String, f5: String, f6: String, r: String}
  Short{}

def c7.g(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, c: Cut) -> C7:
  match c:
    case Cut{f6, r, True{}}:
      Got{f0, f1, f2, f3, f4, f5, f6, r}
    case Cut{f6, r, False{}}:
      Short{}

def c7.f(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, c: Cut) -> C7:
  match c:
    case Cut{f5, r, True{}}:
      c7.g(f0, f1, f2, f3, f4, f5, cut(r))
    case Cut{f5, r, False{}}:
      Short{}

def c7.e(+f0: String, +f1: String, +f2: String, +f3: String, c: Cut) -> C7:
  match c:
    case Cut{f4, r, True{}}:
      c7.f(f0, f1, f2, f3, f4, cut(r))
    case Cut{f4, r, False{}}:
      Short{}

def c7.d(+f0: String, +f1: String, +f2: String, c: Cut) -> C7:
  match c:
    case Cut{f3, r, True{}}:
      c7.e(f0, f1, f2, f3, cut(r))
    case Cut{f3, r, False{}}:
      Short{}

def c7.c(+f0: String, +f1: String, c: Cut) -> C7:
  match c:
    case Cut{f2, r, True{}}:
      c7.d(f0, f1, f2, cut(r))
    case Cut{f2, r, False{}}:
      Short{}

def c7.b(+f0: String, c: Cut) -> C7:
  match c:
    case Cut{f1, r, True{}}:
      c7.c(f0, f1, cut(r))
    case Cut{f1, r, False{}}:
      Short{}

def c7.a(c: Cut) -> C7:
  match c:
    case Cut{f0, r, True{}}:
      c7.b(f0, cut(r))
    case Cut{f0, r, False{}}:
      Short{}

def c7(body: String) -> C7:
  c7.a(cut(body))

# ---------------------------------------------------------------------------
# INFO's END entries, read in place (proof_fast.bend: noend says INFO, the
# text up to the next tab, has no entry with key END)
# ---------------------------------------------------------------------------

def ikeyT.ok3(semi: Bool, eq: Bool, tab: Bool) -> Bool:
  match semi eq tab:
    case False{} False{} False{}:
      True{}
    case _ _ _:
      False{}

def ikeyT.ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      ikeyT.ok3(Char.is_eq(h, ';'), Char.is_eq(h, '='), Char.is_eq(h, '\t'))

def ikeyT.go(s: String, ok: Bool) -> String:
  match s ok:
    case SCon{h, +t} True{}:
      SCon{h, ikeyT.go(t, ikeyT.ok(t))}
    case _ _:
      SNil{}

# The key of the INFO entry s starts (ikey, also stopping at a tab).
def ikeyT(+s: String) -> String:
  ikeyT.go(s, ikeyT.ok(s))

# h, then t; tab: h is a tab; start: h starts an entry.
def noend.go(t: String, +h: Char, tab: Bool, start: Bool) -> Bool:
  match t tab start:
    case _ True{} _:
      True{}
    case SNil{} False{} True{}:
      Bool.not(String.eq(ikeyT(SCon{h, SNil{}}), "END"))
    case SCon{+h2, +t2} False{} True{}:
      Bool.not(String.eq(ikeyT(SCon{h, SCon{h2, t2}}), "END")) && noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'))
    case SNil{} False{} False{}:
      True{}
    case SCon{+h2, t2} False{} False{}:
      noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'))

def noend(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      noend.go(t, h, Char.is_eq(h, '\t'), True{})

# INFO as the machine keeps it: "" when it has no END entry (the END check
# then reads the same), else a copy.
def info.if(ne: Bool, r: String) -> String:
  match ne:
    case True{}:
      ""
    case False{}:
      Cut.f(cut(r))

def pfs.g(g: C7, body: String) -> List<&2, String>:
  match g:
    case Got{f0, f1, f2, f3, f4, f5, f6, +r}:
      [f0, f1, f2, f3, f4, f5, f6, info.if(noend(r), r)]
    case Short{}:
      B.Rec.fields(body)

# The fields the machine keeps for a line: CHROM to FILTER, and INFO as
# info.if keeps it (all fields when the line has fewer than 8). Judging reads
# nothing else, except to rewrite a record (which splits the whole line).
def pfs(+body: String) -> List<&2, String>:
  pfs.g(c7(body), body)

# ---------------------------------------------------------------------------
# A record already in normal form (proof_fast.bend: judge_in gives it
# Normalized, unchanged, not stale), decided from its first 8 fields
# ---------------------------------------------------------------------------

# The record's POS, REF and ALT fields (f1, f3, f4) are written as
# Rec.rebuild writes them.
def same.text(+f1: String, +f3: String, +f4: String, +v: B.Var) -> Bool:
  match v:
    case B.Var{+p, +r, +a}:
      String.eq(Nat.show(p), f1) && String.eq(B.Allele.show(r), f3) && String.eq(String.join(B.Alleles.show(a), ","), f4)

# What judging a record gives, judged once: the record as it is
# (Same: Some{B.Res{B.Normalized{}, POS, body, False{}}}, written without
# rebuild), or judge_in's result (proof_fast.bend). fs: pfs(body); f1, f3,
# f4, f7: its POS, REF, ALT and INFO fields.
type Fast is Data:
  Same{}
  Other{m: Maybe<&2, B.Res>}

def fast.res(o: B.Outcome, +pos: Nat, body: String) -> Fast:
  Other{Some{B.Res{o, pos, body, False{}}}}

def fast.norm.k(ok: Bool, +v: B.Var, +w: B.Var, +body: String) -> Fast:
  match ok:
    case True{}:
      Same{}
    case False{}:
      +fs = B.Rec.fields(body)
      Other{Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)}}}

def fast.norm(m: Maybe<&2, B.Var>, +f1: String, +f3: String, +f4: String, +v: B.Var, +body: String) -> Fast:
  match m:
    case None{}:
      Other{None{}}
    case Some{+w}:
      fast.norm.k(B.Rec.same_var(v, w) && same.text(f1, f3, f4, v), v, w, body)

def fast.ref(ok: Maybe<&2, Bool>, +off: Nat, +bases: List<&2, B.Base>, +f1: String, +f3: String, +f4: String, +v: B.Var, +pos: Nat, +body: String) -> Fast:
  match ok:
    case None{}:
      Other{None{}}
    case Some{False{}}:
      fast.res(B.Problem{B.RefMismatch{}}, pos, body)
    case Some{True{}}:
      fast.norm(V.var_in(off, bases, v), f1, f3, f4, v, body)

def fast.problem(zero: Bool, distinct: Bool, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +f1: String, +f3: String, +f4: String, +v: B.Var, +pos: Nat, +body: String) -> Fast:
  match zero distinct v:
    case True{} _ _:
      fast.res(B.Problem{B.BadPos{}}, pos, body)
    case False{} False{} _:
      fast.res(B.Problem{B.AltDup{}}, pos, body)
    case False{} True{} B.Var{+p, +r, +a}:
      fast.ref(ref_check(clen, off, bases, Nat.sub(p, 1n), r), off, bases, f1, f3, f4, B.Var{p, r, a}, pos, body)

def fast.found(end_ok: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat, +f1: String, +f3: String, +f4: String, +body: String) -> Fast:
  match end_ok r a:
    case False{} _ _:
      fast.res(B.Problem{B.BadEnd{}}, pos, body)
    case True{} Some{+ref} Some{+alts}:
      fast.problem(Nat.is_eq(pos, 0n), B.Alleles.distinct(ref <> alts), clen, off, bases, f1, f3, f4, B.Var{pos, ref, alts}, pos, body)
    case True{} _ _:
      fast.res(B.Problem{B.NonAcgtn{}}, pos, body)

def fast.ans(a: Maybe<&2, Ans>, +pos: Nat, +f1: String, +f3: String, +f4: String, f7: String, alts: List<&2, String>, +body: String) -> Fast:
  match a:
    case None{}:
      Other{None{}}
    case Some{Unknown{}}:
      fast.res(B.NoContig{}, pos, body)
    case Some{Known{+clen, +off, raw}}:
      e = Nat.sub(Nat.add(pos, String.length(f3)), 1n)
      fast.found(end_ok(f7, e), B.Allele.read(f3), B.Alleles.read(alts), clen, off, B.Bases.of_fasta(raw), pos, f1, f3, f4, body)

def fast.go(bad: Bool, skip: Bool, a: Maybe<&2, Ans>, +fs: List<&2, String>, +body: String) -> Fast:
  match bad skip:
    case True{} _:
      fast.res(B.Broken{}, B.Rec.pos(fs), body)
    case False{} True{}:
      fast.res(B.Skipped{}, B.Rec.pos(fs), body)
    case False{} False{}:
      fast.ans(a, B.Rec.pos(fs), B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Rec.field(fs, 7n), B.Rec.alts(fs), body)

def fast(a: Maybe<&2, Ans>, +fs: List<&2, String>, +body: String) -> Fast:
  fast.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), a, fs, body)
