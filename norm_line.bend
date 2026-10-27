import Base
import ./types.bend as B
import ./norm_var.bend as V

# framebender: the result for one body line, reading the reference through a
# window (code, not spec). Reached from the laws through Norm.judge_in
# (norm.bend).

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

def judge_in.ans(a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match a:
    case B.NoAns{}:
      None{}
    case B.Unknown{}:
      Some{mk(B.NoContig{}, fs, body)}
    case B.Known{+clen, +off, raw}:
      +bases = B.Bases.of_fasta(raw)
      +ref = B.Rec.field(fs, 3n)
      e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      found(end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, bases, fs, body)

def judge_in.go(bad: Bool, skip: Bool, a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match bad skip:
    case True{} _:
      Some{mk(B.Broken{}, fs, body)}
    case False{} True{}:
      Some{mk(B.Skipped{}, fs, body)}
    case False{} False{}:
      judge_in.ans(a, fs, body)

# judge_in with the line's fields already split (fs = B.Rec.fields(body)).
def judge_fs(a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  judge_in.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), a, fs, body)

# The result for one body line (its text without terminator), given what the
# reference answered for the line's CHROM; None when the answer is not enough
# (the machine then asks for more).
def judge_in(a: B.Ans, +body: String) -> Maybe<&2, B.Res>:
  judge_fs(a, B.Rec.fields(body), body)
