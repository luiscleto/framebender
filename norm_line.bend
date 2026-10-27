import Base
import ./types.bend as B
import ./norm_var.bend as V

# framebender: the result for one body line, reading the reference through a
# window (code, not spec). Reached from the laws through Norm.judge_in
# (norm.bend).

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
      found(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, bases, fs, body)

def judge_in.go(bad: Bool, skip: Bool, a: B.Ans, +fs: List<&2, String>, +body: String) -> Maybe<&2, B.Res>:
  match bad skip:
    case True{} _:
      Some{mk(B.Broken{}, fs, body)}
    case False{} True{}:
      Some{mk(B.Skipped{}, fs, body)}
    case False{} False{}:
      judge_in.ans(a, fs, body)

# The result for one body line (its text without terminator), given what the
# reference answered for the line's CHROM; None when the answer is not enough
# (the machine then asks for more).
def judge_in(a: B.Ans, +body: String) -> Maybe<&2, B.Res>:
  +fs = B.Rec.fields(body)
  judge_in.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), a, fs, body)
