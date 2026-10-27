import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./proof_window_defs.bend as WD
import ./norm.bend as Norm
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN

# Lemmas for the machine proof: the driver's reference answers (M.truth) are
# truthful, and an answer from the contig's first letter to the end of REF is
# enough (WD.enough) for every line.

# Strings equal themselves
# ========================

law word_cmp_refl:
  for +n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}

def word_cmp_refl(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_cmp_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_cmp_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

law order_refl:
  for +s: String
  {String.order.go(s, s, EQ{}) == EQ{} : Cmp}

def order_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{w}}, t}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      order_refl(t)

law str_eq_refl:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

def str_eq_refl(s):
  %Equal.sym(Cmp, String.order.go(s, s, EQ{}), EQ{}, order_refl(s)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# Taking and dropping letters
# ===========================

law drop_min:
  for +r: String
  for +f: Nat
  {String.drop(r, Nat.min(f, String.length(r))) == String.drop(r, f) : String}

def drop_min(r, f):
  match r f:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      drop_min(t, p)

law take_len_take:
  for +x: String
  for +k: Nat
  {String.take(x, String.length(String.take(x, k))) == String.take(x, k) : String}

def take_len_take(x, k):
  match x k:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %take_len_take(t, p) : {SCon{h, String.take(t, String.length(String.take(t, p)))} == SCon{h, _} : String}
      {==}

law take_len:
  for +x: String
  for +k: Nat
  {String.length(String.take(x, k)) == Nat.min(k, String.length(x)) : Nat}

def take_len(x, k):
  match x k:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %take_len(t, p) : {1n+String.length(String.take(t, p)) == 1n+_ : Nat}
      {==}

law drop_zero:
  for +r: String
  {String.drop(r, 0n) == r : String}

def drop_zero(r):
  match r:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

law sub_le_zero:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.sub(a, b) == 0n : Nat}

def sub_le_zero(a, b, e):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, P.false_ne_true(e))
    case 1n+p 1n+q:
      sub_le_zero(p, q, e)

# The driver's answers are truthful
# =================================

law truthful_of:
  for +fa: List<&2, B.Contig>
  for +chrom: String
  for +f: Nat
  for +u: Nat
  for +m: Maybe<&2, String>
  for +hm: {B.Fasta.find(fa, chrom) == m : Maybe<&2, String>}
  {WD.truthful(fa, chrom, Some{M.truth.of(m, f, u)}) == True{} : Bool}

def truthful_of(fa, chrom, f, u, m, hm):
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, chrom), None{}, hm) : {Maybe.is_none(&2, String, _) == True{} : Bool}
      {==}
    case Some{r}:
      +n = String.length(r)
      +raw = String.take(String.drop(r, f), Nat.sub(u, f))
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, chrom), Some{r}, hm) :
        {WD.known.ok(_, n, Nat.min(f, n), raw) == True{} : Bool}
      %Equal.sym(String, String.drop(r, Nat.min(f, n)), String.drop(r, f), drop_min(r, f)) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, String.take(_, String.length(raw)))) == True{} : Bool}
      %Equal.sym(String, String.take(String.drop(r, f), String.length(raw)), raw, take_len_take(String.drop(r, f), Nat.sub(u, f))) : {Bool.and(Nat.is_eq(n, n), String.eq(raw, _)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, P.eq_refl(n)) : {Bool.and(_, String.eq(raw, raw)) == True{} : Bool}
      str_eq_refl(raw)

law truthful_truth:
  for +fa: List<&2, B.Contig>
  for +chrom: String
  for +f: Nat
  for +u: Nat
  {WD.truthful(fa, chrom, Some{M.truth(fa, chrom, f, u)}) == True{} : Bool}

def truthful_truth(fa, chrom, f, u):
  truthful_of(fa, chrom, f, u, B.Fasta.find(fa, chrom), {==})

# Enough: an answer from the contig's first letter
# ================================================

# What an answer must hold for a line of contig m that reads up to hi: that
# the contig is unknown, or its letters from the first up to hi.
def ans_ok(m: Maybe<&2, String>, a: Maybe<&2, Pr.Ans>, +hi: Nat) -> Bool:
  match m:
    case None{}:
      WD.is_unknown(a)
    case Some{r}:
      WD.covers(a, 0n, hi)

def rlen(+fs: List<&2, String>) -> Nat:
  String.length(B.Rec.field(fs, 3n))

def hi(+fs: List<&2, String>) -> Nat:
  Nat.add(Nat.sub(B.Rec.pos(fs), 1n), rlen(fs))

law covers_lo:
  for +a: Maybe<&2, Pr.Ans>
  for +lo: Nat
  for +h: Nat
  for +e: {WD.covers(a, 0n, h) == True{} : Bool}
  {WD.covers(a, lo, h) == True{} : Bool}

def covers_lo(a, lo, h, e):
  match a:
    case None{}:
      Empty.absurd({WD.covers(None{}, lo, h) == True{} : Bool}, P.false_ne_true(e))
    case Some{Pr.Unknown{}}:
      Empty.absurd({WD.covers(Some{Pr.Unknown{}}, lo, h) == True{} : Bool}, P.false_ne_true(e))
    case Some{Pr.Known{clen, off, raw}}:
      match off:
        case 0n:
          +rest = Nat.is_le(Nat.min(h, clen), String.length(raw))
          PN.and_intro(Nat.is_le(0n, lo), rest, P.le_zero_l(lo), P.and_true_r(True{}, rest, e))
        case 1n+p:
          Empty.absurd({WD.covers(Some{Pr.Known{clen, 1n+p, raw}}, lo, h) == True{} : Bool}, P.false_ne_true(e))

law known_of_covers:
  for +a: Maybe<&2, Pr.Ans>
  for +h: Nat
  for +e: {WD.covers(a, 0n, h) == True{} : Bool}
  {WD.is_known(a) == True{} : Bool}

def known_of_covers(a, h, e):
  match a:
    case None{}:
      Empty.absurd({WD.is_known(None{}) == True{} : Bool}, P.false_ne_true(e))
    case Some{Pr.Unknown{}}:
      Empty.absurd({WD.is_known(Some{Pr.Unknown{}}) == True{} : Bool}, P.false_ne_true(e))
    case Some{Pr.Known{clen, off, raw}}:
      {==}

law E_code:
  for +k: B.Code
  for +fs: List<&2, String>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +hc: {WD.covers(a, 0n, hi(fs)) == True{} : Bool}
  {WD.enough.go(L.res(B.Problem{k}, fs, body), B.Rec.pos(fs), rlen(fs), a) == True{} : Bool}

def E_code(k, fs, body, a, hc):
  match k:
    case B.Malformed{}:
      known_of_covers(a, hi(fs), hc)
    case B.UnknownChrom{}:
      known_of_covers(a, hi(fs), hc)
    case B.BadEnd{}:
      known_of_covers(a, hi(fs), hc)
    case B.NonAcgtn{}:
      known_of_covers(a, hi(fs), hc)
    case B.BadPos{}:
      known_of_covers(a, hi(fs), hc)
    case B.AltDup{}:
      known_of_covers(a, hi(fs), hc)
    case B.RefMismatch{}:
      covers_lo(a, Nat.sub(B.Rec.pos(fs), 1n), hi(fs), hc)
    case B.Unsorted{}:
      known_of_covers(a, hi(fs), hc)
    case B.NoHeader{}:
      known_of_covers(a, hi(fs), hc)
    case B.Stale{}:
      known_of_covers(a, hi(fs), hc)

law E_problem:
  for +c: Maybe<&2, B.Code>
  for +fs: List<&2, String>
  for +body: String
  for +seq: List<&2, B.Base>
  for +v: B.Var
  for +a: Maybe<&2, Pr.Ans>
  for +hc: {WD.covers(a, 0n, hi(fs)) == True{} : Bool}
  {WD.enough.go(L.problem(c, fs, body, seq, v), B.Rec.pos(fs), rlen(fs), a) == True{} : Bool}

def E_problem(c, fs, body, seq, v, a, hc):
  match c:
    case Some{k}:
      E_code(k, fs, body, a, hc)
    case None{}:
      covers_lo(a, Nat.min(Nat.sub(B.Rec.pos(fs), 1n), Nat.sub(L.pos_of(Norm.var(seq, v)), 2n)), hi(fs), hc)

law E_bases:
  for +eo: Bool
  for +r: Maybe<&2, List<&2, B.Base>>
  for +al: Maybe<&2, List<&2, List<&2, B.Base>>>
  for +fs: List<&2, String>
  for +body: String
  for +seq: List<&2, B.Base>
  for +a: Maybe<&2, Pr.Ans>
  for +hc: {WD.covers(a, 0n, hi(fs)) == True{} : Bool}
  {WD.enough.go(L.judge.bases(eo, r, al, fs, body, seq), B.Rec.pos(fs), rlen(fs), a) == True{} : Bool}

def E_bases(eo, r, al, fs, body, seq, a, hc):
  match eo r al:
    case _ Some{ref} Some{alts}:
      +v = {B.Var{B.Rec.pos(fs), ref, alts} : B.Var}
      E_problem(L.checks(eo, seq, v), fs, body, seq, v, a, hc)
    case True{} None{} _:
      E_code(B.NonAcgtn{}, fs, body, a, hc)
    case False{} None{} _:
      E_code(B.BadEnd{}, fs, body, a, hc)
    case True{} Some{ref} None{}:
      E_code(B.NonAcgtn{}, fs, body, a, hc)
    case False{} Some{ref} None{}:
      E_code(B.BadEnd{}, fs, body, a, hc)

law E_contig:
  for +m: Maybe<&2, String>
  for +fs: List<&2, String>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +h: {ans_ok(m, a, hi(fs)) == True{} : Bool}
  {WD.enough.go(L.judge.contig(m, fs, body), B.Rec.pos(fs), rlen(fs), a) == True{} : Bool}

def E_contig(m, fs, body, a, h):
  match m:
    case None{}:
      h
    case Some{raw}:
      +ref = B.Rec.field(fs, 3n)
      E_bases(B.Info.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)),
        B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, body, B.Bases.of_fasta(raw), a, h)

law E_shape:
  for +bad: Bool
  for +skip: Bool
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +h: {ans_ok(B.Fasta.find(fa, WD.chrom_of(body)), a, hi(B.Rec.fields(body))) == True{} : Bool}
  {WD.enough.go(L.judge.shape(bad, skip, fa, B.Rec.fields(body), body), B.Rec.pos(B.Rec.fields(body)), rlen(B.Rec.fields(body)), a) == True{} : Bool}

def E_shape(bad, skip, fa, body, a, h):
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      E_contig(B.Fasta.find(fa, WD.chrom_of(body)), B.Rec.fields(body), body, a, h)

# An answer that is ans_ok is enough.
law E_main:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +h: {ans_ok(B.Fasta.find(fa, WD.chrom_of(body)), a, hi(B.Rec.fields(body))) == True{} : Bool}
  {WD.enough(fa, body, a) == True{} : Bool}

def E_main(fa, body, a, h):
  +fs = B.Rec.fields(body)
  E_shape(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, body, a, h)

# The driver's answer from the contig's first letter up to hi is ans_ok.
law ok_zero:
  for +m: Maybe<&2, String>
  for +u: Nat
  {ans_ok(m, Some{M.truth.of(m, 0n, u)}, u) == True{} : Bool}

def ok_zero(m, u):
  match m:
    case None{}:
      {==}
    case Some{r}:
      +n = String.length(r)
      %Equal.sym(Nat, Nat.sub(u, 0n), u, P.sub_zero(u)) : {WD.covers(Some{Pr.Known{n, 0n, String.take(String.drop(r, 0n), _)}}, 0n, u) == True{} : Bool}
      %Equal.sym(String, String.drop(r, 0n), r, drop_zero(r)) : {WD.covers(Some{Pr.Known{n, 0n, String.take(_, u)}}, 0n, u) == True{} : Bool}
      %Equal.sym(Nat, String.length(String.take(r, u)), Nat.min(u, n), take_len(r, u)) : {Bool.and(Nat.is_le(0n, 0n), Nat.is_le(Nat.min(u, n), _)) == True{} : Bool}
      P.le_refl(Nat.min(u, n))

# The answer for a contig the reference lacks is enough, whatever the window.
law ok_none:
  for +f: Nat
  for +u: Nat
  {ans_ok(None{}, Some{M.truth.of(None{}, f, u)}, u) == True{} : Bool}

def ok_none(f, u):
  {==}
