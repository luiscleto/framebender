import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_cache.bend as K
import ./proof_b_cache_lem.bend as X
import ./proof_window_defs.bend as WS
import ./proof_window_lists.bend as WL
import ./proof_window.bend as PW
import ./proof_fast.bend as PF
import ./proof_b_adv_wf.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY

# pb-cut's budget lemmas on windows (notes/bytes_proofs_budget.md, "Suggested
# for pb-cache"): Z1 fast_none_fits, Z2 zero_decides, Z3 held_serves. The
# statements are pb-cut's, unchanged; proof_b_budget_step.bend calls them.

# ---------------------------------------------------------------------------
# Z3 held_serves: a window that holds a read serves it
# ---------------------------------------------------------------------------

def sv_slice(+c: String, cb: D.Bytes, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, +offu: U32, +rlen: U32, +clenu: U32, +a2: Nat, r: D.Bytes & List<&2, U32>) ->
  {BD.sv_hit(Norm.serve.slice(c, cb, a0, b0, clen, off, offu, rlen, clenu, a2, r)) == True{} : Bool}:
  match r:
    case (raw, xs):
      {==}

def held_serves(w: Norm.Win, +c: String, +a: Nat, +b: Nat,
  +h: {BN.holdsW(w, c, a, b) == True{} : Bool}) ->
  {BD.sv_hit(Norm.serve(w, c, a, b)) == True{} : Bool}:
  match w:
    case Norm.WNone{}:
      Empty.absurd({BD.sv_hit(Norm.serve(Norm.WNone{}, c, a, b)) == True{} : Bool}, N.false_ne_true(h))
    case Norm.WUnk{+c0}:
      %Equal.sym(Bool, String.eq(c0, c), True{}, h) : {BD.sv_hit(Norm.serve.unk(_, c0)) == True{} : Bool}
      {==}
    case Norm.WKnown{+c0, cb, +a0, +b0, +clen, +off, raw, +offu, +rlen, +clenu}:
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))), True{}, h) :
        {BD.sv_hit(Norm.serve.known(_, Norm.WKnown{c0, cb, a0, b0, clen, off, raw, offu, rlen, clenu}, a, b)) == True{} : Bool}
      sv_slice(c0, cb, a0, b0, clen, off, offu, rlen, clenu, Nat.min(a, clen),
        BY.to_list(raw, U32.from_nat(Nat.sub(Nat.min(a, clen), off)), U32.from_nat(Nat.sub(Nat.min(b, clen), Nat.min(a, clen)))))
    case Norm.WStr{+c0, +a0, +b0, +clen, +off, +raw}:
      %Equal.sym(Bool, Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))), True{}, h) :
        {BD.sv_hit(Norm.serve.str(_, c0, a0, b0, clen, off, raw, a, b)) == True{} : Bool}
      {==}

# ---------------------------------------------------------------------------
# Z1 fast_none_fits: "the window is too small" only once REF fits its contig
# ---------------------------------------------------------------------------

def isON(+f: J.Fast) -> Bool:
  match f:
    case J.Same{}:
      False{}
    case J.Other{None{}}:
      True{}
    case J.Other{Some{r}}:
      False{}

def nope(+F: J.Fast, +hx: {isON(F) == False{} : Bool}, +h: {F == J.Other{None{}} : J.Fast}) -> Empty:
  N.false_ne_true(Equal.trans(Bool, False{}, isON(F), True{}, Equal.sym(Bool, isON(F), False{}, hx),
    Equal.cong(J.Fast, Bool, z => isON(z), F, J.Other{None{}}, h)))

# ref_check says "not held" or "matches" only when REF fits.
def rc(+fits: Bool, +cov: Bool, +q: Bool, +off: Nat, +bases: List<&2, B.Base>, +f1: String, +f3: String, +f4: String, +v: B.Var, +pos: Nat, +body: String,
  +h: {J.fast.ref(J.ref_check.go(fits, cov, q), off, bases, f1, f3, f4, v, pos, body) == J.Other{None{}} : J.Fast}) ->
  {fits == True{} : Bool}:
  match fits:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, nope(J.fast.ref(J.ref_check.go(False{}, cov, q), off, bases, f1, f3, f4, v, pos, body), {==}, h))

def fz_prob(+zero: Bool, +dist: Bool, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +f1: String, +f3: String, +f4: String,
  +p: Nat, +r: List<&2, B.Base>, +a: List<&2, List<&2, B.Base>>, +pos: Nat, +body: String,
  +h: {J.fast.problem(zero, dist, clen, off, bases, f1, f3, f4, B.Var{p, r, a}, pos, body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(Nat.add(Nat.sub(p, 1n), List.length(&2, B.Base, r)), clen) == True{} : Bool}:
  match zero dist:
    case True{} _:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(p, 1n), List.length(&2, B.Base, r)), clen) == True{} : Bool}, nope(J.fast.problem(True{}, dist, clen, off, bases, f1, f3, f4, B.Var{p, r, a}, pos, body), {==}, h))
    case False{} False{}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(p, 1n), List.length(&2, B.Base, r)), clen) == True{} : Bool}, nope(J.fast.problem(False{}, False{}, clen, off, bases, f1, f3, f4, B.Var{p, r, a}, pos, body), {==}, h))
    case False{} True{}:
      +n = List.length(&2, B.Base, r)
      +st = Nat.sub(p, 1n)
      rc(Nat.is_le(Nat.add(st, n), clen), Bool.and(Nat.is_le(off, st), Nat.is_le(Nat.add(st, n), Nat.add(off, List.length(&2, B.Base, bases)))),
        B.Bases.eq(List.take(&2, B.Base, List.drop(&2, B.Base, bases, Nat.sub(st, off)), n), r), off, bases, f1, f3, f4, B.Var{p, r, a}, pos, body, h)

def fz_found(+eo: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +pos: Nat,
  +f1: String, +f3: String, +f4: String, +body: String,
  +hr: {B.Allele.read(f3) == rr : Maybe<&2, List<&2, B.Base>>},
  +h: {J.fast.found(eo, rr, aa, clen, off, bases, pos, f1, f3, f4, body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(Nat.add(Nat.sub(pos, 1n), String.length(f3)), clen) == True{} : Bool}:
  match eo rr aa:
    case False{} _ _:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(pos, 1n), String.length(f3)), clen) == True{} : Bool}, nope(J.fast.found(False{}, rr, aa, clen, off, bases, pos, f1, f3, f4, body), {==}, h))
    case True{} Some{+ref} Some{+alts}:
      +k = fz_prob(Nat.is_eq(pos, 0n), B.Alleles.distinct(ref <> alts), clen, off, bases, f1, f3, f4, pos, ref, alts, pos, body, h)
      %WL.read_len(f3, ref, hr) : {Nat.is_le(Nat.add(Nat.sub(pos, 1n), _), clen) == True{} : Bool}
      k
    case True{} Some{+ref} None{}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(pos, 1n), String.length(f3)), clen) == True{} : Bool}, nope(J.fast.found(True{}, Some{ref}, None{}, clen, off, bases, pos, f1, f3, f4, body), {==}, h))
    case True{} None{} _:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(pos, 1n), String.length(f3)), clen) == True{} : Bool}, nope(J.fast.found(True{}, None{}, aa, clen, off, bases, pos, f1, f3, f4, body), {==}, h))

def fz_go(+bad: Bool, +skip: Bool, +clen: Nat, +off: Nat, +raw: String, +fs: List<&2, String>, +body: String,
  +h: {J.fast.go(bad, skip, Some{J.Known{clen, off, raw}}, fs, body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen) == True{} : Bool}:
  match bad skip:
    case True{} _:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen) == True{} : Bool},
        nope(J.fast.go(True{}, skip, Some{J.Known{clen, off, raw}}, fs, body), {==}, h))
    case False{} True{}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen) == True{} : Bool},
        nope(J.fast.go(False{}, True{}, Some{J.Known{clen, off, raw}}, fs, body), {==}, h))
    case False{} False{}:
      +pos = B.Rec.pos(fs)
      +f3 = B.Rec.field(fs, 3n)
      fz_found(J.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(pos, String.length(f3)), 1n)), B.Allele.read(f3), B.Alleles.read(B.Rec.alts(fs)), clen, off, B.Bases.of_fasta(raw), pos,
        B.Rec.field(fs, 1n), f3, B.Rec.field(fs, 4n), body, {==}, h)

def fast_none_fits(+clen: Nat, +off: Nat, +raw: String, +fs: List<&2, String>, +body: String,
  +h: {J.fast(Some{J.Known{clen, off, raw}}, fs, body) == J.Other{None{}} : J.Fast}) ->
  {Nat.is_le(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen) == True{} : Bool}:
  fz_go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), clen, off, raw, fs, body, h)

# ---------------------------------------------------------------------------
# Z2 zero_decides: with the line's zero window held and back >= POS, the
# verdict does not ask. The first try starts at 0 (TA = 0) and is served; the
# truthful answer from 0 is enough (window_enough), so J.fast decides.
# ---------------------------------------------------------------------------

def subz(+m: Nat, +n: Nat, +h: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.sub(m, n) == 0n : Nat}:
  match m n:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, N.false_ne_true(h))
    case 1n+p 1n+q:
      subz(p, q, h)

# The window a known picture makes holds what its picture holds.
def hwk(+c0: String, +a0: Nat, +b0: Nat, +clen: Nat, +off: Nat, r: D.Bytes & U32, +c: String, +a: Nat, +b: Nat) ->
  {BN.holdsW(Norm.win_of.k(c0, a0, b0, clen, off, r), c, a, b) == Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, clen), Nat.min(b0, clen))) : Bool}:
  match r:
    case (raw, rl):
      {==}

def hh.k(+m: Maybe<&2, String>, +c0: String, +a0: Nat, +b0: Nat, +str: Bool, +c: String, +a: Nat, +b: Nat,
  +h: {BN.holdsW(PC.mkWin.k(m, c0, a0, b0, str), c, a, b) == True{} : Bool}) ->
  {Bool.and(Maybe.is_some(&2, String, m), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, PC.wp.clen.k(m)), Nat.min(b0, PC.wp.clen.k(m))))) == True{} : Bool}:
  match m str:
    case None{} _:
      Empty.absurd({Bool.and(Maybe.is_some(&2, String, None{}), Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, PC.wp.clen.k(None{})), Nat.min(b0, PC.wp.clen.k(None{}))))) == True{} : Bool},
        N.false_ne_true(h))
    case Some{+r} False{}:
      +X0 = Bool.and(Bool.and(String.eq(c0, c), Nat.is_le(a0, a)), Nat.is_le(Nat.min(b, String.length(r)), Nat.min(b0, String.length(r))))
      +HW = BN.holdsW(Norm.win_of.k(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0)))), c, a, b)
      Equal.trans(Bool, X0, HW, True{}, Equal.sym(Bool, HW, X0, hwk(c0, a0, b0, String.length(r), Nat.min(a0, String.length(r)), BY.len(E.enc(PC.letters(r, a0, b0))), c, a, b)), h)
    case Some{+r} True{}:
      h

def hold_of(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: String, +a: Nat, +b: Nat,
  +hz: {BN.holdsW(PC.mkWin(fa, wp), c, a, b) == True{} : Bool}) ->
  {PC.holds(fa, wp, c, a, b) == True{} : Bool}:
  match wp:
    case PC.WPNone{}:
      Empty.absurd({PC.holds(fa, PC.WPNone{}, c, a, b) == True{} : Bool}, N.false_ne_true(hz))
    case PC.WPUnk{+c0}:
      hz
    case PC.WPKnown{+c0, +a0, +b0}:
      hh.k(B.Fasta.find(fa, c0), c0, a0, b0, False{}, c, a, b, hz)
    case PC.WPStr{+c0, +a0, +b0}:
      hh.k(B.Fasta.find(fa, c0), c0, a0, b0, True{}, c, a, b, hz)

# An answer from 0 holding up to the end of REF is enough for any outcome but
# NoContig.
def isNC.o(+oc: B.Outcome) -> Bool:
  match oc:
    case B.NoContig{}:
      True{}
    case B.Broken{}:
      False{}
    case B.Skipped{}:
      False{}
    case B.Problem{c}:
      False{}
    case B.Normalized{}:
      False{}

def isNC(+r: B.Res) -> Bool:
  match r:
    case B.Res{+oc, k, t, s}:
      isNC.o(oc)

def cov_c(+c: B.Code, +p: Nat, +rl: Nat, +clen: Nat, +raw: String, +k: Nat, +t: String, +s: Bool,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rl), clen), String.length(raw)) == True{} : Bool}) ->
  {WS.enough.go(B.Res{B.Problem{c}, k, t, s}, p, rl, Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match c:
    case B.RefMismatch{}:
      W.and_tt(Nat.is_le(0n, Nat.sub(p, 1n)), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rl), clen), String.length(raw)), N.le_zero_l(Nat.sub(p, 1n)), hcov)
    case B.Malformed{}:
      {==}
    case B.UnknownChrom{}:
      {==}
    case B.BadEnd{}:
      {==}
    case B.NonAcgtn{}:
      {==}
    case B.BadPos{}:
      {==}
    case B.AltDup{}:
      {==}
    case B.Unsorted{}:
      {==}
    case B.NoHeader{}:
      {==}
    case B.Stale{}:
      {==}
    case B.UndefinedTag{tag}:
      {==}
    case B.BadCount{}:
      {==}
    case B.BadGt{}:
      {==}
    case B.DupAlts{}:
      {==}
    case B.BadCr{}:
      {==}

def cov_o(+oc: B.Outcome, +k: Nat, +t: String, +s: Bool, +p: Nat, +rl: Nat, +clen: Nat, +raw: String,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rl), clen), String.length(raw)) == True{} : Bool},
  +hnc: {isNC.o(oc) == False{} : Bool}) ->
  {WS.enough.go(B.Res{oc, k, t, s}, p, rl, Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match oc:
    case B.Broken{}:
      {==}
    case B.Skipped{}:
      {==}
    case B.NoContig{}:
      Empty.absurd({WS.enough.go(B.Res{B.NoContig{}, k, t, s}, p, rl, Some{J.Known{clen, 0n, raw}}) == True{} : Bool}, N.false_ne_true(Equal.sym(Bool, True{}, False{}, hnc)))
    case B.Problem{+c}:
      cov_c(c, p, rl, clen, raw, k, t, s, hcov)
    case B.Normalized{}:
      W.and_tt(Nat.is_le(0n, Nat.min(Nat.sub(p, 1n), Nat.sub(k, 2n))), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rl), clen), String.length(raw)),
        N.le_zero_l(Nat.min(Nat.sub(p, 1n), Nat.sub(k, 2n))), hcov)

def cov_r(+r: B.Res, +p: Nat, +rl: Nat, +clen: Nat, +raw: String,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rl), clen), String.length(raw)) == True{} : Bool},
  +hnc: {isNC(r) == False{} : Bool}) ->
  {WS.enough.go(r, p, rl, Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match r:
    case B.Res{+oc, +k, +t, +s}:
      cov_o(oc, k, t, s, p, rl, clen, raw, hcov, hnc)

def ep(+c: Maybe<&2, B.Code>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var, +clen: Nat, +raw: String,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen), String.length(raw)) == True{} : Bool}) ->
  {WS.enough.go(L.problem(c, fs, body, seq, v), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match c:
    case Some{+k}:
      cov_r(L.problem(Some{k}, fs, body, seq, v), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), clen, raw, hcov, {==})
    case None{}:
      cov_r(L.problem(None{}, fs, body, seq, v), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), clen, raw, hcov, {==})

def eb(+eo: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +raw: String,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen), String.length(raw)) == True{} : Bool}) ->
  {WS.enough.go(L.judge.bases(eo, rr, aa, fs, body, seq), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match rr aa:
    case Some{+ref} Some{+alts}:
      ep(L.checks(eo, seq, B.Var{B.Rec.pos(fs), ref, alts}), fs, body, seq, B.Var{B.Rec.pos(fs), ref, alts}, clen, raw, hcov)
    case Some{+ref} None{}:
      cov_r(L.judge.bases(eo, Some{ref}, None{}, fs, body, seq), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), clen, raw, hcov, {==})
    case None{} _:
      cov_r(L.judge.bases(eo, None{}, aa, fs, body, seq), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), clen, raw, hcov, {==})

def es(+bad: Bool, +skip: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String, +r0: String,
  +hf: {B.Fasta.find(fa, B.Rec.field(fs, 0n)) == Some{r0} : Maybe<&2, String>},
  +clen: Nat, +raw: String,
  +hcov: {Nat.is_le(Nat.min(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen), String.length(raw)) == True{} : Bool}) ->
  {WS.enough.go(L.judge.shape(bad, skip, fa, fs, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{J.Known{clen, 0n, raw}}) == True{} : Bool}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, B.Rec.field(fs, 0n)), Some{r0}, hf) :
        {WS.enough.go(L.judge.contig(_, fs, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{J.Known{clen, 0n, raw}}) == True{} : Bool}
      eb(B.Info.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n))), 1n)), B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)),
        fs, body, B.Bases.of_fasta(r0), clen, raw, hcov)

# The letters from 0 up to hi: min(hi, clen) of them.
def hcov_l(+r: String, +hi: Nat) -> {Nat.is_le(Nat.min(hi, String.length(r)), String.length(PC.letters(r, 0n, hi))) == True{} : Bool}:
  +M = Nat.min(hi, String.length(r))
  %Equal.sym(Nat, String.length(PC.letters(r, 0n, hi)), Nat.sub(M, Nat.min(0n, String.length(r))), K.len_letters(r, 0n, hi)) : {Nat.is_le(M, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(M, 0n), M, N.sub_zero(M)) : {Nat.is_le(M, _) == True{} : Bool}
  N.le_refl(M)

def unk_on(+bad: Bool, +skip: Bool, +fs: List<&2, String>, +body: String) -> {isON(J.fast.go(bad, skip, Some{J.Unknown{}}, fs, body)) == False{} : Bool}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def on_of(+F: J.Fast, +p: Nat, +body: String, +x: Maybe<&2, B.Res>,
  +hfr: {PF.fr_res(F, p, body) == x : Maybe<&2, B.Res>},
  +hs: {Maybe.is_some(&2, B.Res, x) == True{} : Bool}) ->
  {isON(F) == False{} : Bool}:
  match F:
    case J.Same{}:
      {==}
    case J.Other{None{}}:
      Empty.absurd({isON(J.Other{None{}}) == False{} : Bool},
        N.false_ne_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, B.Res, x), True{}, Equal.cong(Maybe<&2, B.Res>, Bool, z => Maybe.is_some(&2, B.Res, z), None{}, x, hfr), hs)))
    case J.Other{Some{r}}:
      {==}

# J.fast with the truthful answer from 0 up to the end of REF decides.
def zm(+m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +body: String,
  +hf: {B.Fasta.find(fa, B.Rec.field(B.Rec.fields(body), 0n)) == m : Maybe<&2, String>}) ->
  {isON(J.fast(Some{PC.jtruth.k(m, 0n, Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(B.Rec.field(B.Rec.fields(body), 3n))))}, J.pfs(body), body)) == False{} : Bool}:
  match m:
    case None{}:
      unk_on(B.Rec.malformed(J.pfs(body)), B.Rec.out_of_scope(J.pfs(body)), J.pfs(body), body)
    case Some{+r0}:
      +fs = B.Rec.fields(body)
      +C0 = B.Rec.field(fs, 0n)
      +E1 = Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n)))
      +jt = {J.Known{String.length(r0), 0n, PC.letters(r0, 0n, E1)} : J.Ans}
      +ht = AB.subst(Maybe<&2, String>, z => {WS.truthful(fa, C0, Some{PC.jtruth.k(z, 0n, E1)}) == True{} : Bool}, B.Fasta.find(fa, C0), Some{r0}, hf, K.jtruth_ok(fa, C0, 0n, E1))
      +he = es(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, fs, body, r0, hf, String.length(r0), PC.letters(r0, 0n, E1), hcov_l(r0, E1))
      on_of(J.fast(Some{jt}, J.pfs(body), body), B.Rec.pos(fs), body, J.judge_in(Some{jt}, body), PF.fast_judge(Some{jt}, body), PW.window_enough(fa, body, Some{jt}, ht, he))

def zd.f(+F: J.Fast, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +body: String, +hF: {isON(F) == False{} : Bool}) ->
  {BD.is_vwant(MSX.mkVd(fa, wp, MSX.vxP(body, MSX.sgP(63n, fa, wp, body, MSX.fP(back, PC.wp.clen(fa, MSX.TC(body)), B.Rec.pos(J.pfs(body)), F))))) == False{} : Bool}:
  match F:
    case J.Same{}:
      {==}
    case J.Other{None{}}:
      Empty.absurd({BD.is_vwant(MSX.mkVd(fa, wp, MSX.vxP(body, MSX.sgP(63n, fa, wp, body, MSX.fP(back, PC.wp.clen(fa, MSX.TC(body)), B.Rec.pos(J.pfs(body)), J.Other{None{}}))))) == False{} : Bool},
        N.false_ne_true(Equal.sym(Bool, True{}, False{}, hF)))
    case J.Other{Some{r}}:
      {==}

def zd.t(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +body: String,
  +hh: {PC.holds(fa, wp, MSX.TC(body), MSX.TA(back, body), MSX.TE(body)) == True{} : Bool},
  +hF: {isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(back, body), MSX.TE(body))}, J.pfs(body), body)) == False{} : Bool}) ->
  {BD.is_vwant(MSX.mkVd(fa, wp, MSX.vxP(body, MSX.sgP(64n, fa, wp, body, MSX.XA{back})))) == False{} : Bool}:
  %Equal.sym(Bool, PC.holds(fa, wp, MSX.TC(body), MSX.TA(back, body), MSX.TE(body)), True{}, hh) :
    {BD.is_vwant(MSX.mkVd(fa, wp, MSX.vxP(body, MSX.sgP(63n, fa, wp, body, Bool.pick(MSX.SxP, _,
      MSX.fP(back, PC.wp.clen(fa, MSX.TC(body)), B.Rec.pos(J.pfs(body)), J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(back, body), MSX.TE(body))}, J.pfs(body), body)),
      MSX.XM{Norm.slow.reqs(Nat.is_eq(back, 0n), MSX.TC(body), MSX.TA(back, body), MSX.TE(body)), back}))))) == False{} : Bool}
  zd.f(J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(back, body), MSX.TE(body))}, J.pfs(body), body), fa, wp, back, body, hF)

def zd.m(+m: Maybe<&2, B.Res>, +fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +body: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hm: {J.judge_fs(None{}, J.pfs(body), body) == m : Maybe<&2, B.Res>},
  +hh: {PC.holds(fa, wp, MSX.TC(body), MSX.TA(back, body), MSX.TE(body)) == True{} : Bool},
  +hF: {isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(back, body), MSX.TE(body))}, J.pfs(body), body)) == False{} : Bool}) ->
  {BD.is_vwant(Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body)) == False{} : Bool}:
  match m:
    case Some{+r}:
      %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body), MSX.mkVd(fa, wp, MSX.VRP{r}), MSX.vd_some_eq(r, fa, wp, back, body, hm)) :
        {BD.is_vwant(_) == False{} : Bool}
      {==}
    case None{}:
      %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body), MSX.mkVd(fa, wp, MSX.vxP(body, MSX.sgP(64n, fa, wp, body, MSX.XA{back}))),
        MSX.vd_none_eq(fa, wp, back, body, hb, hwp, hm)) :
        {BD.is_vwant(_) == False{} : Bool}
      zd.t(fa, wp, back, body, hh, hF)

def eqTE(+body: String) ->
  {MSX.TE(body) == Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(B.Rec.field(B.Rec.fields(body), 3n))) : Nat}:
  +E1 = Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(B.Rec.field(B.Rec.fields(body), 3n)))
  %Equal.sym(Nat, B.Rec.pos(J.pfs(body)), B.Rec.pos(B.Rec.fields(body)), PF.pfs_pos(body)) :
    {Nat.add(Nat.sub(_, 1n), String.length(B.Rec.field(J.pfs(body), 3n))) == E1 : Nat}
  %Equal.sym(String, B.Rec.field(J.pfs(body), 3n), B.Rec.field(B.Rec.fields(body), 3n), PF.pfs_field(body, 3n, {==})) :
    {Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(_)) == E1 : Nat}
  {==}

def zero_decides(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +body: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hz: {BN.holdsW(PC.mkWin(fa, wp), B.Rec.field(J.pfs(body), 0n), 0n,
    Nat.add(Nat.sub(B.Rec.pos(J.pfs(body)), 1n), String.length(B.Rec.field(J.pfs(body), 3n)))) == True{} : Bool},
  +hp: {Nat.is_le(B.Rec.pos(J.pfs(body)), back) == True{} : Bool}) ->
  {BD.is_vwant(Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body)) == False{} : Bool}:
  +P0 = B.Rec.pos(J.pfs(body))
  +C0 = B.Rec.field(B.Rec.fields(body), 0n)
  +E1 = Nat.add(Nat.sub(B.Rec.pos(B.Rec.fields(body)), 1n), String.length(B.Rec.field(B.Rec.fields(body), 3n)))
  +hta = subz(Nat.sub(P0, 1n), back, N.le_trans(Nat.sub(P0, 1n), P0, back, X.sub_le(P0, 1n), hp))
  +hz2 = AB.subst(Nat, z => {BN.holdsW(PC.mkWin(fa, wp), MSX.TC(body), z, MSX.TE(body)) == True{} : Bool}, 0n, MSX.TA(back, body), Equal.sym(Nat, MSX.TA(back, body), 0n, hta), hz)
  +hh = hold_of(fa, wp, MSX.TC(body), MSX.TA(back, body), MSX.TE(body), hz2)
  +hF0 = zm(B.Fasta.find(fa, C0), fa, body, {==})
  +hF1 = AB.subst(String, z => {isON(J.fast(Some{PC.jtruth(fa, z, 0n, E1)}, J.pfs(body), body)) == False{} : Bool}, C0, MSX.TC(body),
    Equal.sym(String, MSX.TC(body), C0, PF.pfs_field(body, 0n, {==})), hF0)
  +hF2 = AB.subst(Nat, z => {isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), z, E1)}, J.pfs(body), body)) == False{} : Bool}, 0n, MSX.TA(back, body),
    Equal.sym(Nat, MSX.TA(back, body), 0n, hta), hF1)
  +hF3 = AB.subst(Nat, z => {isON(J.fast(Some{PC.jtruth(fa, MSX.TC(body), MSX.TA(back, body), z)}, J.pfs(body), body)) == False{} : Bool}, E1, MSX.TE(body),
    Equal.sym(Nat, MSX.TE(body), E1, eqTE(body)), hF2)
  zd.m(J.judge_fs(None{}, J.pfs(body), body), fa, wp, back, body, hb, hwp, {==}, hh, hF3)
