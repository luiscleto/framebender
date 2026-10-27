import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./proof_window_defs.bend as WS
import ./norm.bend as Norm
import ./tan.bend as V
import ./norm_line.bend as J
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var.bend as PV
import ./proof_window_lists.bend as W
import ./proof_window_info.bend as WI

# Proofs: reading the reference through a window (Norm.judge_in, norm_line.bend).
# window and window_enough were laws before the two-layer spec; they are now
# lemmas of the implementation proof (their definitions: proof_window_defs.bend,
# WS), used by the machine proof. normalized_valid (at the end) restates the
# law of LAWS.bend with every variable reusable (+); PROOF.bend forwards
# L.normalized_valid to it.
#
# Both proofs walk J.judge_in (the code) and L.judge (the spec) side by side:
# the same classification, except that the code reads the contig through the
# answer's window. The pieces: the window's bases are a slice of the contig's
# (window_bases); the REF check through the window is the whole-contig check
# (ref_sound, ref_none); the variant is valid when it reaches the normalizer
# (valid_of); and the var area's var_in_sound / var_in_enough, taken as the
# hypotheses VarSound / VarEnough.

# ---------------------------------------------------------------------------
# The var area's interface laws, as hypotheses
# ---------------------------------------------------------------------------

def VarSound() -> Type:
  (@+seq: List<&2, B.Base> -> @+off: Nat -> @+bases: List<&2, B.Base> -> @+v: B.Var -> @+w: B.Var ->
    @+hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>} ->
    @+hv: {L.valid(seq, v) == True{} : Bool} ->
    @+hw: {V.var_in(off, bases, v) == Some{w} : Maybe<&2, B.Var>} ->
    {w == V.normal(seq, v) : B.Var})

def VarEnough() -> Type:
  (@+seq: List<&2, B.Base> -> @+off: Nat -> @+bases: List<&2, B.Base> -> @+v: B.Var ->
    @+hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>} ->
    @+hv: {L.valid(seq, v) == True{} : Bool} ->
    @+hc: {PV.covers(off, L.len(bases), v, V.normal(seq, v)) == True{} : Bool} ->
    {Maybe.is_some(&2, B.Var, V.var_in(off, bases, v)) == True{} : Bool})

# ---------------------------------------------------------------------------
# The window's bases are a slice of the contig's
# ---------------------------------------------------------------------------

def window_bases(+r0: String, +off: Nat, +raw: String,
  +e: {String.eq(raw, String.take(String.drop(r0, off), String.length(raw))) == True{} : Bool}) ->
  {B.Bases.of_fasta(raw) == L.slice(B.Bases.of_fasta(r0), off, L.len(B.Bases.of_fasta(raw))) : List<&2, B.Base>}:
  %Equal.sym(Nat, L.len(B.Bases.of_fasta(raw)), String.length(raw), W.of_fasta_len(raw)) :
    {B.Bases.of_fasta(raw) == L.slice(B.Bases.of_fasta(r0), off, _) : List<&2, B.Base>}
  %Equal.sym(String, raw, String.take(String.drop(r0, off), String.length(raw)),
      W.string_eq_sound(raw, String.take(String.drop(r0, off), String.length(raw)), e)) :
    {B.Bases.of_fasta(_) == L.slice(B.Bases.of_fasta(r0), off, String.length(raw)) : List<&2, B.Base>}
  %Equal.sym(List<&2, B.Base>, B.Bases.of_fasta(String.take(String.drop(r0, off), String.length(raw))),
      List.take(&2, B.Base, B.Bases.of_fasta(String.drop(r0, off)), String.length(raw)),
      W.of_fasta_take(String.drop(r0, off), String.length(raw))) :
    {_ == L.slice(B.Bases.of_fasta(r0), off, String.length(raw)) : List<&2, B.Base>}
  %Equal.sym(List<&2, B.Base>, B.Bases.of_fasta(String.drop(r0, off)), List.drop(&2, B.Base, B.Bases.of_fasta(r0), off),
      W.of_fasta_drop(r0, off)) :
    {List.take(&2, B.Base, _, String.length(raw)) == L.slice(B.Bases.of_fasta(r0), off, String.length(raw)) : List<&2, B.Base>}
  {==}

# ---------------------------------------------------------------------------
# The REF check through the window
# ---------------------------------------------------------------------------

def fits_of_eq(+seq: List<&2, B.Base>, +clen: Nat, +start: Nat, +ref: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat}, +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +he: {B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(start, L.len(ref)), clen) == True{} : Bool}:
  %Equal.sym(Nat, clen, L.len(seq), hclen) : {Nat.is_le(Nat.add(start, L.len(ref)), _) == True{} : Bool}
  W.slice_len_fits(seq, start, L.len(ref), hl, W.bases_eq_len(L.slice(seq, start, L.len(ref)), ref, he))

def no_fit.go(+seq: List<&2, B.Base>, +clen: Nat, +start: Nat, +ref: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat}, +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hf: {Nat.is_le(Nat.add(start, L.len(ref)), clen) == False{} : Bool},
  +c: Bool, +hq: {B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) == c : Bool}) ->
  {B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) == False{} : Bool}:
  match c:
    case False{}:
      hq
    case True{}:
      Empty.absurd({B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) == False{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.add(start, L.len(ref)), clen), False{},
          Equal.sym(Bool, Nat.is_le(Nat.add(start, L.len(ref)), clen), True{}, fits_of_eq(seq, clen, start, ref, hclen, hl, hq)),
          hf)))

def ref_sound.go(+seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +start: Nat, +ref: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +fits: Bool, +covered: Bool,
  +hf: {Nat.is_le(Nat.add(start, L.len(ref)), clen) == fits : Bool},
  +hc: {Bool.and(Nat.is_le(off, start), Nat.is_le(Nat.add(start, L.len(ref)), Nat.add(off, L.len(bases)))) == covered : Bool},
  +b: Bool,
  +e: {J.ref_check.go(fits, covered, B.Bases.eq(L.slice(bases, Nat.sub(start, off), L.len(ref)), ref)) == Some{b} : Maybe<&2, Bool>}) ->
  {b == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}:
  match fits covered:
    case False{} _:
      %W.some_inj(Bool, False{}, b, e) : {_ == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}
      Equal.sym(Bool, B.Bases.eq(L.slice(seq, start, L.len(ref)), ref), False{},
        no_fit.go(seq, clen, start, ref, hclen, hl, hf, B.Bases.eq(L.slice(seq, start, L.len(ref)), ref), {==}))
    case True{} False{}:
      Empty.absurd({b == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}, W.none_ne_some(Bool, b, e))
    case True{} True{}:
      +h1 = P.and_true_l(Nat.is_le(off, start), Nat.is_le(Nat.add(start, L.len(ref)), Nat.add(off, L.len(bases))), hc)
      +h2 = P.and_true_r(Nat.is_le(off, start), Nat.is_le(Nat.add(start, L.len(ref)), Nat.add(off, L.len(bases))), hc)
      +hw = Equal.trans(List<&2, B.Base>, L.slice(bases, Nat.sub(start, off), L.len(ref)),
        L.slice(L.slice(seq, off, L.len(bases)), Nat.sub(start, off), L.len(ref)),
        L.slice(seq, start, L.len(ref)),
        Equal.cong(List<&2, B.Base>, List<&2, B.Base>, x => L.slice(x, Nat.sub(start, off), L.len(ref)),
          bases, L.slice(seq, off, L.len(bases)), hb),
        W.slice_win(seq, off, start, L.len(bases), L.len(ref), h1, h2))
      %W.some_inj(Bool, B.Bases.eq(L.slice(bases, Nat.sub(start, off), L.len(ref)), ref), b, e) :
        {_ == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}
      %Equal.sym(List<&2, B.Base>, L.slice(bases, Nat.sub(start, off), L.len(ref)), L.slice(seq, start, L.len(ref)), hw) :
        {B.Bases.eq(_, ref) == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}
      {==}

# A REF check the window can answer is the check on the whole contig.
def ref_sound(+seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>, +start: Nat, +ref: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +b: Bool,
  +e: {J.ref_check(clen, off, bases, start, ref) == Some{b} : Maybe<&2, Bool>}) ->
  {b == B.Bases.eq(L.slice(seq, start, L.len(ref)), ref) : Bool}:
  ref_sound.go(seq, clen, off, bases, start, ref, hclen, hb, hl,
    Nat.is_le(Nat.add(start, L.len(ref)), clen),
    Bool.and(Nat.is_le(off, start), Nat.is_le(Nat.add(start, L.len(ref)), Nat.add(off, L.len(bases)))),
    {==}, {==}, b, e)

# ---------------------------------------------------------------------------
# The variant reaching the normalizer is valid
# ---------------------------------------------------------------------------

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def valid_of(+seq: List<&2, B.Base>, +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == True{} : Bool},
  +he: {B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref) == True{} : Bool}) ->
  {L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}:
  +c1 = Nat.is_le(1n, p)
  +c2 = Nat.is_le(1n, L.len(ref))
  +c3 = Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts))
  +c4 = L.all_nonempty(alts)
  +c5 = B.Alleles.distinct(ref <> alts)
  +c6 = B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)
  and_tt(c1 && c2 && c3 && c4 && c5, c6,
    and_tt(c1 && c2 && c3 && c4, c5,
      and_tt(c1 && c2 && c3, c4,
        and_tt(c1 && c2, c3,
          and_tt(c1, c2, W.pos_of_ne_zero(p, hz), hl),
          hn),
        ha),
      hd),
    he)

# What a line that is not MALFORMED guarantees about its REF and ALTs.
def ok_ref(+fs: List<&2, String>, +hm: {B.Rec.malformed(fs) == False{} : Bool}) ->
  {Nat.is_le(1n, String.length(B.Rec.field(fs, 3n))) == True{} : Bool}:
  +a = Bool.or(Bool.or(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
    Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n))))
  +d = B.Text.is_letters(B.Rec.field(fs, 3n))
  W.letters_len(B.Rec.field(fs, 3n),
    W.not_false_inv(d, W.or_false_r(a, Bool.not(d),
      P.or_false_inv(Bool.or(a, Bool.not(d)), B.Text.any_empty(B.Rec.alts(fs)), hm))))

def ok_alts(+fs: List<&2, String>, +hm: {B.Rec.malformed(fs) == False{} : Bool}) ->
  {B.Text.any_empty(B.Rec.alts(fs)) == False{} : Bool}:
  +a = Bool.or(Bool.or(Bool.or(Nat.is_lt(List.length(&2, String, fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
    Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n))))
  W.or_false_r(a, B.Text.any_empty(B.Rec.alts(fs)), hm)

def ok_nalts(+fs: List<&2, String>, +alts: List<&2, List<&2, B.Base>>,
  +haa: {B.Alleles.read(B.Rec.alts(fs)) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, List<&2, B.Base>, alts), List.length(&2, String, B.Rec.alts(fs)), W.alts_len(B.Rec.alts(fs), alts, haa)) :
    {Nat.is_le(1n, _) == True{} : Bool}
  W.split_ne(B.Rec.field(fs, 4n), ',')

# ---------------------------------------------------------------------------
# window
# ---------------------------------------------------------------------------

def win.norm.eq(+fs: List<&2, String>, +v: B.Var, +w: B.Var, +r: B.Res,
  +hr: {Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)}} == Some{r} : Maybe<&2, B.Res>}) ->
  {r == B.Res{B.Normalized{}, L.pos_of(w), B.Rec.rebuild(fs, v, w), B.Rec.stale(fs, v, w)} : B.Res}:
  match w:
    case B.Var{+p, +a, +b}:
      Equal.sym(B.Res, B.Res{B.Normalized{}, p, B.Rec.rebuild(fs, v, B.Var{p, a, b}), B.Rec.stale(fs, v, B.Var{p, a, b})}, r,
        W.some_inj(B.Res, B.Res{B.Normalized{}, p, B.Rec.rebuild(fs, v, B.Var{p, a, b}), B.Rec.stale(fs, v, B.Var{p, a, b})}, r, hr))

def win.norm(sound: VarSound(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +off: Nat, +bases: List<&2, B.Base>, +v: B.Var,
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hv: {L.valid(seq, v) == True{} : Bool},
  +mw: Maybe<&2, B.Var>, +hmw: {V.var_in(off, bases, v) == mw : Maybe<&2, B.Var>},
  +r: B.Res, +hr: {J.found.norm(mw, fs, v) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.problem(None{}, fs, body, seq, v) : B.Res}:
  match mw:
    case None{}:
      Empty.absurd({r == L.problem(None{}, fs, body, seq, v) : B.Res}, W.none_ne_some(B.Res, r, hr))
    case Some{+w}:
      %sound(seq, off, bases, v, w, hb, hv, hmw) :
        {r == B.Res{B.Normalized{}, L.pos_of(_), B.Rec.rebuild(fs, v, _), B.Rec.stale(fs, v, _)} : B.Res}
      win.norm.eq(fs, v, w, r, hr)

def win.ref.b(sound: VarSound(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +off: Nat, +bases: List<&2, B.Base>,
  +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == True{} : Bool},
  +b: Bool, +hbeq: {b == B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref) : Bool},
  +r: B.Res, +hr: {J.found.ref(Some{b}, off, bases, fs, body, B.Var{p, ref, alts}) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.problem(L.first(Bool.not(b), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}) : B.Res}:
  match b:
    case False{}:
      Equal.sym(B.Res, J.mk(B.Problem{B.RefMismatch{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.RefMismatch{}}, fs, body), r, hr))
    case True{}:
      +he = Equal.sym(Bool, True{}, B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), hbeq)
      win.norm(sound, fs, body, seq, off, bases, B.Var{p, ref, alts}, hb,
        valid_of(seq, p, ref, alts, hz, hl, hn, ha, hd, he),
        V.var_in(off, bases, B.Var{p, ref, alts}), {==}, r, hr)

def win.ref(sound: VarSound(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>,
  +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == True{} : Bool},
  +ok: Maybe<&2, Bool>, +hok: {J.ref_check(clen, off, bases, Nat.sub(p, 1n), ref) == ok : Maybe<&2, Bool>},
  +r: B.Res, +hr: {J.found.ref(ok, off, bases, fs, body, B.Var{p, ref, alts}) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.problem(L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}) : B.Res}:
  match ok:
    case None{}:
      Empty.absurd({r == L.problem(L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}) : B.Res},
        W.none_ne_some(B.Res, r, hr))
    case Some{+b}:
      +hbeq = ref_sound(seq, clen, off, bases, Nat.sub(p, 1n), ref, hclen, hb, hl, b, hok)
      %hbeq : {r == L.problem(L.first(Bool.not(_), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}) : B.Res}
      win.ref.b(sound, fs, body, seq, off, bases, p, ref, alts, hb, hz, hl, hn, ha, hd, b, hbeq, r, hr)

def win.problem(sound: VarSound(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>,
  +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +zero: Bool, +dist: Bool,
  +hz: {Nat.is_eq(p, 0n) == zero : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == dist : Bool},
  +r: B.Res, +hr: {J.found.problem(zero, dist, clen, off, bases, fs, body, B.Var{p, ref, alts}) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.problem(L.first(zero, B.BadPos{}, L.first(Bool.not(dist), B.AltDup{},
    L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}))), fs, body, seq, B.Var{p, ref, alts}) : B.Res}:
  match zero dist:
    case True{} _:
      Equal.sym(B.Res, J.mk(B.Problem{B.BadPos{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.BadPos{}}, fs, body), r, hr))
    case False{} False{}:
      Equal.sym(B.Res, J.mk(B.Problem{B.AltDup{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.AltDup{}}, fs, body), r, hr))
    case False{} True{}:
      win.ref(sound, fs, body, seq, clen, off, bases, p, ref, alts, hclen, hb, hz, hl, hn, ha, hd,
        J.ref_check(clen, off, bases, Nat.sub(p, 1n), ref), {==}, r, hr)

def win.found(sound: VarSound(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +bases: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hm: {B.Rec.malformed(fs) == False{} : Bool},
  +eok: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>,
  +hrr: {B.Allele.read(B.Rec.field(fs, 3n)) == rr : Maybe<&2, List<&2, B.Base>>},
  +haa: {B.Alleles.read(B.Rec.alts(fs)) == aa : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +r: B.Res, +hr: {J.found(eok, rr, aa, clen, off, bases, fs, body) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge.bases(eok, rr, aa, fs, body, seq) : B.Res}:
  match eok rr aa:
    case False{} Some{ref} Some{alts}:
      Equal.sym(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, hr))
    case False{} Some{ref} None{}:
      Equal.sym(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, hr))
    case False{} None{} _:
      Equal.sym(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.BadEnd{}}, fs, body), r, hr))
    case True{} Some{+ref} Some{+alts}:
      win.problem(sound, fs, body, seq, clen, off, bases, B.Rec.pos(fs), ref, alts, hclen, hb,
        W.allele_ne(B.Rec.field(fs, 3n), ref, ok_ref(fs, hm), hrr),
        ok_nalts(fs, alts, haa),
        W.alts_ok(B.Rec.alts(fs), alts, ok_alts(fs, hm), haa),
        Nat.is_eq(B.Rec.pos(fs), 0n), B.Alleles.distinct(ref <> alts), {==}, {==}, r, hr)
    case True{} Some{ref} None{}:
      Equal.sym(B.Res, J.mk(B.Problem{B.NonAcgtn{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.NonAcgtn{}}, fs, body), r, hr))
    case True{} None{} _:
      Equal.sym(B.Res, J.mk(B.Problem{B.NonAcgtn{}}, fs, body), r, W.some_inj(B.Res, J.mk(B.Problem{B.NonAcgtn{}}, fs, body), r, hr))

def win.known(sound: VarSound(), +fs: List<&2, String>, +body: String, +hm: {B.Rec.malformed(fs) == False{} : Bool},
  m: Maybe<&2, String>, +clen: Nat, +off: Nat, +raw: String, +r: B.Res,
  +ht: {WS.known.ok(m, clen, off, raw) == True{} : Bool},
  +hr: {J.judge_in.ans(Some{Pr.Known{clen, off, raw}}, fs, body) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge.contig(m, fs, body) : B.Res}:
  match m:
    case None{}:
      Empty.absurd({r == L.judge.contig(None{}, fs, body) : B.Res}, P.false_ne_true(ht))
    case Some{+r0}:
      +hc = Nat.is_eq(clen, String.length(r0))
      +hs = String.eq(raw, String.take(String.drop(r0, off), String.length(raw)))
      +hclen = Equal.trans(Nat, clen, String.length(r0), L.len(B.Bases.of_fasta(r0)),
        P.eq_sound(clen, String.length(r0), P.and_true_l(hc, hs, ht)),
        Equal.sym(Nat, L.len(B.Bases.of_fasta(r0)), String.length(r0), W.of_fasta_len(r0)))
      +hb = window_bases(r0, off, raw, P.and_true_r(hc, hs, ht))
      +ref = B.Rec.field(fs, 3n)
      +e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      %WI.end_ok_eq(B.Rec.field(fs, 7n), e) :
        {r == L.judge.bases(_, B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, body, B.Bases.of_fasta(r0)) : B.Res}
      win.found(sound, fs, body, B.Bases.of_fasta(r0), clen, off, B.Bases.of_fasta(raw), hclen, hb, hm,
        J.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), {==}, {==}, r, hr)

def win.unknown(+fs: List<&2, String>, +body: String, m: Maybe<&2, String>,
  +ht: {Maybe.is_none(&2, String, m) == True{} : Bool},
  +r: B.Res, +hr: {Some{J.mk(B.NoContig{}, fs, body)} == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge.contig(m, fs, body) : B.Res}:
  match m:
    case None{}:
      Equal.sym(B.Res, J.mk(B.NoContig{}, fs, body), r, W.some_inj(B.Res, J.mk(B.NoContig{}, fs, body), r, hr))
    case Some{x}:
      Empty.absurd({r == L.judge.contig(Some{x}, fs, body) : B.Res}, P.false_ne_true(ht))

def win.ans(sound: VarSound(), +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String,
  +hm: {B.Rec.malformed(fs) == False{} : Bool}, a: Maybe<&2, Pr.Ans>, +r: B.Res,
  +ht: {WS.truthful(fa, B.Rec.field(fs, 0n), a) == True{} : Bool},
  +hr: {J.judge_in.ans(a, fs, body) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body) : B.Res}:
  match a:
    case None{}:
      Empty.absurd({r == L.judge.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body) : B.Res}, W.none_ne_some(B.Res, r, hr))
    case Some{Pr.Unknown{}}:
      win.unknown(fs, body, B.Fasta.find(fa, B.Rec.field(fs, 0n)), ht, r, hr)
    case Some{Pr.Known{+clen, +off, +raw}}:
      win.known(sound, fs, body, hm, B.Fasta.find(fa, B.Rec.field(fs, 0n)), clen, off, raw, r, ht, hr)

def win.shape(sound: VarSound(), +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String,
  +bad: Bool, +skip: Bool, +hm: {B.Rec.malformed(fs) == bad : Bool}, a: Maybe<&2, Pr.Ans>, +r: B.Res,
  +ht: {WS.truthful(fa, B.Rec.field(fs, 0n), a) == True{} : Bool},
  +hr: {J.judge_in.go(bad, skip, a, fs, body) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge.shape(bad, skip, fa, fs, body) : B.Res}:
  match bad skip:
    case True{} _:
      Equal.sym(B.Res, J.mk(B.Broken{}, fs, body), r, W.some_inj(B.Res, J.mk(B.Broken{}, fs, body), r, hr))
    case False{} True{}:
      Equal.sym(B.Res, J.mk(B.Skipped{}, fs, body), r, W.some_inj(B.Res, J.mk(B.Skipped{}, fs, body), r, hr))
    case False{} False{}:
      win.ans(sound, fa, fs, body, hm, a, r, ht, hr)

# window, given var_in_sound.
def window.core(sound: VarSound(), +fa: List<&2, B.Contig>, +body: String, a: Maybe<&2, Pr.Ans>, +r: B.Res,
  +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool},
  +hr: {Norm.judge_in(a, body) == Some{r} : Maybe<&2, B.Res>}) ->
  {r == L.judge(fa, body) : B.Res}:
  win.shape(sound, fa, B.Rec.fields(body), body, B.Rec.malformed(B.Rec.fields(body)), B.Rec.out_of_scope(B.Rec.fields(body)),
    {==}, a, r, ht, hr)

# ---------------------------------------------------------------------------
# window_enough
# ---------------------------------------------------------------------------

def some_ne_none(-A: Data, -x: A, e: {Some{x} == None{} : Maybe<&2, A>}) -> Empty:
  W.none_ne_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, e))

def ref_none.fits(+fits: Bool, +covered: Bool, +eq: Bool, e: {J.ref_check.go(fits, covered, eq) == None{} : Maybe<&2, Bool>}) ->
  {fits == True{} : Bool}:
  match fits covered:
    case False{} _:
      Empty.absurd({False{} == True{} : Bool}, some_ne_none(Bool, False{}, e))
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == True{} : Bool}, some_ne_none(Bool, eq, e))

def ref_none.cov(+fits: Bool, +covered: Bool, +eq: Bool, e: {J.ref_check.go(fits, covered, eq) == None{} : Maybe<&2, Bool>}) ->
  {covered == False{} : Bool}:
  match fits covered:
    case False{} _:
      Empty.absurd({covered == False{} : Bool}, some_ne_none(Bool, False{}, e))
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, some_ne_none(Bool, eq, e))

# The upper end of what the line needs, read through the window's length.
def cov_hi(+s: Nat, +n: Nat, +rlen: Nat, +clen: Nat, +off: Nat, +lb: Nat, +lr: Nat,
  +hn: {n == rlen : Nat}, +hfit: {Nat.is_le(Nat.add(s, n), clen) == True{} : Bool}, +hlr: {lb == lr : Nat},
  +h: {Nat.is_le(Nat.min(Nat.add(s, rlen), clen), Nat.add(off, lr)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(s, n), Nat.add(off, lb)) == True{} : Bool}:
  %Equal.sym(Nat, lb, lr, hlr) : {Nat.is_le(Nat.add(s, n), Nat.add(off, _)) == True{} : Bool}
  %W.min_le_id(Nat.add(s, n), clen, hfit) : {Nat.is_le(_, Nat.add(off, lr)) == True{} : Bool}
  %Equal.sym(Nat, n, rlen, hn) : {Nat.is_le(Nat.min(Nat.add(s, _), clen), Nat.add(off, lr)) == True{} : Bool}
  h

# he with the REF check's value x in place of the equal y.
def en.he(+fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var, +p: Nat, +rlen: Nat, +a: Maybe<&2, Pr.Ans>,
  +x: Bool, +y: Bool, +hxy: {x == y : Bool},
  +he: {WS.enough.go(L.problem(L.first(Bool.not(y), B.RefMismatch{}, None{}), fs, body, seq, v), p, rlen, a) == True{} : Bool}) ->
  {WS.enough.go(L.problem(L.first(Bool.not(x), B.RefMismatch{}, None{}), fs, body, seq, v), p, rlen, a) == True{} : Bool}:
  %Equal.sym(Bool, x, y, hxy) : {WS.enough.go(L.problem(L.first(Bool.not(_), B.RefMismatch{}, None{}), fs, body, seq, v), p, rlen, a) == True{} : Bool}
  he

# What the line needs, as the two ends of covers, whichever outcome the REF
# check c gives.
def en.lo(+c: Bool, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var, +p: Nat, +rlen: Nat,
  +clen: Nat, +off: Nat, +raw: String,
  +he: {WS.enough.go(L.problem(L.first(Bool.not(c), B.RefMismatch{}, None{}), fs, body, seq, v), p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Nat.is_le(off, Nat.sub(p, 1n)) == True{} : Bool}:
  match c:
    case False{}:
      P.and_true_l(Nat.is_le(off, Nat.sub(p, 1n)), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw))), he)
    case True{}:
      +k = Nat.sub(L.pos_of(V.normal(seq, v)), 2n)
      W.le_min_l(off, Nat.sub(p, 1n), k, P.and_true_l(Nat.is_le(off, Nat.min(Nat.sub(p, 1n), k)), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw))), he))

def en.hi(+c: Bool, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var, +p: Nat, +rlen: Nat,
  +clen: Nat, +off: Nat, +raw: String,
  +he: {WS.enough.go(L.problem(L.first(Bool.not(c), B.RefMismatch{}, None{}), fs, body, seq, v), p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw))) == True{} : Bool}:
  match c:
    case False{}:
      P.and_true_r(Nat.is_le(off, Nat.sub(p, 1n)), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw))), he)
    case True{}:
      P.and_true_r(Nat.is_le(off, Nat.min(Nat.sub(p, 1n), Nat.sub(L.pos_of(V.normal(seq, v)), 2n))), Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw))), he)

def en.norm(+fs: List<&2, String>, +v: B.Var, +mw: Maybe<&2, B.Var>, +hs: {Maybe.is_some(&2, B.Var, mw) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.found.norm(mw, fs, v)) == True{} : Bool}:
  match mw:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, P.false_ne_true(hs))
    case Some{w}:
      {==}

# What the normalizer needs, from what the line needs.
def en.covers(+seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +p: Nat, +rlen: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hrl: {L.len(ref) == rlen : Nat},
  +hfit: {Nat.is_le(Nat.add(Nat.sub(p, 1n), L.len(ref)), clen) == True{} : Bool},
  +he: {WS.covers(Some{Pr.Known{clen, off, raw}}, Nat.min(Nat.sub(p, 1n), Nat.sub(L.pos_of(V.normal(seq, B.Var{p, ref, alts})), 2n)), Nat.add(Nat.sub(p, 1n), rlen)) == True{} : Bool}) ->
  {PV.covers(off, L.len(bases), B.Var{p, ref, alts}, V.normal(seq, B.Var{p, ref, alts})) == True{} : Bool}:
  +lo = Nat.is_le(off, Nat.min(Nat.sub(p, 1n), Nat.sub(L.pos_of(V.normal(seq, B.Var{p, ref, alts})), 2n)))
  +hi = Nat.is_le(Nat.min(Nat.add(Nat.sub(p, 1n), rlen), clen), Nat.add(off, String.length(raw)))
  and_tt(lo, Nat.is_le(Nat.add(Nat.sub(p, 1n), L.len(ref)), Nat.add(off, L.len(bases))),
    P.and_true_l(lo, hi, he),
    cov_hi(Nat.sub(p, 1n), L.len(ref), rlen, clen, off, L.len(bases), String.length(raw), hrl, hfit, hlr,
      P.and_true_r(lo, hi, he)))

def en.ref.b(enough: VarEnough(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +p: Nat, +rlen: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hrl: {L.len(ref) == rlen : Nat},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == True{} : Bool},
  +b: Bool, +hbeq: {b == B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref) : Bool},
  +he: {WS.enough.go(L.problem(L.first(Bool.not(b), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}), p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.found.ref(Some{b}, off, bases, fs, body, B.Var{p, ref, alts})) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +v = {B.Var{p, ref, alts} : B.Var}
      +ht = Equal.sym(Bool, True{}, B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), hbeq)
      en.norm(fs, v, V.var_in(off, bases, v),
        enough(seq, off, bases, v, hb, valid_of(seq, p, ref, alts, hz, hl, hn, ha, hd, ht),
          en.covers(seq, clen, off, raw, bases, p, rlen, ref, alts, hlr, hrl,
            fits_of_eq(seq, clen, Nat.sub(p, 1n), ref, hclen, hl, ht), he)))

# The window not holding REF contradicts it holding what the line needs.
def en.none(+fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +p: Nat, +rlen: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hrl: {L.len(ref) == rlen : Nat},
  +hok: {J.ref_check(clen, off, bases, Nat.sub(p, 1n), ref) == None{} : Maybe<&2, Bool>},
  +c: Bool, +hq: {B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref) == c : Bool},
  +he: {WS.enough.go(L.problem(L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}), p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  Empty:
  +s = Nat.sub(p, 1n)
  +n = L.len(ref)
  +v = {B.Var{p, ref, alts} : B.Var}
  +hc = en.he(fs, body, seq, v, p, rlen, Some{Pr.Known{clen, off, raw}}, c, B.Bases.eq(L.slice(seq, s, n), ref),
    Equal.sym(Bool, B.Bases.eq(L.slice(seq, s, n), ref), c, hq), he)
  +fits = Nat.is_le(Nat.add(s, n), clen)
  +cov = Bool.and(Nat.is_le(off, s), Nat.is_le(Nat.add(s, n), Nat.add(off, L.len(bases))))
  +eq = B.Bases.eq(L.slice(bases, Nat.sub(s, off), n), ref)
  +hcov = and_tt(Nat.is_le(off, s), Nat.is_le(Nat.add(s, n), Nat.add(off, L.len(bases))),
    en.lo(c, fs, body, seq, v, p, rlen, clen, off, raw, hc),
    cov_hi(s, n, rlen, clen, off, L.len(bases), String.length(raw), hrl, ref_none.fits(fits, cov, eq, hok), hlr,
      en.hi(c, fs, body, seq, v, p, rlen, clen, off, raw, hc)))
  P.true_ne_false(Equal.trans(Bool, True{}, cov, False{}, Equal.sym(Bool, cov, True{}, hcov), ref_none.cov(fits, cov, eq, hok)))

def en.ref(enough: VarEnough(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +p: Nat, +rlen: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hz: {Nat.is_eq(p, 0n) == False{} : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hrl: {L.len(ref) == rlen : Nat},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == True{} : Bool},
  +ok: Maybe<&2, Bool>, +hok: {J.ref_check(clen, off, bases, Nat.sub(p, 1n), ref) == ok : Maybe<&2, Bool>},
  +he: {WS.enough.go(L.problem(L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}), fs, body, seq, B.Var{p, ref, alts}), p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.found.ref(ok, off, bases, fs, body, B.Var{p, ref, alts})) == True{} : Bool}:
  match ok:
    case None{}:
      Empty.absurd({False{} == True{} : Bool},
        en.none(fs, body, seq, clen, off, raw, bases, p, rlen, ref, alts, hlr, hrl, hok,
          B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), {==}, he))
    case Some{+b}:
      +hbeq = ref_sound(seq, clen, off, bases, Nat.sub(p, 1n), ref, hclen, hb, hl, b, hok)
      en.ref.b(enough, fs, body, seq, clen, off, raw, bases, p, rlen, ref, alts, hclen, hb, hlr, hz, hl, hrl, hn, ha, hd, b, hbeq,
        en.he(fs, body, seq, B.Var{p, ref, alts}, p, rlen, Some{Pr.Known{clen, off, raw}}, b, B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), hbeq, he))

def en.problem(enough: VarEnough(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +p: Nat, +rlen: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hrl: {L.len(ref) == rlen : Nat},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +zero: Bool, +dist: Bool,
  +hz: {Nat.is_eq(p, 0n) == zero : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == dist : Bool},
  +he: {WS.enough.go(L.problem(L.first(zero, B.BadPos{}, L.first(Bool.not(dist), B.AltDup{},
    L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}))), fs, body, seq, B.Var{p, ref, alts}),
    p, rlen, Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.found.problem(zero, dist, clen, off, bases, fs, body, B.Var{p, ref, alts})) == True{} : Bool}:
  match zero dist:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      en.ref(enough, fs, body, seq, clen, off, raw, bases, p, rlen, ref, alts, hclen, hb, hlr, hz, hl, hrl, hn, ha, hd,
        J.ref_check(clen, off, bases, Nat.sub(p, 1n), ref), {==}, he)

def en.found(enough: VarEnough(), +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +clen: Nat, +off: Nat, +raw: String, +bases: List<&2, B.Base>,
  +hclen: {clen == L.len(seq) : Nat},
  +hb: {bases == L.slice(seq, off, L.len(bases)) : List<&2, B.Base>},
  +hlr: {L.len(bases) == String.length(raw) : Nat},
  +hm: {B.Rec.malformed(fs) == False{} : Bool},
  +eok: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>,
  +hrr: {B.Allele.read(B.Rec.field(fs, 3n)) == rr : Maybe<&2, List<&2, B.Base>>},
  +haa: {B.Alleles.read(B.Rec.alts(fs)) == aa : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +he: {WS.enough.go(L.judge.bases(eok, rr, aa, fs, body, seq), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.found(eok, rr, aa, clen, off, bases, fs, body)) == True{} : Bool}:
  match eok rr aa:
    case False{} Some{ref} Some{alts}:
      {==}
    case False{} Some{ref} None{}:
      {==}
    case False{} None{} _:
      {==}
    case True{} Some{+ref} Some{+alts}:
      en.problem(enough, fs, body, seq, clen, off, raw, bases, B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), ref, alts,
        hclen, hb, hlr,
        W.allele_ne(B.Rec.field(fs, 3n), ref, ok_ref(fs, hm), hrr),
        W.read_len(B.Rec.field(fs, 3n), ref, hrr),
        ok_nalts(fs, alts, haa),
        W.alts_ok(B.Rec.alts(fs), alts, ok_alts(fs, hm), haa),
        Nat.is_eq(B.Rec.pos(fs), 0n), B.Alleles.distinct(ref <> alts), {==}, {==}, he)
    case True{} Some{ref} None{}:
      {==}
    case True{} None{} _:
      {==}

def en.known(enough: VarEnough(), +fs: List<&2, String>, +body: String, +hm: {B.Rec.malformed(fs) == False{} : Bool},
  m: Maybe<&2, String>, +clen: Nat, +off: Nat, +raw: String,
  +ht: {WS.known.ok(m, clen, off, raw) == True{} : Bool},
  +he: {WS.enough.go(L.judge.contig(m, fs, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), Some{Pr.Known{clen, off, raw}}) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.judge_in.ans(Some{Pr.Known{clen, off, raw}}, fs, body)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&2, B.Res, J.judge_in.ans(Some{Pr.Known{clen, off, raw}}, fs, body)) == True{} : Bool}, P.false_ne_true(ht))
    case Some{+r0}:
      +hc = Nat.is_eq(clen, String.length(r0))
      +hs = String.eq(raw, String.take(String.drop(r0, off), String.length(raw)))
      +hclen = Equal.trans(Nat, clen, String.length(r0), L.len(B.Bases.of_fasta(r0)),
        P.eq_sound(clen, String.length(r0), P.and_true_l(hc, hs, ht)),
        Equal.sym(Nat, L.len(B.Bases.of_fasta(r0)), String.length(r0), W.of_fasta_len(r0)))
      +hb = window_bases(r0, off, raw, P.and_true_r(hc, hs, ht))
      +ref = B.Rec.field(fs, 3n)
      +e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      %Equal.sym(Bool, J.end_ok(B.Rec.field(fs, 7n), e), B.Info.end_ok(B.Rec.field(fs, 7n), e), WI.end_ok_eq(B.Rec.field(fs, 7n), e)) :
        {Maybe.is_some(&2, B.Res, J.found(_, B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), clen, off, B.Bases.of_fasta(raw), fs, body)) == True{} : Bool}
      en.found(enough, fs, body, B.Bases.of_fasta(r0), clen, off, raw, B.Bases.of_fasta(raw), hclen, hb, W.of_fasta_len(raw), hm,
        B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), {==}, {==}, he)

# With no answer the line must need nothing.
def en.noans.code(+k: B.Code, +fs: List<&2, String>, +body: String, +p: Nat, +rlen: Nat,
  +he: {WS.enough.go(L.res(B.Problem{k}, fs, body), p, rlen, None{}) == True{} : Bool}) -> Empty:
  match k:
    case B.Malformed{}:
      P.false_ne_true(he)
    case B.UnknownChrom{}:
      P.false_ne_true(he)
    case B.BadEnd{}:
      P.false_ne_true(he)
    case B.NonAcgtn{}:
      P.false_ne_true(he)
    case B.BadPos{}:
      P.false_ne_true(he)
    case B.AltDup{}:
      P.false_ne_true(he)
    case B.RefMismatch{}:
      P.false_ne_true(he)
    case B.Unsorted{}:
      P.false_ne_true(he)
    case B.NoHeader{}:
      P.false_ne_true(he)
    case B.Stale{}:
      P.false_ne_true(he)

def en.noans.problem(+c: Maybe<&2, B.Code>, +fs: List<&2, String>, +body: String, +p: Nat, +rlen: Nat, +seq: List<&2, B.Base>, +v: B.Var,
  +he: {WS.enough.go(L.problem(c, fs, body, seq, v), p, rlen, None{}) == True{} : Bool}) -> Empty:
  match c:
    case None{}:
      P.false_ne_true(he)
    case Some{+k}:
      en.noans.code(k, fs, body, p, rlen, he)

def en.noans.bases(+eok: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>,
  +fs: List<&2, String>, +body: String, +p: Nat, +rlen: Nat, +seq: List<&2, B.Base>,
  +he: {WS.enough.go(L.judge.bases(eok, rr, aa, fs, body, seq), p, rlen, None{}) == True{} : Bool}) -> Empty:
  match eok rr aa:
    case _ Some{+ref} Some{+alts}:
      +v = {B.Var{B.Rec.pos(fs), ref, alts} : B.Var}
      en.noans.problem(L.checks(eok, seq, v), fs, body, p, rlen, seq, v, he)
    case True{} Some{ref} None{}:
      P.false_ne_true(he)
    case True{} None{} _:
      P.false_ne_true(he)
    case False{} Some{ref} None{}:
      P.false_ne_true(he)
    case False{} None{} _:
      P.false_ne_true(he)

def en.noans(+fs: List<&2, String>, +body: String, +p: Nat, +rlen: Nat, m: Maybe<&2, String>,
  +he: {WS.enough.go(L.judge.contig(m, fs, body), p, rlen, None{}) == True{} : Bool}) -> Empty:
  match m:
    case None{}:
      P.false_ne_true(he)
    case Some{+raw}:
      +ref = B.Rec.field(fs, 3n)
      e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      en.noans.bases(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, body, p, rlen,
        B.Bases.of_fasta(raw), he)

def en.ans(enough: VarEnough(), +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String,
  +hm: {B.Rec.malformed(fs) == False{} : Bool}, a: Maybe<&2, Pr.Ans>,
  +ht: {WS.truthful(fa, B.Rec.field(fs, 0n), a) == True{} : Bool},
  +he: {WS.enough.go(L.judge.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), a) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.judge_in.ans(a, fs, body)) == True{} : Bool}:
  match a:
    case None{}:
      Empty.absurd({False{} == True{} : Bool},
        en.noans(fs, body, B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), B.Fasta.find(fa, B.Rec.field(fs, 0n)), he))
    case Some{Pr.Unknown{}}:
      {==}
    case Some{Pr.Known{+clen, +off, +raw}}:
      en.known(enough, fs, body, hm, B.Fasta.find(fa, B.Rec.field(fs, 0n)), clen, off, raw, ht, he)

def en.shape(enough: VarEnough(), +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String,
  +bad: Bool, +skip: Bool, +hm: {B.Rec.malformed(fs) == bad : Bool}, a: Maybe<&2, Pr.Ans>,
  +ht: {WS.truthful(fa, B.Rec.field(fs, 0n), a) == True{} : Bool},
  +he: {WS.enough.go(L.judge.shape(bad, skip, fa, fs, body), B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n)), a) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, J.judge_in.go(bad, skip, a, fs, body)) == True{} : Bool}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      en.ans(enough, fa, fs, body, hm, a, ht, he)

# window_enough, given var_in_enough.
def window_enough.core(enough: VarEnough(), +fa: List<&2, B.Contig>, +body: String, a: Maybe<&2, Pr.Ans>,
  +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool},
  +he: {WS.enough(fa, body, a) == True{} : Bool}) ->
  {Maybe.is_some(&2, B.Res, Norm.judge_in(a, body)) == True{} : Bool}:
  en.shape(enough, fa, B.Rec.fields(body), body, B.Rec.malformed(B.Rec.fields(body)), B.Rec.out_of_scope(B.Rec.fields(body)),
    {==}, a, ht, he)

law window:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +r: B.Res
  for +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool}
  for +hr: {Norm.judge_in(a, body) == Some{r} : Maybe<&2, B.Res>}
  {r == L.judge(fa, body) : B.Res}

def window(fa, body, a, r, ht, hr):
  window.core(PV.var_in_sound, fa, body, a, r, ht, hr)

law window_enough:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +a: Maybe<&2, Pr.Ans>
  for +ht: {WS.truthful(fa, WS.chrom_of(body), a) == True{} : Bool}
  for +he: {WS.enough(fa, body, a) == True{} : Bool}
  {Maybe.is_some(&2, B.Res, Norm.judge_in(a, body)) == True{} : Bool}

def window_enough(fa, body, a, ht, he):
  window_enough.core(PV.var_in_enough, fa, body, a, ht, he)

# ---------------------------------------------------------------------------
# normalized_valid: a record judge normalizes describes a valid variant
# ---------------------------------------------------------------------------

# The checks judge makes, as flags: only all passing leaves the record to be
# normalized, and then valid_of applies.
def nv.checks(+fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +eok: Bool, +z: Bool, +d: Bool, +q: Bool,
  +hz: {Nat.is_eq(p, 0n) == z : Bool},
  +hd: {B.Alleles.distinct(ref <> alts) == d : Bool},
  +hq: {B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref) == q : Bool},
  +hl: {Nat.is_le(1n, L.len(ref)) == True{} : Bool},
  +hn: {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool},
  +ha: {L.all_nonempty(alts) == True{} : Bool},
  +h: {L.is_normalized(L.problem(L.first(Bool.not(eok), B.BadEnd{}, L.first(z, B.BadPos{}, L.first(Bool.not(d), B.AltDup{},
    L.first(Bool.not(q), B.RefMismatch{}, None{})))), fs, body, seq, B.Var{p, ref, alts})) == True{} : Bool}) ->
  {L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}:
  match eok z d q:
    case True{} False{} True{} True{}:
      valid_of(seq, p, ref, alts, hz, hl, hn, ha, hd, hq)
    case False{} _ _ _:
      Empty.absurd({L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}, P.false_ne_true(h))
    case True{} True{} _ _:
      Empty.absurd({L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}, P.false_ne_true(h))
    case True{} False{} False{} _:
      Empty.absurd({L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}, P.false_ne_true(h))
    case True{} False{} True{} False{}:
      Empty.absurd({L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}, P.false_ne_true(h))

def nv.bases(+fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>,
  +hm: {B.Rec.malformed(fs) == False{} : Bool},
  +eok: Bool, +rr: Maybe<&2, List<&2, B.Base>>, +aa: Maybe<&2, List<&2, List<&2, B.Base>>>,
  +hrr: {B.Allele.read(B.Rec.field(fs, 3n)) == rr : Maybe<&2, List<&2, B.Base>>},
  +haa: {B.Alleles.read(B.Rec.alts(fs)) == aa : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +h: {L.is_normalized(L.judge.bases(eok, rr, aa, fs, body, seq)) == True{} : Bool}) ->
  {L.line_valid.vars(rr, aa, seq, B.Rec.pos(fs)) == True{} : Bool}:
  match eok rr aa:
    case True{} Some{+ref} Some{+alts}:
      +p = B.Rec.pos(fs)
      nv.checks(fs, body, seq, p, ref, alts, True{}, Nat.is_eq(p, 0n), B.Alleles.distinct(ref <> alts),
        B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), {==}, {==}, {==},
        W.allele_ne(B.Rec.field(fs, 3n), ref, ok_ref(fs, hm), hrr),
        ok_nalts(fs, alts, haa),
        W.alts_ok(B.Rec.alts(fs), alts, ok_alts(fs, hm), haa), h)
    case False{} Some{ref} Some{alts}:
      Empty.absurd({L.line_valid.vars(Some{ref}, Some{alts}, seq, B.Rec.pos(fs)) == True{} : Bool}, P.false_ne_true(h))
    case _ Some{ref} None{}:
      Empty.absurd({L.line_valid.vars(Some{ref}, None{}, seq, B.Rec.pos(fs)) == True{} : Bool}, P.false_ne_true(h))
    case _ None{} _:
      Empty.absurd({L.line_valid.vars(None{}, aa, seq, B.Rec.pos(fs)) == True{} : Bool}, P.false_ne_true(h))

def nv.contig(+fs: List<&2, String>, +body: String, m: Maybe<&2, String>,
  +hm: {B.Rec.malformed(fs) == False{} : Bool},
  +h: {L.is_normalized(L.judge.contig(m, fs, body)) == True{} : Bool}) ->
  {L.line_valid.contig(m, fs) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({L.line_valid.contig(None{}, fs) == True{} : Bool}, P.false_ne_true(h))
    case Some{+raw}:
      +ref = B.Rec.field(fs, 3n)
      nv.bases(fs, body, B.Bases.of_fasta(raw), hm,
        B.Info.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)),
        B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), {==}, {==}, h)

def nv.shape(+fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String, +bad: Bool, +skip: Bool,
  +hm: {B.Rec.malformed(fs) == bad : Bool},
  +h: {L.is_normalized(L.judge.shape(bad, skip, fa, fs, body)) == True{} : Bool}) ->
  {L.line_valid.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs) == True{} : Bool}:
  match bad skip:
    case True{} _:
      Empty.absurd({L.line_valid.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs) == True{} : Bool}, P.false_ne_true(h))
    case False{} True{}:
      Empty.absurd({L.line_valid.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs) == True{} : Bool}, P.false_ne_true(h))
    case False{} False{}:
      nv.contig(fs, body, B.Fasta.find(fa, B.Rec.field(fs, 0n)), hm, h)

law normalized_valid:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +h: {L.is_normalized(L.judge(fa, body)) == True{} : Bool}
  {L.line_valid(fa, body) == True{} : Bool}

def normalized_valid(fa, body, h):
  +fs = B.Rec.fields(body)
  nv.shape(fa, fs, body, B.Rec.malformed(fs), B.Rec.out_of_scope(fs), {==}, h)
