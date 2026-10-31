import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_text.bend as X
import ./proof_run_dec.bend as D
import ./proof_run_rec.bend as C
import ./proof_run_rejudge.bend as J
import ./proof_run_line.bend as N
import ./proof_run_tail.bend as U
import ./proof_run_head.bend as H
import ./proof_run_two.bend as W
import ./tan.bend as Tan
import ./proof_var.bend as PV
import ./proof_s_wna.bend as WN
import ./proof_s_chars.bend as CH
import ./proof_s_cr.bend as CR
import ./proof_s_recs.bend as RS
import ./proof_s_one.bend as OI
import ./proof_b_simdefs.bend as SB

# twice_run under -m: each record run 1 writes is a good line that run 2
# takes as one item (whole, or refused again under -c w) with the same key,
# CHROM and text. A whole line's record keeps its number of ALTs; a split
# line's records have one ALT each, and no LF or CR (the line had none);
# a refused line is written as it came and refused again (the same header
# definitions).

def Bs() -> Data:
  List<&2, B.Base>

def Vs() -> Data:
  List<&2, List<&2, B.Base>>

def not_true(x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(h))
    case False{}:
      {==}

# The text of an item
# ===================

def wt.problem(c: Maybe<&2, B.Code>, +fs: List<&2, String>, +b: String, +seq: Bs(), +v: B.Var, +term: String, +at: B.At, +p: Nat) ->
  {R.Item.text(L.item_of(L.problem(c, fs, b, seq, v), B.Line{b, term}, at, p)) == L.res_text(L.problem(c, fs, b, seq, v)) ++ term : String}:
  match c:
    case Some{+cd}:
      {==}
    case None{}:
      {==}

def wt.bases(+eok: Bool, r: Maybe<&2, Bs()>, a: Maybe<&2, Vs()>, +fs: List<&2, String>, +b: String, +seq: Bs(), +term: String, +at: B.At, +p: Nat) ->
  {R.Item.text(L.item_of(L.judge.bases(eok, r, a, fs, b, seq), B.Line{b, term}, at, p)) == L.res_text(L.judge.bases(eok, r, a, fs, b, seq)) ++ term : String}:
  match r a:
    case Some{+ref} Some{+alts}:
      wt.problem(L.checks(eok, seq, B.Var{B.Rec.pos(fs), ref, alts}), fs, b, seq, B.Var{B.Rec.pos(fs), ref, alts}, term, at, p)
    case None{} _:
      {==}
    case Some{+ref} None{}:
      {==}

def wt.contig(m: Maybe<&2, String>, +fs: List<&2, String>, +b: String, +term: String, +at: B.At, +p: Nat) ->
  {R.Item.text(L.item_of(L.judge.contig(m, fs, b), B.Line{b, term}, at, p)) == L.res_text(L.judge.contig(m, fs, b)) ++ term : String}:
  match m:
    case None{}:
      {==}
    case Some{+raw}:
      +e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n))), 1n)
      wt.bases(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), fs, b, B.Bases.of_fasta(raw), term, at, p)

def wt.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +b: String, +term: String, +at: B.At, +p: Nat) ->
  {R.Item.text(L.item_of(L.judge.shape(bad, skip, fa, fs, b), B.Line{b, term}, at, p)) == L.res_text(L.judge.shape(bad, skip, fa, fs, b)) ++ term : String}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      wt.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, b, term, at, p)

# An item's text is the text judge gives its line, then the terminator.
law item_text:
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  for +n: Nat
  {R.Item.text(L.item(fa, l, n)) == L.written(fa, B.Line.body(l)) ++ B.Line.term(l) : String}

def item_text(fa, l, n):
  match l:
    case B.Line{+b, +term}:
      +fs = B.Rec.fields(b)
      wt.shape(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, fs, b, term, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

# The written text is a good line
# ===============================

# A normalized line: its rebuilt text, with the line's terminator, is a good line.
def nz_good(+fa: List<&2, B.Contig>, +b: String, +term: String, +hg: {X.goodb(B.Line{b, term}) == True{} : Bool},
  +raw: String, +ref: Bs(), +alts: Vs(), w: B.Var,
  +ew: {Tan.normal(B.Bases.of_fasta(raw), N.VV(b, ref, alts)) == w : B.Var},
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool}) ->
  {X.goodb(B.Line{B.Rec.rebuild(N.FS(b), N.VV(b, ref, alts), w), term}) == True{} : Bool}:
  match w:
    case B.Var{+q, +s, +y}:
      +fs = N.FS(b)
      +v = N.VV(b, ref, alts)
      +W2 = {B.Var{q, s, y} : B.Var}
      +info = B.Rec.field(fs, 7n)
      +f3 = B.Rec.field(fs, 3n)
      +mv = B.Rec.moved(v, W2)
      +i2 = N.info2(mv, info, q, s, y)
      +e2 = Nat.sub(Nat.add(q, L.len(s)), 1n)
      +or4 = Bool.or(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
        Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3)))
      +or2F = P.or_false_inv(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n))),
        P.or_false_inv(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))),
          Bool.not(B.Text.is_letters(f3)), P.or_false_inv(or4, B.Text.any_empty(B.Rec.alts(fs)), em)))
      +m1 = P.or_false_inv(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n)), or2F)
      +k = Nat.sub(J.slen(fs), 8n)
      +hl = J.ge8(J.slen(fs), m1)
      +hnlfs = C.pieces_sub_noc(b, '\t', '\n', P.and_true_l(X.no_c(b, '\n'),
        Bool.or(String.eq(term, "\r\n"), Bool.and(String.eq(term, "\n"), Bool.not(String.ends_with(b, "\r")))), hg))
      +hnl = J.fa_noc(fs, q, s, y, i2, '\n', hnlfs, C.digits_noc(Nat.show(q), '\n', D.show_digits(q), {==}), C.show_noc(s, '\n', {==}),
        C.join_noc2(B.Alleles.show(y), ",", '\n', C.shows_noc(y, '\n', {==}), {==}),
        N.inf_noc(mv, info, q, s, y, '\n', C.field_noc(fs, 7n, '\n', hnlfs), C.digits_noc(Nat.show(e2), '\n', D.show_digits(e2), {==}), {==}))
      J.good_re(b, term, fs, q, s, y, i2, k, {==}, hl, hg, hnl, h => N.inf_ecr(mv, info, q, s, y, h))

def wg.problem(c: Maybe<&2, B.Code>, +fa: List<&2, B.Contig>, +b: String, +term: String, +hg: {X.goodb(B.Line{b, term}) == True{} : Bool},
  +raw: String, +ref: Bs(), +alts: Vs(),
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool}) ->
  {X.goodb(B.Line{L.res_text(L.problem(c, N.FS(b), b, B.Bases.of_fasta(raw), N.VV(b, ref, alts))), term}) == True{} : Bool}:
  match c:
    case Some{+cd}:
      hg
    case None{}:
      nz_good(fa, b, term, hg, raw, ref, alts, Tan.normal(B.Bases.of_fasta(raw), N.VV(b, ref, alts)), {==}, em)

def wg.bases(+eok: Bool, r: Maybe<&2, Bs()>, a: Maybe<&2, Vs()>, +fa: List<&2, B.Contig>, +b: String, +term: String,
  +hg: {X.goodb(B.Line{b, term}) == True{} : Bool}, +raw: String,
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool}) ->
  {X.goodb(B.Line{L.res_text(L.judge.bases(eok, r, a, N.FS(b), b, B.Bases.of_fasta(raw))), term}) == True{} : Bool}:
  match r a:
    case Some{+ref} Some{+alts}:
      wg.problem(L.checks(eok, B.Bases.of_fasta(raw), N.VV(b, ref, alts)), fa, b, term, hg, raw, ref, alts, em)
    case None{} _:
      hg
    case Some{+ref} None{}:
      hg

def wg.contig(m: Maybe<&2, String>, +fa: List<&2, B.Contig>, +b: String, +term: String, +hg: {X.goodb(B.Line{b, term}) == True{} : Bool},
  +em: {B.Rec.malformed(N.FS(b)) == False{} : Bool}) ->
  {X.goodb(B.Line{L.res_text(L.judge.contig(m, N.FS(b), b)), term}) == True{} : Bool}:
  match m:
    case None{}:
      hg
    case Some{+raw}:
      +fs = N.FS(b)
      wg.bases(B.Info.end_ok(B.Rec.field(fs, 7n), N.E1(b)), B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), fa, b, term, hg, raw, em)

def wg.shape(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +b: String, +term: String, +hg: {X.goodb(B.Line{b, term}) == True{} : Bool},
  +em: {B.Rec.malformed(N.FS(b)) == bad : Bool}) ->
  {X.goodb(B.Line{L.res_text(L.judge.shape(bad, skip, fa, N.FS(b), b)), term}) == True{} : Bool}:
  match bad skip:
    case True{} _:
      hg
    case False{} True{}:
      hg
    case False{} False{}:
      wg.contig(B.Fasta.find(fa, B.Rec.field(N.FS(b), 0n)), fa, b, term, hg, em)

# The text judge gives a good line, with its terminator, is a good line.
law written_good:
  for +fa: List<&2, B.Contig>
  for +b: String
  for +term: String
  for +hg: {X.goodb(B.Line{b, term}) == True{} : Bool}
  {X.goodb(B.Line{L.written(fa, b), term}) == True{} : Bool}

def written_good(fa, b, term, hg):
  wg.shape(B.Rec.malformed(N.FS(b)), B.Rec.out_of_scope(N.FS(b)), fa, b, term, hg, {==})

# Lines -m leaves whole
# =====================

def gm.go(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +fs: List<&2, String>, +b: String,
  +hgo: {N.go_on(o, L.judge.shape(bad, skip, fa, fs, b)) == True{} : Bool}) -> {bad == False{} : Bool}:
  match bad skip:
    case True{} _:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(hgo))
    case False{} _:
      {==}

# A line whose outcome goes on is not MALFORMED.
law go_mal:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +b: String
  for +hgo: {N.go_on(o, L.judge(fa, b)) == True{} : Bool}
  {B.Rec.malformed(B.Rec.fields(b)) == False{} : Bool}

def go_mal(fa, o, b, hgo):
  +fs = B.Rec.fields(b)
  gm.go(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, o, fs, b, hgo)

def is_whole(p: B.Parts) -> Bool:
  match p:
    case B.Whole{}:
      True{}
    case B.Pieces{ps}:
      False{}
    case B.Unsplit{c}:
      False{}

def nw_cons(g: B.Got, r: B.Parts, +h: {is_whole(r) == False{} : Bool}) -> {is_whole(B.Parts.cons(g, r)) == False{} : Bool}:
  match g r:
    case B.Refuse{+c} _:
      {==}
    case B.Got{+x} B.Pieces{+ps}:
      {==}
    case B.Got{+x} B.Whole{}:
      Empty.absurd({is_whole(B.Parts.cons(B.Got{x}, B.Whole{})) == False{} : Bool}, P.true_ne_false(h))
    case B.Got{+x} B.Unsplit{+c}:
      {==}

law nw_of:
  for +gs: List<&2, B.Got>
  {is_whole(B.Parts.of(gs)) == False{} : Bool}

def nw_of(gs):
  match gs:
    case Nil{}:
      {==}
    case +g <> +t:
      nw_cons(g, B.Parts.of(t), nw_of(t))

def pw.split(ok: Bool, +alts: List<&2, String>, +fs: List<&2, String>, +defs: B.Defs, +over0: Bool) ->
  {is_whole(B.Rec.parts.split(ok, alts, fs, defs, over0)) == False{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      nw_of(B.Rec.pieces.go(alts, fs, defs, over0, List.length(&2, String, alts), 1n))

def pw.cr(cr: Bool, +defs: B.Defs, +over0: Bool, +fs: List<&2, String>) -> {is_whole(B.Rec.parts.cr(cr, defs, over0, fs)) == False{} : Bool}:
  match cr:
    case True{}:
      {==}
    case False{}:
      +alts = B.Rec.alts(fs)
      pw.split(B.Alts.distinct(alts), alts, fs, defs, over0)

def pw.go(g: Bool, +cr: Bool, +defs: B.Defs, +over0: Bool, +fs: List<&2, String>,
  +h: {B.Rec.parts.if(g, cr, defs, over0, fs) == B.Whole{} : B.Parts}) -> {g == False{} : Bool}:
  match g:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.true_ne_false(Equal.trans(Bool, True{}, is_whole(B.Rec.parts.cr(cr, defs, over0, fs)), False{},
        Equal.cong(B.Parts, Bool, z => is_whole(z), B.Whole{}, B.Rec.parts.cr(cr, defs, over0, fs), Equal.sym(B.Parts, B.Rec.parts.cr(cr, defs, over0, fs), B.Whole{}, h)),
        pw.cr(cr, defs, over0, fs))))

def ws.sp(sp: Bool, +defs: B.Defs, +o0: Bool, +b: String, +w: String,
  +hb: {Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(B.Rec.fields(b)))), Nat.is_le(2n, L.n_alts(b))) == False{} : Bool},
  +hmal: {B.Rec.malformed(B.Rec.fields(b)) == False{} : Bool},
  +hn: {L.n_alts(w) == L.n_alts(b) : Nat}) ->
  {B.Rec.parts.if(Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(B.Rec.fields(w)))), Nat.is_le(2n, L.n_alts(w))), B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}:
  match sp:
    case False{}:
      {==}
    case True{}:
      +nm = Bool.not(B.Rec.malformed(B.Rec.fields(w)))
      +hle = {(%hmal : {Bool.and(Bool.not(_), Nat.is_le(2n, L.n_alts(b))) == False{} : Bool}; hb) : {Nat.is_le(2n, L.n_alts(b)) == False{} : Bool}}
      %Equal.sym(Nat, L.n_alts(w), L.n_alts(b), hn) : {B.Rec.parts.if(Bool.and(nm, Nat.is_le(2n, _)), B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Nat.is_le(2n, L.n_alts(b)), False{}, hle) : {B.Rec.parts.if(Bool.and(nm, _), B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Bool.and(nm, False{}), False{}, P.and_false_r(nm)) : {B.Rec.parts.if(_, B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      {==}

# A text with a whole line's number of ALTs (the line not MALFORMED) is whole too.
law whole_stays:
  for +defs: B.Defs
  for +o: B.Opts
  for +b: String
  for +w: String
  for +hpt: {B.Rec.parts(defs, o, b) == B.Whole{} : B.Parts}
  for +hmal: {B.Rec.malformed(B.Rec.fields(b)) == False{} : Bool}
  for +hn: {L.n_alts(w) == L.n_alts(b) : Nat}
  {B.Rec.parts(defs, o, w) == B.Whole{} : B.Parts}

def whole_stays(defs, o, b, w, hpt, hmal, hn):
  match o:
    case B.Opts{+s, +wd, +sp, +o0, +a}:
      +fs = B.Rec.fields(b)
      ws.sp(sp, defs, o0, b, w, pw.go(Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, L.n_alts(b))), B.Text.has_cr(b), defs, o0, fs, hpt), hmal, hn)

def lt2(n: Nat, +h: {Nat.is_lt(n, 2n) == True{} : Bool}) -> {Nat.is_le(2n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.is_le(2n, 2n+q) == False{} : Bool}, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, P.lt_zero(q)), h)))

# A text with one ALT is whole.
law one_whole:
  for +defs: B.Defs
  for +o: B.Opts
  for +p: String
  for +w: String
  for +h1: {Nat.is_lt(L.n_alts(p), 2n) == True{} : Bool}
  for +hn: {L.n_alts(w) == L.n_alts(p) : Nat}
  {B.Rec.parts(defs, o, w) == B.Whole{} : B.Parts}

def one_whole(defs, o, p, w, h1, hn):
  match o:
    case B.Opts{+s, +wd, +sp, +o0, +a}:
      +g = Bool.and(sp, Bool.not(B.Rec.malformed(B.Rec.fields(w))))
      %Equal.sym(Nat, L.n_alts(w), L.n_alts(p), hn) : {B.Rec.parts.if(Bool.and(g, Nat.is_le(2n, _)), B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Nat.is_le(2n, L.n_alts(p)), False{}, lt2(L.n_alts(p), h1)) : {B.Rec.parts.if(Bool.and(g, _), B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Bool.and(g, False{}), False{}, P.and_false_r(g)) : {B.Rec.parts.if(_, B.Text.has_cr(w), defs, o0, B.Rec.fields(w)) == B.Whole{} : B.Parts}
      {==}

# Characters
# ==========

law allc_noc:
  for +s: String
  for +d: Char
  for +h: {X.no_c(s, d) == True{} : Bool}
  {CH.ALLC(CH.NoC{d}, s) == True{} : Bool}

def allc_noc(s, d, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      S.and_intro(Bool.not(Char.is_eq(c, d)), CH.ALLC(CH.NoC{d}, t), P.and_true_l(Bool.not(Char.is_eq(c, d)), X.no_c(t, d), h),
        allc_noc(t, d, P.and_true_r(Bool.not(Char.is_eq(c, d)), X.no_c(t, d), h)))

law noc_allc:
  for +s: String
  for +d: Char
  for +h: {CH.ALLC(CH.NoC{d}, s) == True{} : Bool}
  {X.no_c(s, d) == True{} : Bool}

def noc_allc(s, d, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      S.and_intro(Bool.not(Char.is_eq(c, d)), X.no_c(t, d), P.and_true_l(Bool.not(Char.is_eq(c, d)), CH.ALLC(CH.NoC{d}, t), h),
        noc_allc(t, d, P.and_true_r(Bool.not(Char.is_eq(c, d)), CH.ALLC(CH.NoC{d}, t), h)))

law cr_allc:
  for +s: String
  for +h: {B.Text.has_cr(s) == False{} : Bool}
  {CH.ALLC(CH.NoC{'\r'}, s) == True{} : Bool}

def cr_allc(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h1 = P.or_false_inv(Char.is_eq(c, '\r'), B.Text.has_cr(t), h)
      +h2 = C.or_inv_r(Char.is_eq(c, '\r'), B.Text.has_cr(t), h)
      %Equal.sym(Bool, Char.is_eq(c, '\r'), False{}, h1) : {Bool.and(Bool.not(_), CH.ALLC(CH.NoC{'\r'}, t)) == True{} : Bool}
      cr_allc(t, h2)

def ae.go(+c: Char, t: String, +hc: {Char.is_eq(c, '\r') == False{} : Bool}, ih: {C.ecr(t) == False{} : Bool}) -> {C.ecr(SCon{c, t}) == False{} : Bool}:
  match t:
    case SNil{}:
      C.ecr_one(c, hc)
    case SCon{+x, +t2}:
      Equal.trans(Bool, C.ecr(SCon{c, SCon{x, t2}}), C.ecr(SCon{x, t2}), False{}, C.ecr_app(SCon{c, SNil{}}, x, t2), ih)

# A text without CR does not end with CR.
law allc_ecr:
  for +s: String
  for +h: {CH.ALLC(CH.NoC{'\r'}, s) == True{} : Bool}
  {C.ecr(s) == False{} : Bool}

def allc_ecr(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hc = not_true(Char.is_eq(c, '\r'), P.and_true_l(Bool.not(Char.is_eq(c, '\r')), CH.ALLC(CH.NoC{'\r'}, t), h))
      ae.go(c, t, hc, allc_ecr(t, P.and_true_r(Bool.not(Char.is_eq(c, '\r')), CH.ALLC(CH.NoC{'\r'}, t), h)))

def tc(x: Bool, +y: Bool, +z: Bool, +h: {Bool.or(x, Bool.and(y, z)) == True{} : Bool}) -> {Bool.or(x, Bool.and(y, True{})) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, y, True{}, P.and_true_l(y, z, h)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

# A record of a good line, without LF or CR, is a good line with its terminator.
law good_rec:
  for +l: B.Line
  for +p: String
  for +hg: {X.goodb(l) == True{} : Bool}
  for +hn: {X.no_c(p, '\n') == True{} : Bool}
  for +hr: {CH.ALLC(CH.NoC{'\r'}, p) == True{} : Bool}
  {X.goodb(B.Line{p, B.Line.term(l)}) == True{} : Bool}

def good_rec(l, p, hg, hn, hr):
  match l:
    case B.Line{+b, +term}:
      +x = String.eq(term, "\r\n")
      +y = String.eq(term, "\n")
      +hz = tc(x, y, Bool.not(String.ends_with(b, "\r")), P.and_true_r(X.no_c(b, '\n'), Bool.or(x, Bool.and(y, Bool.not(String.ends_with(b, "\r")))), hg))
      %Equal.sym(Bool, String.ends_with(p, "\r"), False{}, allc_ecr(p, hr)) : {Bool.and(X.no_c(p, '\n'), Bool.or(x, Bool.and(y, Bool.not(_)))) == True{} : Bool}
      S.and_intro(X.no_c(p, '\n'), Bool.or(x, Bool.and(y, True{})), hn, hz)

law good_noc:
  for +l: B.Line
  for +hg: {X.goodb(l) == True{} : Bool}
  {X.no_c(B.Line.body(l), '\n') == True{} : Bool}

def good_noc(l, hg):
  match l:
    case B.Line{+b, +term}:
      P.and_true_l(X.no_c(b, '\n'), Bool.or(String.eq(term, "\r\n"), Bool.and(String.eq(term, "\n"), Bool.not(String.ends_with(b, "\r")))), hg)

# What run 2 needs of a record
# ============================

def qm(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +y: R.Item) -> Bool:
  +l2 = N.ln(R.Item.text(y))
  X.goodb(l2) && String.eq(B.Line.text(l2), R.Item.text(y)) && W.m1(fa, defs, o, l2) && N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y)

law qm_of:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +y: R.Item
  for +l2: B.Line
  for +hl: {N.ln(R.Item.text(y)) == l2 : B.Line}
  for +hg: {X.goodb(l2) == True{} : Bool}
  for +ht: {B.Line.text(l2) == R.Item.text(y) : String}
  for +hm: {W.m1(fa, defs, o, l2) == True{} : Bool}
  for +hs: {N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y) == True{} : Bool}
  {qm(fa, defs, o, y) == True{} : Bool}

def qm_of(fa, defs, o, y, l2, hl, hg, ht, hm, hs):
  %Equal.sym(B.Line, N.ln(R.Item.text(y)), l2, hl) :
    {Bool.and(Bool.and(Bool.and(X.goodb(_), String.eq(B.Line.text(_), R.Item.text(y))), W.m1(fa, defs, o, _)),
      N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(_)), fa, _, 0n), y)) == True{} : Bool}
  +he = {(%ht : {String.eq(B.Line.text(l2), _) == True{} : Bool}; Q.str_eq_refl(B.Line.text(l2))) : {String.eq(B.Line.text(l2), R.Item.text(y)) == True{} : Bool}}
  +ge = Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)))
  S.and_intro(Bool.and(ge, W.m1(fa, defs, o, l2)), N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y),
    S.and_intro(ge, W.m1(fa, defs, o, l2), S.and_intro(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)), hg, he), hm), hs)

# A line whose outcome goes on, and whose written text -m leaves whole.
law qm_one:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +l: B.Line
  for +n: Nat
  for +hg: {X.goodb(l) == True{} : Bool}
  for +hgo: {N.go_on(o, L.judge(fa, B.Line.body(l))) == True{} : Bool}
  for +hw: {B.Rec.parts(defs, o, L.written(fa, B.Line.body(l))) == B.Whole{} : B.Parts}
  {qm(fa, defs, o, L.item(fa, l, n)) == True{} : Bool}

def qm_one(fa, defs, o, l, n, hg, hgo, hw):
  match l:
    case B.Line{+b, +term}:
      +y = L.item(fa, B.Line{b, term}, n)
      +w = L.written(fa, b)
      +lw = {B.Line{w, term} : B.Line}
      +hq = N.line_qi(fa, o, B.Line{b, term}, n, hg, hgo)
      +et = item_text(fa, B.Line{b, term}, n)
      +gw = written_good(fa, b, term, hg)
      +el = {(%Equal.sym(String, R.Item.text(y), w ++ term, et) : {N.ln(_) == lw : B.Line}; N.ln_good(lw, gw)) : {N.ln(R.Item.text(y)) == lw : B.Line}}
      +l2 = N.ln(R.Item.text(y))
      +G2 = X.goodb(l2)
      +E2 = String.eq(B.Line.text(l2), R.Item.text(y))
      +GO2 = N.go_on(o, L.judge(fa, B.Line.body(l2)))
      +SI2 = N.simb(L.item(fa, l2, 0n), y)
      +q4 = P.and_true_l(Bool.and(Bool.and(G2, E2), GO2), SI2, hq)
      +go2 = P.and_true_r(Bool.and(G2, E2), GO2, q4)
      +si2 = P.and_true_r(Bool.and(Bool.and(G2, E2), GO2), SI2, hq)
      +gow = {(%el : {N.go_on(o, L.judge(fa, B.Line.body(_))) == True{} : Bool}; go2) : {N.go_on(o, L.judge(fa, w)) == True{} : Bool}}
      +siw = {(%el : {N.simb(L.item(fa, _, 0n), y) == True{} : Bool}; si2) : {N.simb(L.item(fa, lw, 0n), y) == True{} : Bool}}
      +hm = {(%Equal.sym(B.Parts, B.Rec.parts(defs, o, w), B.Whole{}, hw) : {W.m1.go(_, fa, o, lw) == True{} : Bool}; gow) : {W.m1(fa, defs, o, lw) == True{} : Bool}}
      +hs = {(%Equal.sym(B.Parts, B.Rec.parts(defs, o, w), B.Whole{}, hw) : {N.simb(W.it1(_, fa, lw, 0n), y) == True{} : Bool}; siw) :
        {N.simb(W.it1(B.Rec.parts(defs, o, w), fa, lw, 0n), y) == True{} : Bool}}
      qm_of(fa, defs, o, y, lw, el, gw, Equal.sym(String, R.Item.text(y), w ++ term, et), hm, hs)

# A line -m refuses, which goes on: written as it came.
law qm_un:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +l: B.Line
  for +n: Nat
  for +c: B.Code
  for +hg: {X.goodb(l) == True{} : Bool}
  for +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == B.Unsplit{c} : B.Parts}
  for +hq: {Bool.and(N.go_on(o, L.judge(fa, B.Line.body(l))), Bool.not(R.Opts.strict(o))) == True{} : Bool}
  {qm(fa, defs, o, W.it1(B.Unsplit{c}, fa, l, n)) == True{} : Bool}

def qm_un(fa, defs, o, l, n, c, hg, hpt, hq):
  +fs = B.Rec.fields(B.Line.body(l))
  +y = W.it1(B.Unsplit{c}, fa, l, n)
  +hm = {(%Equal.sym(B.Parts, B.Rec.parts(defs, o, B.Line.body(l)), B.Unsplit{c}, hpt) : {W.m1.go(_, fa, o, l) == True{} : Bool}; hq) : {W.m1(fa, defs, o, l) == True{} : Bool}}
  +hs = {(%Equal.sym(B.Parts, B.Rec.parts(defs, o, B.Line.body(l)), B.Unsplit{c}, hpt) : {N.simb(W.it1(_, fa, l, 0n), y) == True{} : Bool};
      N.simb_refl(B.Rec.pos(fs), B.Rec.pos(fs), B.Rec.pos(fs), 0n, n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.field(fs, 1n), B.Line.text(l))) :
    {N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 0n), y) == True{} : Bool}}
  qm_of(fa, defs, o, y, l, N.ln_good(l, hg), hg, {==}, hm, hs)

def allqm(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      qm(fa, defs, o, x) && allqm(fa, defs, o, t)

law allqm_app:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h1: {allqm(fa, defs, o, xs) == True{} : Bool}
  for +h2: {allqm(fa, defs, o, ys) == True{} : Bool}
  {allqm(fa, defs, o, S.app(xs, ys)) == True{} : Bool}

def allqm_app(fa, defs, o, xs, ys, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      S.and_intro(qm(fa, defs, o, x), allqm(fa, defs, o, S.app(t, ys)), P.and_true_l(qm(fa, defs, o, x), allqm(fa, defs, o, t), h1),
        allqm_app(fa, defs, o, t, ys, P.and_true_r(qm(fa, defs, o, x), allqm(fa, defs, o, t), h1), h2))

# The records of a split line.
law qm_ps:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +l: B.Line
  for +n: Nat
  for +hg: {X.goodb(l) == True{} : Bool}
  for +hn: {CH.ALLS(CH.NoC{'\n'}, ps) == True{} : Bool}
  for +hr: {CH.ALLS(CH.NoC{'\r'}, ps) == True{} : Bool}
  for +h1: {SB.all_one(RS.LS(ps, B.Line.term(l))) == True{} : Bool}
  for +hp: {H.pgo(ps, fa, o) == True{} : Bool}
  {allqm(fa, defs, o, L.items.pieces(ps, fa, B.Line.term(l), n)) == True{} : Bool}

def qm_ps(ps, fa, defs, o, l, n, hg, hn, hr, h1, hp):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      +term = B.Line.term(l)
      +lp = {B.Line{p, term} : B.Line}
      +hn1 = P.and_true_l(CH.ALLC(CH.NoC{'\n'}, p), CH.ALLS(CH.NoC{'\n'}, t), hn)
      +hr1 = P.and_true_l(CH.ALLC(CH.NoC{'\r'}, p), CH.ALLS(CH.NoC{'\r'}, t), hr)
      +ho = P.and_true_l(SB.one_alt(lp), SB.all_one(RS.LS(t, term)), h1)
      +hgp = P.and_true_l(N.go_on(o, L.judge(fa, p)), H.pgo(t, fa, o), hp)
      +q1 = qm_one(fa, defs, o, lp, n, good_rec(l, p, hg, noc_allc(p, '\n', hn1), hr1), hgp,
        one_whole(defs, o, p, L.written(fa, p), ho, WN.written_nalts(fa, p)))
      S.and_intro(qm(fa, defs, o, L.item(fa, lp, n)), allqm(fa, defs, o, L.items.pieces(t, fa, term, n)), q1,
        qm_ps(t, fa, defs, o, l, n, hg,
          P.and_true_r(CH.ALLC(CH.NoC{'\n'}, p), CH.ALLS(CH.NoC{'\n'}, t), hn),
          P.and_true_r(CH.ALLC(CH.NoC{'\r'}, p), CH.ALLS(CH.NoC{'\r'}, t), hr),
          P.and_true_r(SB.one_alt(lp), SB.all_one(RS.LS(t, term)), h1),
          P.and_true_r(N.go_on(o, L.judge(fa, p)), H.pgo(t, fa, o), hp)))

def lq.go(pt: B.Parts, +l: B.Line, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat,
  +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts},
  +hg: {X.goodb(l) == True{} : Bool},
  +hl: {H.lgo.go(pt, fa, o, l) == True{} : Bool}) ->
  {allqm(fa, defs, o, L.items.line(pt, fa, l, n)) == True{} : Bool}:
  match pt:
    case B.Whole{}:
      +b = B.Line.body(l)
      +hw = whole_stays(defs, o, b, L.written(fa, b), hpt, go_mal(fa, o, b, hl), WN.written_nalts(fa, b))
      S.and_intro(qm(fa, defs, o, L.item(fa, l, n)), True{}, qm_one(fa, defs, o, l, n, hg, hl, hw), {==})
    case B.Pieces{+ps}:
      +b = B.Line.body(l)
      +hb = allc_noc(b, '\n', good_noc(l, hg))
      +hn = CH.parts_chars(CH.NoC{'\n'}, defs, o, b, ps, hpt, hb, {==}, {==})
      +hr = CH.parts_chars(CH.NoC{'\r'}, defs, o, b, ps, hpt, cr_allc(b, CR.cr_none(defs, o, b, ps, hpt)), {==}, {==})
      qm_ps(ps, fa, defs, o, l, n, hg, hn, hr, OI.pieces_one(defs, o, b, ps, B.Line.term(l), hpt), hl)
    case B.Unsplit{+c}:
      S.and_intro(qm(fa, defs, o, W.it1(B.Unsplit{c}, fa, l, n)), True{}, qm_un(fa, defs, o, l, n, c, hg, hpt, hl), {==})

# Every record run 1 writes, from good lines that let it go on.
law allqm_lines:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +hg: {X.all_good(ls) == True{} : Bool}
  for +hl: {H.all_lgo(ls, fa, defs, o) == True{} : Bool}
  {allqm(fa, defs, o, U.mitems(ls, fa, defs, o, n)) == True{} : Bool}

def allqm_lines(ls, fa, defs, o, n, hg, hl):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      +pt = B.Rec.parts(defs, o, B.Line.body(l))
      %Equal.sym(List<&2, R.Item>, U.mitems(l <> t, fa, defs, o, n), S.app(L.items.line(pt, fa, l, 1n+n), U.mitems(t, fa, defs, o, 1n+n)), U.mitems_cons(l, t, fa, defs, o, n)) : {allqm(fa, defs, o, _) == True{} : Bool}
      allqm_app(fa, defs, o, L.items.line(pt, fa, l, 1n+n), U.mitems(t, fa, defs, o, 1n+n),
        lq.go(pt, l, fa, defs, o, 1n+n, {==}, P.and_true_l(X.goodb(l), X.all_good(t), hg), P.and_true_l(H.lgo(fa, defs, o, l), H.all_lgo(t, fa, defs, o), hl)),
        allqm_lines(t, fa, defs, o, 1n+n, P.and_true_r(X.goodb(l), X.all_good(t), hg), P.and_true_r(H.lgo(fa, defs, o, l), H.all_lgo(t, fa, defs, o), hl)))

# Sorting keeps the property
# ==========================

def allqm_ins.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +x: R.Item, +y: R.Item, +t: List<&2, R.Item>, b: Bool,
  +hx: {qm(fa, defs, o, x) == True{} : Bool}, +hy: {qm(fa, defs, o, y) == True{} : Bool}, +ht: {allqm(fa, defs, o, t) == True{} : Bool},
  ih: {allqm(fa, defs, o, L.ins_first(x, t)) == True{} : Bool}) ->
  {allqm(fa, defs, o, L.ins_first.put(b, x, y, t, L.ins_first(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      S.and_intro(qm(fa, defs, o, x), allqm(fa, defs, o, y <> t), hx, S.and_intro(qm(fa, defs, o, y), allqm(fa, defs, o, t), hy, ht))
    case False{}:
      S.and_intro(qm(fa, defs, o, y), allqm(fa, defs, o, L.ins_first(x, t)), hy, ih)

law allqm_ins:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +x: R.Item
  for +ys: List<&2, R.Item>
  for +hx: {qm(fa, defs, o, x) == True{} : Bool}
  for +hy: {allqm(fa, defs, o, ys) == True{} : Bool}
  {allqm(fa, defs, o, L.ins_first(x, ys)) == True{} : Bool}

def allqm_ins(fa, defs, o, x, ys, hx, hy):
  match ys:
    case Nil{}:
      S.and_intro(qm(fa, defs, o, x), True{}, hx, {==})
    case +y <> +t:
      +h1 = P.and_true_l(qm(fa, defs, o, y), allqm(fa, defs, o, t), hy)
      +h2 = P.and_true_r(qm(fa, defs, o, y), allqm(fa, defs, o, t), hy)
      allqm_ins.go(fa, defs, o, x, y, t, Nat.is_le(R.Item.key(x), R.Item.key(y)), hx, h1, h2, allqm_ins(fa, defs, o, x, t, hx, h2))

law allqm_isort:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +h: {allqm(fa, defs, o, xs) == True{} : Bool}
  {allqm(fa, defs, o, L.isort(xs)) == True{} : Bool}

def allqm_isort(fa, defs, o, xs, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      allqm_ins(fa, defs, o, x, L.isort(t), P.and_true_l(qm(fa, defs, o, x), allqm(fa, defs, o, t), h),
        allqm_isort(fa, defs, o, t, P.and_true_r(qm(fa, defs, o, x), allqm(fa, defs, o, t), h)))

def allqm_gs.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +x: R.Item, +t: List<&2, R.Item>, +run: List<&2, R.Item>, +done: List<&2, R.Item>, b: Bool,
  +hx: {qm(fa, defs, o, x) == True{} : Bool}, +hr: {allqm(fa, defs, o, run) == True{} : Bool}, +hd: {allqm(fa, defs, o, done) == True{} : Bool},
  ih: @r2: List<&2, R.Item> -> @d2: List<&2, R.Item> -> {allqm(fa, defs, o, r2) == True{} : Bool} -> {allqm(fa, defs, o, d2) == True{} : Bool} ->
    {allqm(fa, defs, o, L.gsort.go(t, r2, d2)) == True{} : Bool}) ->
  {allqm(fa, defs, o, L.gsort.go(t, Bool.pick(List<&2, R.Item>, b, S.app(run, [x]), [x]), Bool.pick(List<&2, R.Item>, b, done, S.app(done, L.isort(run))))) == True{} : Bool}:
  match b:
    case True{}:
      ih(S.app(run, [x]), done, allqm_app(fa, defs, o, run, [x], hr, S.and_intro(qm(fa, defs, o, x), True{}, hx, {==})), hd)
    case False{}:
      ih([x], S.app(done, L.isort(run)), S.and_intro(qm(fa, defs, o, x), True{}, hx, {==}), allqm_app(fa, defs, o, done, L.isort(run), hd, allqm_isort(fa, defs, o, run, hr)))

law allqm_gs:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +run: List<&2, R.Item>
  for +done: List<&2, R.Item>
  for +hx: {allqm(fa, defs, o, xs) == True{} : Bool}
  for +hr: {allqm(fa, defs, o, run) == True{} : Bool}
  for +hd: {allqm(fa, defs, o, done) == True{} : Bool}
  {allqm(fa, defs, o, L.gsort.go(xs, run, done)) == True{} : Bool}

def allqm_gs(fa, defs, o, xs, run, done, hx, hr, hd):
  match xs:
    case Nil{}:
      allqm_app(fa, defs, o, done, L.isort(run), hd, allqm_isort(fa, defs, o, run, hr))
    case +x <> +t:
      allqm_gs.go(fa, defs, o, x, t, run, done, L.same_chrom(run, R.Item.chrom(x)), P.and_true_l(qm(fa, defs, o, x), allqm(fa, defs, o, t), hx), hr, hd,
        r2 => d2 => h2 => h3 => allqm_gs(fa, defs, o, t, r2, d2, P.and_true_r(qm(fa, defs, o, x), allqm(fa, defs, o, t), hx), h2, h3))


# Run 2 reads the records back
# ============================

# The lines run 1 writes for its items.
def lns(ys: List<&2, R.Item>) -> List<&2, B.Line>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      N.ln(R.Item.text(y)) <> lns(t)

def QM4(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +y: R.Item) -> Bool:
  +l2 = N.ln(R.Item.text(y))
  X.goodb(l2) && String.eq(B.Line.text(l2), R.Item.text(y)) && W.m1(fa, defs, o, l2)

law qm_good:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +y: R.Item
  for +h: {qm(fa, defs, o, y) == True{} : Bool}
  {X.goodb(N.ln(R.Item.text(y))) == True{} : Bool}

def qm_good(fa, defs, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  +h3 = P.and_true_l(QM4(fa, defs, o, y), N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y), h)
  +h2 = P.and_true_l(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), W.m1(fa, defs, o, l2), h3)
  P.and_true_l(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)), h2)

law qm_text:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +y: R.Item
  for +h: {qm(fa, defs, o, y) == True{} : Bool}
  {B.Line.text(N.ln(R.Item.text(y))) == R.Item.text(y) : String}

def qm_text(fa, defs, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  +h3 = P.and_true_l(QM4(fa, defs, o, y), N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y), h)
  +h2 = P.and_true_l(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), W.m1(fa, defs, o, l2), h3)
  Q.str_eq_sound(B.Line.text(l2), R.Item.text(y), P.and_true_r(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)), h2))

law qm_m1:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +y: R.Item
  for +h: {qm(fa, defs, o, y) == True{} : Bool}
  {W.m1(fa, defs, o, N.ln(R.Item.text(y))) == True{} : Bool}

def qm_m1(fa, defs, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  +h3 = P.and_true_l(QM4(fa, defs, o, y), N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y), h)
  P.and_true_r(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), W.m1(fa, defs, o, l2), h3)

law qm_sim:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +y: R.Item
  for +h: {qm(fa, defs, o, y) == True{} : Bool}
  {N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(N.ln(R.Item.text(y)))), fa, N.ln(R.Item.text(y)), 0n), y) == True{} : Bool}

def qm_sim(fa, defs, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  P.and_true_r(QM4(fa, defs, o, y), N.simb(W.it1(B.Rec.parts(defs, o, B.Line.body(l2)), fa, l2, 0n), y), h)

law lnsm_good:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {allqm(fa, defs, o, ys) == True{} : Bool}
  {X.all_good(lns(ys)) == True{} : Bool}

def lnsm_good(fa, defs, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      S.and_intro(X.goodb(N.ln(R.Item.text(y))), X.all_good(lns(t)), qm_good(fa, defs, o, y, P.and_true_l(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)),
        lnsm_good(fa, defs, o, t, P.and_true_r(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)))

law lnsm_m1:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {allqm(fa, defs, o, ys) == True{} : Bool}
  {W.all_m1(lns(ys), fa, defs, o) == True{} : Bool}

def lnsm_m1(fa, defs, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      S.and_intro(W.m1(fa, defs, o, N.ln(R.Item.text(y))), W.all_m1(lns(t), fa, defs, o), qm_m1(fa, defs, o, y, P.and_true_l(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)),
        lnsm_m1(fa, defs, o, t, P.and_true_r(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)))

law lnsm_text:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {allqm(fa, defs, o, ys) == True{} : Bool}
  {B.Lines.text(lns(ys)) == L.texts(ys) : String}

def lnsm_text(fa, defs, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(String, B.Line.text(N.ln(R.Item.text(y))), R.Item.text(y), qm_text(fa, defs, o, y, P.and_true_l(qm(fa, defs, o, y), allqm(fa, defs, o, t), h))) :
        {_ ++ B.Lines.text(lns(t)) == R.Item.text(y) ++ L.texts(t) : String}
      %Equal.sym(String, B.Lines.text(lns(t)), L.texts(t), lnsm_text(fa, defs, o, t, P.and_true_r(qm(fa, defs, o, y), allqm(fa, defs, o, t), h))) :
        {R.Item.text(y) ++ _ == R.Item.text(y) ++ L.texts(t) : String}
      {==}

# Same key, CHROM and text, item by item.
def allsim(xs: List<&2, R.Item>, ys: List<&2, R.Item>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> t y <> u:
      N.simb(x, y) && allsim(t, u)
    case _ _:
      False{}

def sn.go(r: B.Res, l2: B.Line, +f0: String, +f1: String, +p: Nat, +n: Nat, y: R.Item,
  h: {N.simb(L.item_of(r, l2, B.At{0n, f0, f1}, p), y) == True{} : Bool}) ->
  {N.simb(L.item_of(r, l2, B.At{n, f0, f1}, p), y) == True{} : Bool}:
  match r l2 y:
    case B.Res{B.Normalized{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Broken{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Skipped{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.NoContig{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Problem{c}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h

def su.go(+k: Nat, +p: Nat, +n: Nat, +c: String, +q: String, +t: String, y: R.Item,
  h: {N.simb(R.Item{k, p, B.At{0n, c, q}, t}, y) == True{} : Bool}) ->
  {N.simb(R.Item{k, p, B.At{n, c, q}, t}, y) == True{} : Bool}:
  match y:
    case R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h

def ms.go(pt: B.Parts, +l2: B.Line, +fa: List<&2, B.Contig>, +o: B.Opts, +m: Nat, +y: R.Item, +t: List<&2, R.Item>, +rest: List<&2, R.Item>,
  +hm: {W.m1.go(pt, fa, o, l2) == True{} : Bool},
  +hs: {N.simb(W.it1(pt, fa, l2, 0n), y) == True{} : Bool},
  +ih: {allsim(rest, t) == True{} : Bool}) ->
  {allsim(S.app(L.items.line(pt, fa, l2, m), rest), y <> t) == True{} : Bool}:
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l2))
      S.and_intro(N.simb(L.item(fa, l2, m), y), allsim(rest, t),
        sn.go(L.judge(fa, B.Line.body(l2)), l2, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.pos(fs), m, y, hs), ih)
    case B.Pieces{+ps}:
      Empty.absurd({allsim(S.app(L.items.line(B.Pieces{ps}, fa, l2, m), rest), y <> t) == True{} : Bool}, P.false_ne_true(hm))
    case B.Unsplit{+c}:
      +fs = B.Rec.fields(B.Line.body(l2))
      +it = W.it1(B.Unsplit{c}, fa, l2, m)
      S.and_intro(N.simb(it, y), allsim(rest, t),
        su.go(B.Rec.pos(fs), B.Rec.pos(fs), m, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Line.text(l2), y, hs), ih)

# Run 2's records are run 1's, item by item.
law mitems_sim:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +n: Nat
  for +h: {allqm(fa, defs, o, ys) == True{} : Bool}
  {allsim(U.mitems(lns(ys), fa, defs, o, n), ys) == True{} : Bool}

def mitems_sim(fa, defs, o, ys, n, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +l2 = N.ln(R.Item.text(y))
      +pt = B.Rec.parts(defs, o, B.Line.body(l2))
      +hy = P.and_true_l(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)
      +ht = P.and_true_r(qm(fa, defs, o, y), allqm(fa, defs, o, t), h)
      +rest = U.mitems(lns(t), fa, defs, o, 1n+n)
      %Equal.sym(List<&2, R.Item>, U.mitems(l2 <> lns(t), fa, defs, o, n), S.app(L.items.line(pt, fa, l2, 1n+n), rest), U.mitems_cons(l2, lns(t), fa, defs, o, n)) :
        {allsim(_, y <> t) == True{} : Bool}
      ms.go(pt, l2, fa, o, 1n+n, y, t, rest, qm_m1(fa, defs, o, y, hy), qm_sim(fa, defs, o, y, hy), mitems_sim(fa, defs, o, t, 1n+n, ht))
