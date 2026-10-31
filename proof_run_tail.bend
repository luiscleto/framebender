import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_s_when.bend as W

# What the run laws need about -m: the rest of a run from inside a split line
# (its records left, then the lines left), the items of the run's records
# (L.out_items), a record's item as the run keys it, and that a line -m
# cannot split never stops the run with UNSORTED. Every variable is reusable.

# The rest of a run
# =================

# The records ps left of a split line (with the line's terminator, place and
# input POS), then the lines t.
def TR(+ps: List<&2, String>, +term: String, +at: B.At, +inpos: Nat, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  L.run.go(t, fa, defs, o, L.pieces_in(ps, fa, o, st, term, at, inpos))

law pieces_halted:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +term: String
  for +at: B.At
  for +inpos: Nat
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {L.pieces_in(ps, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}, term, at, inpos) == R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}} : R.RunSt}

def pieces_halted(ps, fa, o, term, at, inpos, n, i, h, c, e, l, b, k, out, ns):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      pieces_halted(t, fa, o, term, at, inpos, n, i, h, c, e, l, b, k, out, ns)

# A stopped run, from inside a split line: exit code 1, the messages so far.
law tr_halted:
  for +ps: List<&2, String>
  for +term: String
  for +at: B.At
  for +inpos: Nat
  for +t: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.finish(TR(ps, term, at, inpos, t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})) == R.Report{out, ns, 1n} : R.Report}

def tr_halted(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.RunSt, L.pieces_in(ps, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}, term, at, inpos), R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}},
    pieces_halted(ps, fa, o, term, at, inpos, n, i, h, c, e, l, b, k, out, ns)) :
    {R.finish(L.run.go(t, fa, defs, o, _)) == R.Report{out, ns, 1n} : R.Report}
  T.halted(t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)

law tr_code:
  for +ps: List<&2, String>
  for +term: String
  for +at: B.At
  for +inpos: Nat
  for +t: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.Report.code(R.finish(TR(ps, term, at, inpos, t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == 1n : Nat}

def tr_code(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.Report, R.finish(TR(ps, term, at, inpos, t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})), R.Report{out, ns, 1n},
    tr_halted(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {R.Report.code(_) == 1n : Nat}
  {==}

law tr_notes:
  for +ps: List<&2, String>
  for +term: String
  for +at: B.At
  for +inpos: Nat
  for +t: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.Report.notes(R.finish(TR(ps, term, at, inpos, t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == ns : List<&2, B.Note>}

def tr_notes(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.Report, R.finish(TR(ps, term, at, inpos, t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})), R.Report{out, ns, 1n},
    tr_halted(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {R.Report.notes(_) == ns : List<&2, B.Note>}
  {==}

# The items
# =========

# The items of the run's records from the lines ls on, line numbers after n.
def mitems(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, n: Nat) -> List<&2, R.Item>:
  L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{True{}, n, Nil{}}))

law macc_split:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +i: Bool
  for +n: Nat
  for +a: List<&2, R.Item>
  {L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{i, n, a})) == S.app(a, L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{i, n, Nil{}}))) : List<&2, R.Item>}

def macc_split(ls, fa, defs, o, i, n, a):
  match ls:
    case Nil{}:
      Equal.sym(List<&2, R.Item>, S.app(a, Nil{}), a, P.append_nil(R.Item, a))
    case +l <> +t:
      match i:
        case False{}:
          macc_split(t, fa, defs, o, R.is_chrom_line(B.Line.body(l)), 1n+n, a)
        case True{}:
          +x = L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n)
          +rest = L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{True{}, 1n+n, Nil{}}))
          %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{True{}, 1n+n, S.app(a, x)})), S.app(S.app(a, x), rest),
            macc_split(t, fa, defs, o, True{}, 1n+n, S.app(a, x))) : {_ == S.app(a, L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{True{}, 1n+n, x}))) : List<&2, R.Item>}
          %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{True{}, 1n+n, x})), S.app(x, rest),
            macc_split(t, fa, defs, o, True{}, 1n+n, x)) : {S.app(S.app(a, x), rest) == S.app(a, _) : List<&2, R.Item>}
          P.append_assoc(R.Item, a, x, rest)

law mitems_cons:
  for +l: B.Line
  for +t: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  {mitems(l <> t, fa, defs, o, n) == S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), mitems(t, fa, defs, o, 1n+n)) : List<&2, R.Item>}

def mitems_cons(l, t, fa, defs, o, n):
  macc_split(t, fa, defs, o, True{}, 1n+n, L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n))

# A record of a split line (same CHROM and POS as the line, fields fs): its
# item, as the run keys it with the line's place and input POS.
def item_site(+fs: List<&2, String>, +p: String, +term: String, +n: Nat, +fa: List<&2, B.Contig>,
  +h: {L.same_site(fs, p) == True{} : Bool}) ->
  {L.item(fa, B.Line{p, term}, n) == L.item_of(L.judge(fa, p), B.Line{p, term}, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) : R.Item}:
  +gs = B.Rec.fields(p)
  +s0 = String.eq(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n))
  +s1 = String.eq(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n))
  +sr = L.same_fields(fs, gs, [2n, 3n, 5n, 6n, 8n])
  +hf = P.and_true_r(Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)), Bool.and(s0, Bool.and(s1, sr)), h)
  +e0 = Q.str_eq_sound(B.Rec.field(fs, 0n), B.Rec.field(gs, 0n), P.and_true_l(s0, Bool.and(s1, sr), hf))
  +e1 = Q.str_eq_sound(B.Rec.field(fs, 1n), B.Rec.field(gs, 1n), P.and_true_l(s1, sr, P.and_true_r(s0, Bool.and(s1, sr), hf)))
  +J = L.judge(fa, p)
  +LN = {B.Line{p, term} : B.Line}
  %e1 : {L.item_of(J, LN, B.At{n, B.Rec.field(gs, 0n), _}, Maybe.default(&2, Nat, B.Pos.read(_), 0n)) == L.item_of(J, LN, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) : R.Item}
  %e0 : {L.item_of(J, LN, B.At{n, _, B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.item_of(J, LN, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) : R.Item}
  {==}

# A line -m cannot split never stops the run with UNSORTED
# ========================================================

def AOK(ms: List<&2, Maybe<&2, B.Code>>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      T.mcode_ok(m) && AOK(t)

def and_tt(a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

def put_ok(m: Maybe<&2, B.Code>, +r: Maybe<&2, B.Code>, +hm: {T.mcode_ok(m) == True{} : Bool}, +hr: {T.mcode_ok(r) == True{} : Bool}) ->
  {T.mcode_ok(L.first_code.put(m, r)) == True{} : Bool}:
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

law fc_ok:
  for +ms: List<&2, Maybe<&2, B.Code>>
  for +h: {AOK(ms) == True{} : Bool}
  {T.mcode_ok(L.first_code(ms)) == True{} : Bool}

def fc_ok(ms, h):
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      put_ok(m, L.first_code(t), P.and_true_l(T.mcode_ok(m), AOK(t), h), fc_ok(t, P.and_true_r(T.mcode_ok(m), AOK(t), h)))

law aok_app:
  for +xs: List<&2, Maybe<&2, B.Code>>
  for +ys: List<&2, Maybe<&2, B.Code>>
  for +hx: {AOK(xs) == True{} : Bool}
  for +hy: {AOK(ys) == True{} : Bool}
  {AOK(List.append(&2, Maybe<&2, B.Code>, xs, ys)) == True{} : Bool}

def aok_app(xs, ys, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+m, +t}:
      and_tt(T.mcode_ok(m), AOK(List.append(&2, Maybe<&2, B.Code>, t, ys)), P.and_true_l(T.mcode_ok(m), AOK(t), hx),
        aok_app(t, ys, P.and_true_r(T.mcode_ok(m), AOK(t), hx), hy))

def pick_ok(b: Bool, +x: Maybe<&2, B.Code>, +y: Maybe<&2, B.Code>, +hx: {T.mcode_ok(x) == True{} : Bool}, +hy: {T.mcode_ok(y) == True{} : Bool}) ->
  {T.mcode_ok(Bool.pick(Maybe<&2, B.Code>, b, x, y)) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

def count_ok(+num: B.Num, +n: Nat, +cp: Maybe<&2, Nat>, +v: String) -> {T.mcode_ok(L.count_problem(num, n, cp, v)) == True{} : Bool}:
  +c = List.length(&2, String, L.values(v))
  pick_ok(String.eq(v, ".") || B.Vals.fits(B.Vals.expected_count(num, n, B.Vals.copies(cp, n, c)), c), None{}, Some{B.BadCount{}}, {==}, {==})

def iof_n(x: B.Num, +e: String, +n: Nat) -> {T.mcode_ok(L.info_problem.of(Some{x}, e, n)) == True{} : Bool}:
  match x:
    case B.NumA{}:
      count_ok(B.NumA{}, n, Some{2n}, L.value_text(e))
    case B.NumR{}:
      count_ok(B.NumR{}, n, Some{2n}, L.value_text(e))
    case B.NumG{}:
      count_ok(B.NumG{}, n, Some{2n}, L.value_text(e))
    case B.NumOther{}:
      {==}
    case B.NumUnknown{}:
      {==}

def iof_ok(m: Maybe<&2, B.Num>, +e: String, +n: Nat) -> {T.mcode_ok(L.info_problem.of(m, e, n)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      iof_n(x, e, n)

def ip_ok(es: List<&2, String>, +tags: List<&2, B.Tag>, +n: Nat) -> {AOK(L.info_problems(es, tags, n)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +m = B.Tags.find(tags, B.Info.key(e))
      and_tt(T.mcode_ok(L.info_problem(m, e, n)), AOK(L.info_problems(t, tags, n)),
        pick_ok(L.has_value(e), L.info_problem.of(m, e, n), Bool.pick(Maybe<&2, B.Code>, B.Num.per_allele(m), Some{B.BadCount{}}, None{}),
          iof_ok(m, e, n), pick_ok(B.Num.per_allele(m), Some{B.BadCount{}}, None{}, {==}, {==})),
        ip_ok(t, tags, n))

def fpn_ok(x: B.Num, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>) -> {T.mcode_ok(L.format_problem(Some{x}, k, v, n, p)) == True{} : Bool}:
  match x:
    case B.NumA{}:
      count_ok(B.NumA{}, n, p, v)
    case B.NumR{}:
      count_ok(B.NumR{}, n, p, v)
    case B.NumG{}:
      count_ok(B.NumG{}, n, p, v)
    case B.NumOther{}:
      {==}
    case B.NumUnknown{}:
      {==}

def fp_ok(m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>) -> {T.mcode_ok(L.format_problem(m, k, v, n, p)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      fpn_ok(x, k, v, n, p)

def sp_ok(ks: List<&2, String>, vs: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat, +p: Maybe<&2, Nat>) -> {AOK(L.sample_problems(ks, vs, fmt, n, p)) == True{} : Bool}:
  match ks vs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+v, +vt}:
      {==}
    case Con{+k, +kt} Nil{}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      and_tt(T.mcode_ok(Bool.pick(Maybe<&2, B.Code>, String.eq(k, "GT"), L.gt_problem(n, v), L.format_problem(B.Tags.find(fmt, k), k, v, n, p))),
        AOK(L.sample_problems(kt, vt, fmt, n, p)),
        pick_ok(String.eq(k, "GT"), L.gt_problem(n, v), L.format_problem(B.Tags.find(fmt, k), k, v, n, p),
          pick_ok(L.gt_ok.go(L.gt_tokens(v), n), None{}, Some{B.BadGt{}}, {==}, {==}),
          fp_ok(B.Tags.find(fmt, k), k, v, n, p)),
        sp_ok(kt, vt, fmt, n, p))

def ssp_ok(cols: List<&2, String>, +ks: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat) -> {AOK(L.samples_problems(cols, ks, fmt, n)) == True{} : Bool}:
  match cols:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      +vs = String.split(c, ':')
      aok_app(L.sample_problems(ks, vs, fmt, n, B.Gt.copies(B.Fmt.gt(ks, vs))), L.samples_problems(t, ks, fmt, n),
        sp_ok(ks, vs, fmt, n, B.Gt.copies(B.Fmt.gt(ks, vs))), ssp_ok(t, ks, fmt, n))

# split_problem never answers UNSORTED.
def problem_ok(+defs: B.Defs, +body: String) -> {T.mcode_ok(L.split_problem(defs, body)) == True{} : Bool}:
  +fs = B.Rec.fields(body)
  +n = L.n_alts(body)
  +d = Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(fs)), None{}, Some{B.DupAlts{}})
  +IP = L.info_problems(L.info_entries(body), B.Defs.info(defs), n)
  +SP = L.samples_problems(List.drop(&2, String, fs, 9n), L.format_keys(body), B.Defs.fmt(defs), n)
  +dc = Bool.pick(Maybe<&2, B.Code>, B.Text.has_cr(body), Some{B.BadCr{}}, None{})
  fc_ok(dc <> (d <> List.append(&2, Maybe<&2, B.Code>, IP, SP)),
    and_tt(T.mcode_ok(dc), AOK(d <> List.append(&2, Maybe<&2, B.Code>, IP, SP)),
      pick_ok(B.Text.has_cr(body), Some{B.BadCr{}}, None{}, {==}, {==}),
      and_tt(T.mcode_ok(d), AOK(List.append(&2, Maybe<&2, B.Code>, IP, SP)),
        pick_ok(B.Alts.distinct(B.Rec.alts(fs)), None{}, Some{B.DupAlts{}}, {==}, {==}),
        aok_app(IP, SP, ip_ok(L.info_entries(body), B.Defs.info(defs), n), ssp_ok(List.drop(&2, String, fs, 9n), L.format_keys(body), B.Defs.fmt(defs), n)))))

def is_unsplit(pt: B.Parts) -> Bool:
  match pt:
    case B.Unsplit{c}:
      True{}
    case _:
      False{}

def uo.k(+c: B.Code, +m: Maybe<&2, B.Code>, +e: {Some{Some{c}} == Some{m} : Maybe<&2, Maybe<&2, B.Code>>}, +hm: {T.mcode_ok(m) == True{} : Bool}) -> {T.code_ok(c) == True{} : Bool}:
  Equal.trans(Bool, T.code_ok(c), T.mcode_ok(m), True{},
    Equal.cong(Maybe<&2, Maybe<&2, B.Code>>, Bool, z => T.mcode_ok(Maybe.default(&2, Maybe<&2, B.Code>, z, None{})), Some{Some{c}}, Some{m}, e), hm)

def UR(+defs: B.Defs, +o0: Bool, +fs: List<&2, String>, +body: String, z1: Bool, z2: Bool) -> Maybe<&2, Maybe<&2, B.Code>>:
  L.refusal(B.Rec.parts.if(True{} && Bool.not(z1) && z2, B.Text.has_cr(body), defs, o0, fs))

def uo(sp: Bool, m: Bool, b: Bool, +defs: B.Defs, +s: Bool, +w: Nat, +o0: Bool, +a: List<&2, String>, +body: String, +c: B.Code,
  +em: {B.Rec.malformed(B.Rec.fields(body)) == m : Bool},
  +eb: {Nat.is_le(2n, L.n_alts(body)) == b : Bool},
  +h: {B.Rec.parts.if(sp && Bool.not(m) && b, B.Text.has_cr(body), defs, o0, B.Rec.fields(body)) == B.Unsplit{c} : B.Parts}) -> {T.code_ok(c) == True{} : Bool}:
  match sp m b:
    case False{} _ _:
      Empty.absurd({T.code_ok(c) == True{} : Bool}, P.false_ne_true(Equal.cong(B.Parts, Bool, z => is_unsplit(z), B.Whole{}, B.Unsplit{c}, h)))
    case True{} True{} _:
      Empty.absurd({T.code_ok(c) == True{} : Bool}, P.false_ne_true(Equal.cong(B.Parts, Bool, z => is_unsplit(z), B.Whole{}, B.Unsplit{c}, h)))
    case True{} False{} False{}:
      Empty.absurd({T.code_ok(c) == True{} : Bool}, P.false_ne_true(Equal.cong(B.Parts, Bool, z => is_unsplit(z), B.Whole{}, B.Unsplit{c}, h)))
    case True{} False{} True{}:
      +fs = B.Rec.fields(body)
      +e1 = W.split_when_p(defs, B.Opts{s, w, True{}, o0, a}, body, {==}, em, eb)
      +e2 = Equal.trans(Maybe<&2, Maybe<&2, B.Code>>, L.refusal(B.Rec.parts.if(True{}, B.Text.has_cr(body), defs, o0, fs)),
        L.refusal(B.Rec.parts.if(True{} && Bool.not(B.Rec.malformed(fs)) && Nat.is_le(2n, L.n_alts(body)), B.Text.has_cr(body), defs, o0, fs)),
        Some{L.split_problem(defs, body)},
        Equal.sym(Maybe<&2, Maybe<&2, B.Code>>, L.refusal(B.Rec.parts.if(True{} && Bool.not(B.Rec.malformed(fs)) && Nat.is_le(2n, L.n_alts(body)), B.Text.has_cr(body), defs, o0, fs)),
          L.refusal(B.Rec.parts.if(True{}, B.Text.has_cr(body), defs, o0, fs)),
          Equal.trans(Maybe<&2, Maybe<&2, B.Code>>, UR(defs, o0, fs, body, B.Rec.malformed(fs), Nat.is_le(2n, L.n_alts(body))), UR(defs, o0, fs, body, False{}, Nat.is_le(2n, L.n_alts(body))), UR(defs, o0, fs, body, False{}, True{}),
            Equal.cong(Bool, Maybe<&2, Maybe<&2, B.Code>>, z => UR(defs, o0, fs, body, z, Nat.is_le(2n, L.n_alts(body))), B.Rec.malformed(fs), False{}, em),
            Equal.cong(Bool, Maybe<&2, Maybe<&2, B.Code>>, z => UR(defs, o0, fs, body, False{}, z), Nat.is_le(2n, L.n_alts(body)), True{}, eb))),
        e1)
      +e3 = Equal.trans(Maybe<&2, Maybe<&2, B.Code>>, Some{Some{c}}, L.refusal(B.Rec.parts.if(True{}, B.Text.has_cr(body), defs, o0, fs)), Some{L.split_problem(defs, body)},
        Equal.cong(B.Parts, Maybe<&2, Maybe<&2, B.Code>>, z => L.refusal(z), B.Unsplit{c}, B.Rec.parts.if(True{}, B.Text.has_cr(body), defs, o0, fs), Equal.sym(B.Parts, B.Rec.parts.if(True{}, B.Text.has_cr(body), defs, o0, fs), B.Unsplit{c}, h)),
        e2)
      uo.k(c, L.split_problem(defs, body), e3, problem_ok(defs, body))

# The code of a line -m cannot split is not UNSORTED.
law unsplit_ok:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +c: B.Code
  for +h: {B.Rec.parts(defs, o, body) == B.Unsplit{c} : B.Parts}
  {T.code_ok(c) == True{} : Bool}

def unsplit_ok(defs, o, body, c, h):
  match o:
    case B.Opts{+s, +w, +sp, +o0, +a}:
      +fs = B.Rec.fields(body)
      uo(sp, B.Rec.malformed(fs), Nat.is_le(2n, L.n_alts(body)), defs, s, w, o0, a, body, c, {==}, {==}, h)

# The rest of a run, as one value
# ===============================

type Tl is Data:
  Tl{ps: List<&2, String>, term: String, at: B.At, inpos: Nat, t: List<&2, B.Line>}

def TT(tl: Tl, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  match tl:
    case Tl{ps, term, at, inpos, t}:
      TR(ps, term, at, inpos, t, fa, defs, o, st)

# The lines ls, from a line boundary.
def TLs(ls: List<&2, B.Line>) -> Tl:
  Tl{Nil{}, "", B.At{0n, "", ""}, 0n, ls}

def tt_code(tl: Tl, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  {R.Report.code(R.finish(TT(tl, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == 1n : Nat}:
  match tl:
    case Tl{+ps, +term, +at, +inpos, +t}:
      tr_code(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)

def tt_notes(tl: Tl, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  {R.Report.notes(R.finish(TT(tl, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == ns : List<&2, B.Note>}:
  match tl:
    case Tl{+ps, +term, +at, +inpos, +t}:
      tr_notes(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)

def tt_halted(tl: Tl, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  {R.finish(TT(tl, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})) == R.Report{out, ns, 1n} : R.Report}:
  match tl:
    case Tl{+ps, +term, +at, +inpos, +t}:
      tr_halted(ps, term, at, inpos, t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)

# A body line whose outcome stops the run.
def BLS(-M: R.RunSt -> Type, r: B.Res, +st: R.RunSt, o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hr: {T.res_ok(r) == True{} : Bool},
  hs: {L.stops(r, R.Opts.strict(o)) == True{} : Bool},
  hstop: @cd: B.Code -> {L.is_unsorted(B.Stop{cd, Some{at}, None{}}) == False{} : Bool} -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}}))) ->
  M(R.body_line(r, st, o, l, at, inpos)):
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      hstop(B.Malformed{}, {==})
    case B.Res{B.NoContig{}, k, t, s}:
      hstop(B.UnknownChrom{}, {==})
    case B.Res{B.Problem{+c}, k, t, s}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              hstop(c, T.stop_ok(c, Some{at}, None{}, hr))
            case False{}:
              Empty.absurd(M(R.body_line(B.Res{B.Problem{c}, k, t, s}, st, B.Opts{False{}, w, om_m, om_z, a}, l, at, inpos)), P.false_ne_true(hs))
    case B.Res{B.Skipped{}, k, t, s}:
      Empty.absurd(M(R.body_line(B.Res{B.Skipped{}, k, t, s}, st, o, l, at, inpos)), P.false_ne_true(hs))
    case B.Res{B.Normalized{}, k, t, s}:
      Empty.absurd(M(R.body_line(B.Res{B.Normalized{}, k, t, s}, st, o, l, at, inpos)), P.false_ne_true(hs))

def ul.s(-M: R.RunSt -> Type, s: Bool, +r: B.Res, +c: B.Code, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hs: {L.stops(r, R.Opts.strict(o)) == s : Bool},
  hr: {T.res_ok(r) == True{} : Bool},
  hc: {T.code_ok(c) == True{} : Bool},
  hstop: @cd: B.Code -> {L.is_unsorted(B.Stop{cd, Some{at}, None{}}) == False{} : Bool} -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: @nts: List<&2, B.Note> -> @k2: R.Cnt -> {L.any_unsorted(nts) == False{} : Bool} ->
    M(R.keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, nts, k2))) ->
  M(Bool.pick(R.RunSt, s, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))):
  match s:
    case True{}:
      BLS(M, r, st, o, l, at, inpos, hr, hs, hstop)
    case False{}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              hstop(c, T.stop_ok(c, Some{at}, None{}, hc))
            case False{}:
              hkey([B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}), {==})

# A line -m cannot split (code c): it stops the run (not with UNSORTED) or
# goes on as the line as it came.
def UL(-M: R.RunSt -> Type, +r: B.Res, +c: B.Code, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hr: {T.res_ok(r) == True{} : Bool},
  hc: {T.code_ok(c) == True{} : Bool},
  hstop: @cd: B.Code -> {L.is_unsorted(B.Stop{cd, Some{at}, None{}}) == False{} : Bool} -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: @nts: List<&2, B.Note> -> @k2: R.Cnt -> {L.any_unsorted(nts) == False{} : Bool} ->
    M(R.keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, nts, k2))) ->
  M(L.unsplit_in(r, c, o, st, l, at, inpos)):
  ul.s(M, L.stops(r, R.Opts.strict(o)), r, c, st, o, l, at, inpos, {==}, hr, hc, hstop, hkey)
