import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./proof_b_simdefs.bend as S
import ./proof_b_frame_fr.bend as FF
import ./proof_s_recs.bend as RS
import ./proof_s_site.bend as SI
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# The records of a split line, handled one by one as the machine does
# (proof_b_simdefs.bend's rgo: each record unticks the run, then is a line
# of its own), give what the spec gives the split line (LAWS.bend's
# pieces_in). Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def POS(+c1: String) -> Nat:
  Maybe.default(&2, Nat, B.Pos.read(c1), 0n)

# body_line keeps the line count (copied from proof_e_wrap_spec.bend).
law stop_n:
  for +st: R.RunSt
  for +out: String
  for +nt: B.Note
  {R.RunSt.n(R.stop(st, out, nt)) == R.RunSt.n(st) : Nat}

def stop_n(st, out, nt):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law emit_n:
  for +f: R.Flush
  for +st: R.RunSt
  for +rest: List<&2, R.Item>
  for +at: B.At
  {R.RunSt.n(R.emit.ready(f, st, rest, at)) == R.RunSt.n(st) : Nat}

def emit_n(f, st, rest, at):
  match f st:
    case R.Broke{+o, +bad, +prev} +s:
      stop_n(s, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{+o2, +l2} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law same_run_n:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  {R.RunSt.n(R.same_run(st, w, it)) == R.RunSt.n(st) : Nat}

def same_run_n(st, w, it):
  match st it:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x} R.Item{+key, +inpos, +at, +text}:
      +buf = R.insert(R.Item{key, inpos, at, text}, b)
      emit_n(R.flush(R.take_ready(w, inpos, buf), l), R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, R.drop_ready(w, inpos, buf), at)

law new_run_go_n:
  for +f: R.Flush
  for +again: Bool
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.n(R.new_run.go(f, again, st, w, chrom, it)) == R.RunSt.n(st) : Nat}

def new_run_go_n(f, again, st, w, chrom, it):
  match f again st:
    case R.Broke{+o, +bad, +prev} _ +s:
      stop_n(s, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{+o2, +l2} True{} +s:
      stop_n(s, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})
    case R.Flushed{+o2, +l2} False{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      same_run_n(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, x}, w, it)

law new_run_n:
  for +st: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.n(R.new_run(st, w, chrom, it)) == R.RunSt.n(st) : Nat}

def new_run_n(st, w, chrom, it):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      new_run_go_n(R.flush(b, l), R.has(chrom, e), R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)

law keyed_go_n:
  for +same: Bool
  for +st2: R.RunSt
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  {R.RunSt.n(R.keyed.go(same, st2, w, chrom, it)) == R.RunSt.n(st2) : Nat}

def keyed_go_n(same, st2, w, chrom, it):
  match same:
    case True{}:
      same_run_n(st2, w, it)
    case False{}:
      new_run_n(st2, w, chrom, it)

law keyed_n:
  for +st: R.RunSt
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  {R.RunSt.n(R.keyed(st, w, it, nts, k2)) == R.RunSt.n(st) : Nat}

def keyed_n(st, w, it, nts, k2):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      keyed_go_n(R.is_cur(c, R.Item.chrom(it)), R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}, w, R.Item.chrom(it), it)

law problem_n:
  for +strict: Bool
  for +st: R.RunSt
  for +w: Nat
  for +c: B.Code
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.n(R.problem_line(strict, st, w, c, l, at, inpos)) == R.RunSt.n(st) : Nat}

def problem_n(strict, st, w, c, l, at, inpos):
  match strict:
    case True{}:
      stop_n(st, "", B.Stop{c, Some{at}, None{}})
    case False{}:
      keyed_n(st, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

law body_n:
  for +r: B.Res
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.n(R.body_line(r, st, o, l, at, inpos)) == R.RunSt.n(st) : Nat}

def body_n(r, st, o, l, at, inpos):
  match r:
    case B.Res{B.Broken{}, +k, +t, +s}:
      stop_n(st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, +k, +t, +s}:
      stop_n(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{+c}, +k, +t, +s}:
      problem_n(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, +k, +t, +s}:
      keyed_n(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +k, +t, +s}:
      keyed_n(st, R.Opts.w(o), R.Item{k, inpos, at, t ++ B.Line.term(l)}, R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

# At most one ALT: the record stays whole.
def whole1(+defs: B.Defs, +o: B.Opts, +p: String, +h: {L.n_alts(p) == 1n : Nat}) -> {B.Rec.parts(defs, o, p) == B.Whole{} : B.Parts}:
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(p)
      +A = Bool.and(sp, Bool.not(B.Rec.malformed(fs)))
      %Equal.sym(Nat, List.length(&2, String, B.Rec.alts(fs)), 1n, h) :
        {B.Rec.parts.if(Bool.and(A, Nat.is_le(2n, _)), B.Text.has_cr(p), defs, o0, fs) == B.Whole{} : B.Parts}
      %Equal.sym(Bool, Bool.and(A, False{}), False{}, N.and_false_r(A)) :
        {B.Rec.parts.if(_, B.Text.has_cr(p), defs, o0, fs) == B.Whole{} : B.Parts}
      {==}

# One record from a run not stopped, in the body, at line 1+k: unticked,
# then a line of its own, it is the spec's piece_in.
def one.k(+fa: List<&2, B.Contig>, +defs2: B.Defs, +o: B.Opts, +term: String, +c0: String, +c1: String, +p: String, +k: Nat,
  +hh: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +ck: R.Cnt, +so: String, +ns: List<&2, B.Note>,
  hs: SI.SITE(c0, c1, p)) ->
  {L.line_step(fa, defs2, o, Norm.rs_untick(R.RunSt{1n+k, True{}, hh, c, e, la, b, ck, so, ns, False{}}), B.Line{p, term})
    == L.piece_in(False{}, p, fa, o, R.RunSt{1n+k, True{}, hh, c, e, la, b, ck, so, ns, False{}}, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}:
  (h0, q) = hs
  (h1, ha) = q
  +s = {R.RunSt{1n+k, True{}, hh, c, e, la, b, ck, so, ns, False{}} : R.RunSt}
  +fs = B.Rec.fields(p)
  %Equal.sym(Nat, Nat.sub(k, 0n), k, N.sub_zero(k)) :
    {L.body_in(B.Rec.parts(defs2, o, p), fa, o, R.RunSt{1n+_, True{}, hh, c, e, la, b, ck, so, ns, False{}}, B.Line{p, term}, B.At{1n+_, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
      == L.piece_in(False{}, p, fa, o, s, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}
  %Equal.sym(B.Parts, B.Rec.parts(defs2, o, p), B.Whole{}, whole1(defs2, o, p, ha)) :
    {L.body_in(_, fa, o, s, B.Line{p, term}, B.At{1n+k, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.piece_in(False{}, p, fa, o, s, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 0n), c0, h0) :
    {R.body_line(L.judge(fa, p), s, o, B.Line{p, term}, B.At{1n+k, _, B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.piece_in(False{}, p, fa, o, s, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 1n), c1, h1) :
    {R.body_line(L.judge(fa, p), s, o, B.Line{p, term}, B.At{1n+k, c0, _}, POS(_)) == L.piece_in(False{}, p, fa, o, s, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}
  {==}

# The records one by one, from a run in the body at line 1+k.
law rgo_pieces:
  for +ps: Ss()
  for +fa: List<&2, B.Contig>
  for +defs2: B.Defs
  for +o: B.Opts
  for +term: String
  for +c0: String
  for +c1: String
  for +k: Nat
  for +s: R.RunSt
  for hs: SI.ALLSITE(c0, c1, ps)
  for +hi: {R.RunSt.inbody(s) == True{} : Bool}
  for +hn: {R.RunSt.n(s) == 1n+k : Nat}
  {S.rgo(RS.LS(ps, term), fa, defs2, o, s) == L.pieces_in(ps, fa, o, s, term, B.At{1n+k, c0, c1}, POS(c1)) : R.RunSt}

def rgo_pieces(ps, fa, defs2, o, term, c0, c1, k, s, hs, hi, hn):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      match s:
        case R.RunSt{+n, +i, +hh, +c, +e, +la, +b, +ck, +so, +ns, +x}:
          match x:
            case True{}:
              (sp, rest) = hs
              rgo_pieces(t, fa, defs2, o, term, c0, c1, k, R.RunSt{n, i, hh, c, e, la, b, ck, so, ns, True{}}, rest, hi, hn)
            case False{}:
              (sp, rest) = hs
              +AT = {B.At{1n+k, c0, c1} : B.At}
              %Equal.sym(Bool, i, True{}, hi) :
                {S.rgo(RS.LS(t, term), fa, defs2, o, L.line_step(fa, defs2, o, Norm.rs_untick(R.RunSt{n, _, hh, c, e, la, b, ck, so, ns, False{}}), B.Line{p, term}))
                  == L.pieces_in(t, fa, o, L.piece_in(False{}, p, fa, o, R.RunSt{n, _, hh, c, e, la, b, ck, so, ns, False{}}, term, AT, POS(c1)), term, AT, POS(c1)) : R.RunSt}
              %Equal.sym(Nat, n, 1n+k, hn) :
                {S.rgo(RS.LS(t, term), fa, defs2, o, L.line_step(fa, defs2, o, Norm.rs_untick(R.RunSt{_, True{}, hh, c, e, la, b, ck, so, ns, False{}}), B.Line{p, term}))
                  == L.pieces_in(t, fa, o, L.piece_in(False{}, p, fa, o, R.RunSt{_, True{}, hh, c, e, la, b, ck, so, ns, False{}}, term, AT, POS(c1)), term, AT, POS(c1)) : R.RunSt}
              +s1 = {R.RunSt{1n+k, True{}, hh, c, e, la, b, ck, so, ns, False{}} : R.RunSt}
              +X = L.piece_in(False{}, p, fa, o, s1, term, AT, POS(c1))
              %Equal.sym(R.RunSt, L.line_step(fa, defs2, o, Norm.rs_untick(s1), B.Line{p, term}), X, one.k(fa, defs2, o, term, c0, c1, p, k, hh, c, e, la, b, ck, so, ns, sp)) :
                {S.rgo(RS.LS(t, term), fa, defs2, o, _) == L.pieces_in(t, fa, o, X, term, AT, POS(c1)) : R.RunSt}
              rgo_pieces(t, fa, defs2, o, term, c0, c1, k, X, rest,
                FF.ib_body_line(L.judge(fa, p), s1, o, B.Line{p, term}, AT, POS(c1)),
                body_n(L.judge(fa, p), s1, o, B.Line{p, term}, AT, POS(c1)))

# A split line (B.Rec.parts' Pieces) from a run in the body that has not
# stopped: its records, one by one from the ticked run, give the spec's step.
law rgo_line:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +defs2: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +ps: Ss()
  for +hx: {R.RunSt.halt(st) == False{} : Bool}
  for +hi: {R.RunSt.inbody(st) == True{} : Bool}
  for +hp: {B.Rec.parts(defs, o, B.Line.body(l)) == B.Pieces{ps} : B.Parts}
  {S.rgo(RS.LS(ps, B.Line.term(l)), fa, defs2, o, R.tick(st)) == L.line_step(fa, defs, o, st, l) : R.RunSt}

def rgo_line(fa, defs, defs2, o, st, l, ps, hx, hi, hp):
  match st:
    case R.RunSt{+n, +i, +hh, +c, +e, +la, +b, +ck, +so, +ns, +x}:
      +fs = B.Rec.fields(B.Line.body(l))
      +tm = B.Line.term(l)
      %Equal.sym(Bool, x, False{}, hx) :
        {S.rgo(RS.LS(ps, tm), fa, defs2, o, R.RunSt{1n+n, i, hh, c, e, la, b, ck, so, ns, _}) == L.line_step.go(_, fa, defs, o, R.RunSt{n, i, hh, c, e, la, b, ck, so, ns, _}, l) : R.RunSt}
      %Equal.sym(Bool, i, True{}, hi) :
        {S.rgo(RS.LS(ps, tm), fa, defs2, o, R.RunSt{1n+n, _, hh, c, e, la, b, ck, so, ns, False{}}) == L.line_in(_, fa, defs, o, R.RunSt{1n+n, _, hh, c, e, la, b, ck, so, ns, False{}}, l) : R.RunSt}
      +s1 = {R.RunSt{1n+n, True{}, hh, c, e, la, b, ck, so, ns, False{}} : R.RunSt}
      %Equal.sym(B.Parts, B.Rec.parts(defs, o, B.Line.body(l)), B.Pieces{ps}, hp) :
        {S.rgo(RS.LS(ps, tm), fa, defs2, o, s1) == L.body_in(_, fa, o, s1, l, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) : R.RunSt}
      rgo_pieces(ps, fa, defs2, o, tm, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), n, s1, SI.parts_site(defs, o, B.Line.body(l), ps, hp), {==}, {==})
