import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_rundefs.bend as RD
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BD
import ./proof_b_lines_pd.bend as LP
import ./proof_machine_nat.bend as PN
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_drive_out.bend as DO
import ./proof_b_run.bend as RN
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_ins.bend as RI
import ./proof_b_enc.bend as EN
import ./proof_b_lit.bend as LIT
import ./proof_b_lines_str.bend as LS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Two budget lemmas (notes/bytes_proofs_budget.md, "For pb-run", R1 and
# R2), with the statements fixed there:
#   hop: what a state stands for begins with what the driver wrote (once in
#     the body, run.bend only adds to out; before it, the guard makes O
#     empty);
#   yield_out: a yield hands out at least 256 bytes.

# ---------------------------------------------------------------------------
# R1: out only grows in the body
# ---------------------------------------------------------------------------

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

# b's out is at least a's, and b is in the body exactly when a is.
def Q2(+a: R.RunSt, +b: R.RunSt) -> Bool:
  Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b))) && beq(R.RunSt.inbody(a), R.RunSt.inbody(b))

def len_app(+x: String, +s: String) -> {Nat.is_le(String.length(x), String.length(String.append(x, s))) == True{} : Bool}:
  match x:
    case SNil{}:
      N.le_zero_l(String.length(s))
    case SCon{+h, +t}:
      len_app(t, s)

def beq_refl(+a: Bool) -> {beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def beq_trans(+a: Bool, +b: Bool, +c: Bool, +h1: {beq(a, b) == True{} : Bool}, +h2: {beq(b, c) == True{} : Bool}) -> {beq(a, c) == True{} : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case False{} False{} False{}:
      {==}
    case True{} True{} False{}:
      h2
    case True{} False{} _:
      Empty.absurd({beq(True{}, c) == True{} : Bool}, AB.false_ne_true(h1))
    case False{} True{} _:
      Empty.absurd({beq(False{}, c) == True{} : Bool}, AB.false_ne_true(h1))
    case False{} False{} True{}:
      h2

def beq_true(+a: Bool, +b: Bool, +h: {beq(a, b) == True{} : Bool}, +ha: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, AB.false_ne_true(h))
    case False{} _:
      Empty.absurd({b == True{} : Bool}, AB.false_ne_true(ha))

def q2_le(+a: R.RunSt, +b: R.RunSt, +h: {Q2(a, b) == True{} : Bool}) ->
  {Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b))) == True{} : Bool}:
  AB.and_true_l(Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b))), beq(R.RunSt.inbody(a), R.RunSt.inbody(b)), h)

def q2_ib(+a: R.RunSt, +b: R.RunSt, +h: {Q2(a, b) == True{} : Bool}) ->
  {beq(R.RunSt.inbody(a), R.RunSt.inbody(b)) == True{} : Bool}:
  AB.and_true_r(Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b))), beq(R.RunSt.inbody(a), R.RunSt.inbody(b)), h)

def q2_refl(+a: R.RunSt) -> {Q2(a, a) == True{} : Bool}:
  LP.and_tt(Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(a))), beq(R.RunSt.inbody(a), R.RunSt.inbody(a)),
    N.le_refl(String.length(P.RunSt.out(a))), beq_refl(R.RunSt.inbody(a)))

def q2_trans(+a: R.RunSt, +b: R.RunSt, +c: R.RunSt, +h1: {Q2(a, b) == True{} : Bool}, +h2: {Q2(b, c) == True{} : Bool}) -> {Q2(a, c) == True{} : Bool}:
  LP.and_tt(Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(c))), beq(R.RunSt.inbody(a), R.RunSt.inbody(c)),
    N.le_trans(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b)), String.length(P.RunSt.out(c)), q2_le(a, b, h1), q2_le(b, c, h2)),
    beq_trans(R.RunSt.inbody(a), R.RunSt.inbody(b), R.RunSt.inbody(c), q2_ib(a, b, h1), q2_ib(b, c, h2)))

# b's out is a's then s, and b keeps a's inbody.
def q2_ext(+a: R.RunSt, +b: R.RunSt, +s: String,
  +ho: {P.RunSt.out(b) == String.append(P.RunSt.out(a), s) : String},
  +hi: {R.RunSt.inbody(b) == R.RunSt.inbody(a) : Bool}) -> {Q2(a, b) == True{} : Bool}:
  +hl = AB.subst(String, z => {Nat.is_le(String.length(P.RunSt.out(a)), String.length(z)) == True{} : Bool}, String.append(P.RunSt.out(a), s), P.RunSt.out(b),
    Equal.sym(String, P.RunSt.out(b), String.append(P.RunSt.out(a), s), ho), len_app(P.RunSt.out(a), s))
  +hb = AB.subst(Bool, z => {beq(R.RunSt.inbody(a), z) == True{} : Bool}, R.RunSt.inbody(a), R.RunSt.inbody(b), Equal.sym(Bool, R.RunSt.inbody(b), R.RunSt.inbody(a), hi), beq_refl(R.RunSt.inbody(a)))
  LP.and_tt(Nat.is_le(String.length(P.RunSt.out(a)), String.length(P.RunSt.out(b))), beq(R.RunSt.inbody(a), R.RunSt.inbody(b)), hl, hb)

# The body's state updates (run.bend).
def stop_q(+st: R.RunSt, +out: String, +nt: B.Note) -> {Q2(st, R.stop(st, out, nt)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      q2_ext(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, R.stop(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, out, nt), out, {==}, {==})

def emit_q(+f: R.Flush, +st: R.RunSt, +rest: List<&2, R.Item>, +at: B.At) -> {Q2(st, R.emit.ready(f, st, rest, at)) == True{} : Bool}:
  match f st:
    case R.Broke{+o, +bad, +prev} _:
      stop_q(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{+o2, +l2} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      q2_ext(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, R.RunSt{n, i, h, c, e, l2, rest, k, String.append(o, o2), ns, x}, o2, {==}, {==})

def same_q(+st: R.RunSt, +w: Nat, +it: R.Item) -> {Q2(st, R.same_run(st, w, it)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      match it:
        case R.Item{+key, +inpos, +at, +text}:
          +buf = R.insert(R.Item{key, inpos, at, text}, b)
          +st0 = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
          +st1 = {R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x} : R.RunSt}
          q2_trans(st0, st1, R.emit.ready(R.flush(R.take_ready(w, inpos, buf), l), st1, R.drop_ready(w, inpos, buf), at),
            q2_ext(st0, st1, "", Equal.sym(String, String.append(o, ""), o, PN.str_nil(o)), {==}),
            emit_q(R.flush(R.take_ready(w, inpos, buf), l), st1, R.drop_ready(w, inpos, buf), at))

def newgo_q(+f: R.Flush, +again: Bool, +st: R.RunSt, +w: Nat, +chrom: String, +it: R.Item) ->
  {Q2(st, R.new_run.go(f, again, st, w, chrom, it)) == True{} : Bool}:
  match f again st:
    case R.Broke{+o, +bad, +prev} _ _:
      stop_q(st, o, B.Stop{B.Unsorted{}, Some{bad}, prev})
    case R.Flushed{+o2, +l2} True{} _:
      stop_q(st, o2, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}})
    case R.Flushed{+o2, +l2} False{} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +st0 = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
      +st1 = {R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, String.append(o, o2), ns, x} : R.RunSt}
      q2_trans(st0, st1, R.same_run(st1, w, it), q2_ext(st0, st1, o2, {==}, {==}), same_q(st1, w, it))

def new_q(+st: R.RunSt, +w: Nat, +chrom: String, +it: R.Item) -> {Q2(st, R.new_run(st, w, chrom, it)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      newgo_q(R.flush(b, l), R.has(chrom, e), R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)

def kgo_q(+same: Bool, +st2: R.RunSt, +w: Nat, +chrom: String, +it: R.Item) -> {Q2(st2, R.keyed.go(same, st2, w, chrom, it)) == True{} : Bool}:
  match same:
    case True{}:
      same_q(st2, w, it)
    case False{}:
      new_q(st2, w, chrom, it)

def keyed_q(+st: R.RunSt, +w: Nat, +it: R.Item, +nts: List<&2, B.Note>, +k2: R.Cnt) -> {Q2(st, R.keyed(st, w, it, nts, k2)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +st0 = {R.RunSt{n, i, h, c, e, l, b, k, o, ns, x} : R.RunSt}
      +st2 = {R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x} : R.RunSt}
      q2_trans(st0, st2, R.keyed.go(R.is_cur(c, R.Item.chrom(it)), st2, w, R.Item.chrom(it), it),
        q2_ext(st0, st2, "", Equal.sym(String, String.append(o, ""), o, PN.str_nil(o)), {==}),
        kgo_q(R.is_cur(c, R.Item.chrom(it)), st2, w, R.Item.chrom(it), it))

def prob_q(+strict: Bool, +st: R.RunSt, +w: Nat, +c: B.Code, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {Q2(st, R.problem_line(strict, st, w, c, l, at, inpos)) == True{} : Bool}:
  match strict:
    case True{}:
      stop_q(st, "", B.Stop{c, Some{at}, None{}})
    case False{}:
      keyed_q(st, w, R.Item{inpos, inpos, at, B.Line.text(l)}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

def body_q(+r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {Q2(st, R.body_line(r, st, o, l, at, inpos)) == True{} : Bool}:
  match r:
    case B.Res{B.Broken{}, +k, +t, +s}:
      stop_q(st, "", B.Stop{B.Malformed{}, Some{at}, None{}})
    case B.Res{B.NoContig{}, +k, +t, +s}:
      stop_q(st, "", B.Stop{B.UnknownChrom{}, Some{at}, None{}})
    case B.Res{B.Problem{+c}, +k, +t, +s}:
      prob_q(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)
    case B.Res{B.Skipped{}, +k, +t, +s}:
      keyed_q(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +k, +t, +s}:
      keyed_q(st, R.Opts.w(o), R.Item{k, inpos, at, String.append(t, B.Line.term(l))}, R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, B.Line.body(l))), False{}, False{}))

# A split line's records, each as a body line (LAWS.bend's pieces_in).
def pin_q(halted: Bool, +p: String, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) ->
  {Q2(st, L.piece_in(halted, p, fa, o, st, term, at, inpos)) == True{} : Bool}:
  match halted:
    case True{}:
      q2_refl(st)
    case False{}:
      body_q(L.judge(fa, p), st, o, B.Line{p, term}, at, inpos)

def pins_q(ps: List<&2, String>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) ->
  {Q2(st, L.pieces_in(ps, fa, o, st, term, at, inpos)) == True{} : Bool}:
  match ps:
    case Nil{}:
      q2_refl(st)
    case +p <> +t:
      +st1 = L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)
      q2_trans(st, st1, L.pieces_in(t, fa, o, st1, term, at, inpos), pin_q(R.RunSt.halt(st), p, fa, o, st, term, at, inpos), pins_q(t, fa, o, st1, term, at, inpos))

def uns_q(b: Bool, +r: B.Res, +c: B.Code, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {Q2(st, Bool.pick(R.RunSt, b, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))) == True{} : Bool}:
  match b:
    case True{}:
      body_q(r, st, o, l, at, inpos)
    case False{}:
      prob_q(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)

# A body line by what -m does with it (LAWS.bend's body_in).
def bin_q(pt: B.Parts, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {Q2(st, L.body_in(pt, fa, o, st, l, at, inpos)) == True{} : Bool}:
  match pt:
    case B.Whole{}:
      body_q(L.judge(fa, B.Line.body(l)), st, o, l, at, inpos)
    case B.Pieces{ps}:
      pins_q(ps, fa, o, st, B.Line.term(l), at, inpos)
    case B.Unsplit{+c}:
      uns_q(L.stops(L.judge(fa, B.Line.body(l)), R.Opts.strict(o)), L.judge(fa, B.Line.body(l)), c, o, st, l, at, inpos)

# One line, in the body.
def step_q(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Q2(st, L.line_step(fa, dfs, o, st, l)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +ou, +ns, True{}}:
      q2_refl(R.RunSt{n, i, h, c, e, la, b, k, ou, ns, True{}})
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +ou, +ns, False{}}:
      +st0 = {R.RunSt{n, True{}, h, c, e, la, b, k, ou, ns, False{}} : R.RunSt}
      +st1 = R.tick(st0)
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{R.RunSt.n(st1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      q2_trans(st0, st1, L.body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, o, st1, l, at, B.Rec.pos(fs)),
        q2_ext(st0, st1, "", Equal.sym(String, String.append(ou, ""), ou, PN.str_nil(ou)), {==}),
        bin_q(B.Rec.parts(dfs, o, B.Line.body(l)), fa, o, st1, l, at, B.Rec.pos(fs)))
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +ou, +ns, False{}}:
      Empty.absurd({Q2(R.RunSt{n, False{}, h, c, e, la, b, k, ou, ns, False{}}, L.line_step(fa, dfs, o, R.RunSt{n, False{}, h, c, e, la, b, k, ou, ns, False{}}, l)) == True{} : Bool},
        AB.false_ne_true(hin))


def run_q(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Q2(st, L.run.go(ls, fa, dfs, o, st)) == True{} : Bool}:
  match ls:
    case Nil{}:
      q2_refl(st)
    case +l <> +t:
      +st1 = L.line_step(fa, dfs, o, st, l)
      +h1 = step_q(dfs, fa, o, st, l, hin)
      q2_trans(st, st1, L.run.go(t, fa, dfs, o, st1), h1,
        run_q(dfs, t, fa, o, st1, beq_true(R.RunSt.inbody(st), R.RunSt.inbody(st1), q2_ib(st, st1, h1), hin)))

# The end, in the body.
def ffl_q(+f: R.Flush, +o: String, +ns: List<&2, B.Note>, +k: R.Cnt) ->
  {Nat.is_le(String.length(o), String.length(R.Report.out(R.finish.flush(f, o, ns, k)))) == True{} : Bool}:
  match f k:
    case R.Broke{+o2, +bad, +prev} _:
      len_app(o, o2)
    case R.Flushed{+o2, +l2} R.Cnt{+n, +ch, +sk, +wa}:
      len_app(o, o2)

def fin_q(+st: R.RunSt, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Nat.is_le(String.length(P.RunSt.out(st)), String.length(R.Report.out(R.finish(st)))) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      N.le_refl(String.length(o))
    case R.RunSt{+n, True{}, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      ffl_q(R.flush(b, l), o, ns, k)
    case R.RunSt{+n, False{}, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      Empty.absurd({Nat.is_le(String.length(o), String.length(R.Report.out(R.finish(R.RunSt{n, False{}, h, c, e, l, b, k, o, ns, False{}})))) == True{} : Bool},
        AB.false_ne_true(hin))

# The driver's O, then the run's own out, then the rest of the run.
def pre_ib(+O: String, +N: List<&2, B.Note>, +st: R.RunSt) -> {R.RunSt.inbody(S.pre(O, N, st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

def pre_out(+O: String, +N: List<&2, B.Note>, +st: R.RunSt) -> {Nat.is_le(String.length(O), String.length(P.RunSt.out(S.pre(O, N, st)))) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      len_app(O, o)

def run_out(+dfs: B.Defs, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +O: String, +N: List<&2, B.Note>, +st: R.RunSt,
  +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), String.length(R.Report.out(R.finish(L.run.go(ls, fa, dfs, o, S.pre(O, N, st)))))) == True{} : Bool}:
  +s0 = S.pre(O, N, st)
  +hin0 = Equal.trans(Bool, R.RunSt.inbody(s0), R.RunSt.inbody(st), True{}, pre_ib(O, N, st), hin)
  +h1 = run_q(dfs, ls, fa, o, s0, hin0)
  +sF = L.run.go(ls, fa, dfs, o, s0)
  N.le_trans(String.length(O), String.length(P.RunSt.out(s0)), String.length(R.Report.out(R.finish(sF))), pre_out(O, N, st),
    N.le_trans(String.length(P.RunSt.out(s0)), String.length(P.RunSt.out(sF)), String.length(R.Report.out(R.finish(sF))), q2_le(s0, sF, h1),
      fin_q(sF, beq_true(R.RunSt.inbody(s0), R.RunSt.inbody(sF), q2_ib(s0, sF, h1), hin0))))

# The records still waiting (S.RG): each a step from the unticked run.
def ut_q(+st: R.RunSt) -> {Q2(st, Norm.rs_untick(st)) == True{} : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      q2_ext(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, Norm.rs_untick(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}), "", Equal.sym(String, String.append(o, ""), o, PN.str_nil(o)), {==})

def rsi_q(halt: Bool, +fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Q2(st, S.rstep.if(halt, fa, dfs, o, st, l)) == True{} : Bool}:
  match halt:
    case True{}:
      q2_refl(st)
    case False{}:
      +u = Norm.rs_untick(st)
      +hu = ut_q(st)
      q2_trans(st, u, L.line_step(fa, dfs, o, u, l), hu, step_q(dfs, fa, o, u, l, beq_true(R.RunSt.inbody(st), R.RunSt.inbody(u), q2_ib(st, u, hu), hin)))

def rgo_q(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Q2(st, S.rgo(ls, fa, dfs, o, st)) == True{} : Bool}:
  match ls:
    case Nil{}:
      q2_refl(st)
    case +l <> +t:
      +st1 = S.rstep(fa, dfs, o, st, l)
      +h1 = rsi_q(R.RunSt.halt(st), fa, dfs, o, st, l, hin)
      q2_trans(st, st1, S.rgo(t, fa, dfs, o, st1), h1, rgo_q(t, fa, dfs, o, st1, beq_true(R.RunSt.inbody(st), R.RunSt.inbody(st1), q2_ib(st, st1, h1), hin)))

def rg_q(rs: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Q2(st, S.RG(rs, fa, dfs, o, st)) == True{} : Bool}:
  match rs:
    case Nil{}:
      q2_refl(st)
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      +st1 = S.rgo(B.Text.lines(P.srctext(P.SPP{len, t, d, at})), fa, dfs, o, st)
      +h1 = rgo_q(B.Text.lines(P.srctext(P.SPP{len, t, d, at})), fa, dfs, o, st, hin)
      q2_trans(st, st1, S.RG(r, fa, dfs, o, st1), h1, rg_q(r, fa, dfs, o, st1, beq_true(R.RunSt.inbody(st), R.RunSt.inbody(st1), q2_ib(st, st1, h1), hin)))
    case Con{P.SRP{+l}, +r}:
      +st1 = S.rstep(fa, dfs, o, st, l)
      +h1 = rsi_q(R.RunSt.halt(st), fa, dfs, o, st, l, hin)
      q2_trans(st, st1, S.RG(r, fa, dfs, o, st1), h1, rg_q(r, fa, dfs, o, st1, beq_true(R.RunSt.inbody(st), R.RunSt.inbody(st1), q2_ib(st, st1, h1), hin)))
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      q2_refl(st)
    case Con{P.SLP{+q}, +r}:
      q2_refl(st)

# The same with the records first.
def run_out2(+dfs: B.Defs, +rs: List<&2, P.SrcP>, +ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +O: String, +N: List<&2, B.Note>, +st: R.RunSt,
  +hin: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), String.length(R.Report.out(R.finish(L.run.go(ls, fa, dfs, o, S.RG(rs, fa, dfs, o, S.pre(O, N, st))))))) == True{} : Bool}:
  +s0 = S.pre(O, N, st)
  +hin0 = Equal.trans(Bool, R.RunSt.inbody(s0), R.RunSt.inbody(st), True{}, pre_ib(O, N, st), hin)
  +s1 = S.RG(rs, fa, dfs, o, s0)
  +h0 = rg_q(rs, fa, dfs, o, s0, hin0)
  +hin1 = beq_true(R.RunSt.inbody(s0), R.RunSt.inbody(s1), q2_ib(s0, s1, h0), hin0)
  +h1 = run_q(dfs, ls, fa, o, s1, hin1)
  +sF = L.run.go(ls, fa, dfs, o, s1)
  N.le_trans(String.length(O), String.length(P.RunSt.out(s0)), String.length(R.Report.out(R.finish(sF))), pre_out(O, N, st),
    N.le_trans(String.length(P.RunSt.out(s0)), String.length(P.RunSt.out(s1)), String.length(R.Report.out(R.finish(sF))), q2_le(s0, s1, h0),
      N.le_trans(String.length(P.RunSt.out(s1)), String.length(P.RunSt.out(sF)), String.length(R.Report.out(R.finish(sF))), q2_le(s1, sF, h1),
        fin_q(sF, beq_true(R.RunSt.inbody(s1), R.RunSt.inbody(sF), q2_ib(s1, sF, h1), hin1)))))

# The guard's two cases.
def len0(+s: String, +h: {String.is_empty(s) == True{} : Bool}, +m: Nat) -> {Nat.is_le(String.length(s), m) == True{} : Bool}:
  match s:
    case SNil{}:
      N.le_zero_l(m)
    case SCon{+a, +t}:
      Empty.absurd({Nat.is_le(String.length(SCon{a, t}), m) == True{} : Bool}, AB.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

def gcase(+ib: Bool, +O: String, +N: List<&2, B.Note>, +m: Nat,
  +hg: {Bool.or(ib, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool},
  ih: @hib: {ib == True{} : Bool} -> {Nat.is_le(String.length(O), m) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), m) == True{} : Bool}:
  match ib:
    case True{}:
      ih({==})
    case False{}:
      len0(O, AB.and_true_l(String.is_empty(O), List.is_empty(&2, B.Note, N), hg), m)

def hop_k(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hg: {S.guard(O, N, p) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), String.length(R.Report.out(S.report(fa, cs, O, N, p)))) == True{} : Bool}:
  match p:
    case S.StP{+o, S.MSP{+s, +qs, +ql, Some{+c}}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      len_app(O, Norm.cat(List.reverse(&2, String, qs)))
    case S.StP{+o, S.MSP{+s, +qs, +ql, None{}}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +st = S.smd(S.MSP{s, qs, ql, None{}})
      +ls = B.Text.lines(S.intext(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs))
      gcase(R.RunSt.inbody(st), O, N, String.length(R.Report.out(R.finish(L.run.go(ls, fa, S.DEFS(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), o, S.RG(S.recs(src), fa, S.DEFS(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), o, S.pre(O, N, st)))))), hg,
        hib => run_out2(S.DEFS(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), S.recs(src), ls, fa, o, O, N, st, hib))
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +st = S.smd(S.MBP{rp})
      +ls = B.Text.lines(S.intext(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}, cs))
      gcase(R.RunSt.inbody(st), O, N, String.length(R.Report.out(R.finish(L.run.go(ls, fa, S.DEFS(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), o, S.RG(S.recs(src), fa, S.DEFS(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), o, S.pre(O, N, st)))))), hg,
        hib => run_out2(S.DEFS(S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}, cs), S.recs(src), ls, fa, o, O, N, st, hib))


# R1.
def hop(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  +hg: {S.guard(O, N, p) == True{} : Bool}) ->
  {Nat.is_le(String.length(O), String.length(R.Report.out(T))) == True{} : Bool}:
  AB.subst(R.Report, z => {Nat.is_le(String.length(O), String.length(R.Report.out(z))) == True{} : Bool}, S.report(fa, cs, O, N, p), T, hr, hop_k(fa, cs, O, N, p, hg))

# ---------------------------------------------------------------------------
# R2: a yield hands out at least 256 bytes
# ---------------------------------------------------------------------------

def unsome(+d: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def some_inj(+a: String, +b: String, +h: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => unsome("", m), Some{a}, Some{b}, h)

# 256 <= 2^30 (as a word, then a number).
def c256() -> {Nat.is_le(256n, U32.to_nat(1073741824)) == True{} : Bool}:
  AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(1073741824)) == True{} : Bool}, U32.to_nat(256), 256n, {==},
    Equal.trans(Bool, Nat.is_le(U32.to_nat(256), U32.to_nat(1073741824)), U32.is_le(256, 1073741824), True{},
      Equal.sym(Bool, U32.is_le(256, 1073741824), Nat.is_le(U32.to_nat(256), U32.to_nat(1073741824)), U.is_le_to_nat(256, 1073741824)), {==}))

# The byte mode: what take hands out is ob's first ow bytes, ow >= 2^30.
def spec_out_len(+rp: P.RunP, +hi: {RD.RunInv(rp) == True{} : Bool}, +hy: {U32.is_le(1073741824, P.RunP.ow(rp)) == True{} : Bool}) ->
  {Nat.is_le(256n, String.length(P.RunSt.out(P.specRun(rp)))) == True{} : Bool}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +X = NR.chars(D.view(C.BT(obl, obt)))
      +W = U32.to_nat(ow)
      +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +hwo = PI.pr11(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +hX = Equal.trans(Nat, String.length(X), List.length(&2, U32, D.view(C.BT(obl, obt))), U32.to_nat(obl), LS.length_chars(D.view(C.BT(obl, obt))), O.view_size_t(obl, obt, RD.tdepth(obt), hok))
      +hkX = AB.subst(Nat, z => {Nat.is_le(W, z) == True{} : Bool}, U32.to_nat(obl), String.length(X), Equal.sym(Nat, String.length(X), U32.to_nat(obl), hX), hwo)
      +h256 = N.le_trans(256n, U32.to_nat(1073741824), W, c256(),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(1073741824), W), U32.is_le(1073741824, ow), True{}, Equal.sym(Bool, U32.is_le(1073741824, ow), Nat.is_le(U32.to_nat(1073741824), W), U.is_le_to_nat(1073741824, ow)), hy))
      AB.subst(Nat, z => {Nat.is_le(256n, z) == True{} : Bool}, W, String.length(String.take(X, W)), Equal.sym(Nat, String.length(String.take(X, W)), W, RI.s_len_take(X, W, hkX)), h256)

def yo_mb(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +t: String,
  +hi: {RD.RunInv(rp) == True{} : Bool},
  +hy: {U32.is_le(1073741824, P.RunP.ow(rp)) == True{} : Bool},
  +ht: {BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>},
  tk: DO.TakeR(rp, DO.lsum(src))) ->
  {Nat.is_le(256n, String.length(t)) == True{} : Bool}:
  (+ol, tk1) = tk
  (+ot, tk2) = tk1
  (+d, tk3) = tk2
  (+rp2, tk4) = tk3
  (+e1, tk5) = tk4
  (+eok, tk6) = tk5
  (+ech, tk7) = tk6
  (+einv, tk8) = tk7
  (+esp, eow) = tk8
  +SP = P.specRun(rp)
  +ns = P.RunSt.notes(SP)
  +t2 = P.RunSt.out(SP)
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{t2},
    EN.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), t2,
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), t2, DO.chars_nr(D.view(C.BT(ol, ot))), ech)))
  +hs = {
    %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
      {BN.sout(Norm.out.left(o, Norm.MB{P.mkRun(rp)}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Ask{Nil{}})) == Some{t2} : Maybe<&2, String>}
    %Equal.sym((D.Bytes & List<&2, B.Note>) & NR.Run, NR.take(P.mkRun(rp), DO.lsum(src)), ((C.BT(ol, ot), ns), P.mkRun(rp2)), e1) :
      {BN.sout(Norm.out.k(Norm.md.take.k(_), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Ask{Nil{}})) == Some{t2} : Maybe<&2, String>}
    eout : {BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})) == Some{t2} : Maybe<&2, String>}}
  +tt = some_inj(t, t2, Equal.trans(Maybe<&2, String>, Some{t}, BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})), Some{t2},
    Equal.sym(Maybe<&2, String>, BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})), Some{t}, ht), hs))
  AB.subst(String, z => {Nat.is_le(256n, String.length(z)) == True{} : Bool}, t2, t, Equal.sym(String, t, t2, tt), spec_out_len(rp, hi, hy))

# The String mode: take_w's first part has min(|s|, w) characters at least.
def pred_le(+k: Nat, +W: Nat, +h: {Nat.is_le(1n+k, W) == True{} : Bool}) -> {Nat.is_le(k, Nat.sub(W, 1n)) == True{} : Bool}:
  match W:
    case 0n:
      Empty.absurd({Nat.is_le(k, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+V:
      %Equal.sym(Nat, Nat.sub(V, 0n), V, N.sub_zero(V)) : {Nat.is_le(k, _) == True{} : Bool}
      h

def tg(+s: String, +z: Bool, +w: U32, +ez: {U32.is_zero(w) == z : Bool}, +q: Nat,
  +hs: {Nat.is_le(q, String.length(s)) == True{} : Bool},
  +hw: {Nat.is_le(q, U32.to_nat(w)) == True{} : Bool}) ->
  {Nat.is_le(q, String.length(Norm.Cut2.now(Norm.take_w.go(s, z, w)))) == True{} : Bool}:
  match s z q:
    case SNil{} _ 0n:
      N.le_zero_l(String.length(Norm.Cut2.now(Norm.take_w.go(SNil{}, z, w))))
    case SNil{} _ 1n+q2:
      Empty.absurd({Nat.is_le(1n+q2, String.length(Norm.Cut2.now(Norm.take_w.go(SNil{}, z, w)))) == True{} : Bool}, AB.false_ne_true(hs))
    case SCon{+a, +t} True{} 0n:
      N.le_zero_l(String.length(Norm.Cut2.now(Norm.take_w.go(SCon{a, t}, True{}, w))))
    case SCon{+a, +t} True{} 1n+q2:
      +h0 = Equal.trans(Bool, Nat.is_eq(U32.to_nat(w), 0n), U32.is_zero(w), True{}, Equal.sym(Bool, U32.is_zero(w), Nat.is_eq(U32.to_nat(w), 0n), U.is_zero_to_nat(w)), ez)
      +hw0 = AB.subst(Nat, v => {Nat.is_le(1n+q2, v) == True{} : Bool}, U32.to_nat(w), 0n, N.eq_sound(U32.to_nat(w), 0n, h0), hw)
      Empty.absurd({Nat.is_le(1n+q2, String.length(Norm.Cut2.now(Norm.take_w.go(SCon{a, t}, True{}, w)))) == True{} : Bool}, AB.false_ne_true(hw0))
    case SCon{+a, +t} False{} 0n:
      N.le_zero_l(String.length(Norm.Cut2.now(Norm.take_w.go(SCon{a, t}, False{}, w))))
    case SCon{+a, +t} False{} 1n+q2:
      +w1 = (w - 1 : U32)
      +X = Norm.take_w.go(t, U32.is_zero(w1), w1)
      +h1w = Equal.trans(Bool, U32.is_le(1, w), Nat.is_le(U32.to_nat(1), U32.to_nat(w)), True{}, U.is_le_to_nat(1, w),
        N.le_trans(U32.to_nat(1), 1n+q2, U32.to_nat(w), N.le_zero_l(q2), hw))
      +hw1 = AB.subst(Nat, v => {Nat.is_le(q2, v) == True{} : Bool}, Nat.sub(U32.to_nat(w), 1n), U32.to_nat(w1),
        Equal.sym(Nat, U32.to_nat(w1), Nat.sub(U32.to_nat(w), 1n), U.to_nat_sub_le(w, 1, h1w)), pred_le(q2, U32.to_nat(w), hw))
      +ih = tg(t, U32.is_zero(w1), w1, {==}, q2, hs, hw1)
      %Equal.sym(Norm.Cut2, X, Norm.Cut2{Norm.Cut2.now(X), Norm.Cut2.later(X)}, DO.cut_eta(X)) :
        {Nat.is_le(1n+q2, String.length(Norm.Cut2.now(Norm.take_w.cons(a, _)))) == True{} : Bool}
      ih

def yo_ms2(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o2: String, +ns: List<&2, B.Note>, +x: Bool,
  +qs: List<&2, String>, +ql: Nat, +code: Maybe<&2, Nat>, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +t: String,
  +h256: {Nat.is_le(256n, String.length(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)))) == True{} : Bool},
  +ht: {BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>},
  os: &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) == C.BT(ol, ot) : D.Bytes}
    & ({D.ok(C.BT(ol, ot), d) == True{} : Bool} & {NR.chars(D.view(C.BT(ol, ot))) == Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)) : String}))) ->
  {Nat.is_le(256n, String.length(t)) == True{} : Bool}:
  (+ol, os1) = os
  (+ot, os2) = os1
  (+d, os3) = os2
  (+e1, os4) = os3
  (+hok, ech) = os4
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))},
    EN.out_ok(ol, ot, d, hok, C.ok_d(ol, ot, d, hok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)),
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), DO.chars_nr(D.view(C.BT(ol, ot))), ech)))
  +hs = {
    %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
      {BN.sout(Norm.out.left(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Ask{Nil{}})) == Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))} : Maybe<&2, String>}
    %Equal.sym(Norm.Cut2, Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), Norm.Cut2{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))}, DO.cut_eta(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) :
      {BN.sout(Norm.out.k(Norm.ms.take.c(_, R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, code), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Ask{Nil{}})) == Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))} : Maybe<&2, String>}
    %Equal.sym(D.Bytes, NR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), C.BT(ol, ot), e1) :
      {BN.sout(Norm.out.k(((_, ns), Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))], String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), code}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Ask{Nil{}})) == Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))} : Maybe<&2, String>}
    eout : {BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})) == Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))} : Maybe<&2, String>}}
  +tt = some_inj(t, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Equal.trans(Maybe<&2, String>, Some{t}, BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})), Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))},
    Equal.sym(Maybe<&2, String>, BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})), Some{t}, ht), hs))
  AB.subst(String, z => {Nat.is_le(256n, String.length(z)) == True{} : Bool}, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), t, Equal.sym(String, t, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), tt), h256)

def yo_ms1(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o2: String, +ns: List<&2, B.Note>, +x: Bool,
  +qs: List<&2, String>, +ql: Nat, +code: Maybe<&2, Nat>, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +t: String,
  +hmd: {S.md_ok(S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}) == True{} : Bool},
  +hy: {Nat.is_le(Norm.lim(), ql) == True{} : Bool},
  +ht: {BN.sout(Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>},
  tw: {String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) == Norm.cat(List.reverse(&2, String, qs)) : String} & {Norm.len_le(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), 1073741824) == True{} : Bool}) ->
  {Nat.is_le(256n, String.length(t)) == True{} : Bool}:
  (+hcat, hlen) = tw
  +hql = N.eq_sound(ql, String.length(Norm.cat(List.reverse(&2, String, qs))), DO.z6_1(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))
  +hbc = DO.z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)
  +hbn = DO.bytes_l(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), AB.subst(String, z => {E.is_bytes(z) == True{} : Bool}, Norm.cat(List.reverse(&2, String, qs)), String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), Equal.sym(String, String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), Norm.cat(List.reverse(&2, String, qs)), hcat), hbc))
  +hq = AB.subst(Nat, v => {Nat.is_le(256n, v) == True{} : Bool}, ql, String.length(Norm.cat(List.reverse(&2, String, qs))), hql, N.le_trans(256n, Norm.lim(), ql, {==}, hy))
  +h256 = tg(Norm.cat(List.reverse(&2, String, qs)), U32.is_zero(1073741824), 1073741824, {==}, 256n, hq, c256())
  yo_ms2(dfs, fa, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, t, h256, ht, RN.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), hbn, hlen))

# R2.
def yield_out(+fa: List<&2, B.Contig>, +p: S.StP, +hw: {S.WF(fa, p) == True{} : Bool}, +hy: {BD.yc(p) == True{} : Bool}, +t: String,
  +ht: {BN.sout(Norm.out(S.mkSt(fa, p), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>}) ->
  {Nat.is_le(256n, String.length(t)) == True{} : Bool}:
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +hi = DO.wf_md(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}, hw)
      yo_mb(dfs, fa, o, rp, src, pd, eof, back, wp, asked, fneed, t, hi, hy, ht, RN.run_take(rp, DO.lsum(src), hi))
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      yo_ms1(dfs, fa, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, t,
        DO.wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed, dfs}, hw), hy, ht, LIT.take_w_ok(Norm.cat(List.reverse(&2, String, qs)), 1073741824))
