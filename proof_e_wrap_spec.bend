import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_b_defs.bend as P
import ./proof_b_simdefs.bend as S
import ./proof_b_frame.bend as FRM
import ./proof_b_frame_bl.bend as BL
import ./proof_b_lines_str.bend as LS
import ./proof_base.bend as PB
import ./proof_e_defs.bend as SD

# Helpers for proof_e_wrap.bend (area E1), on the spec only: each line the
# run handles adds one to its line count (while it has not stopped); the run
# over appended lines; settle, pre and the segment lemma's shiftS and segok.

# The line count
# ==============

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

law head_n:
  for +isc: Bool
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {R.RunSt.n(R.head_line(isc, st, o, l)) == R.RunSt.n(st) : Nat}

def head_n(isc, st, o, l):
  match isc st l:
    case True{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x} B.Line{+bd, +term}:
      {==}
    case False{} R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x} +ln:
      {==}

law line_in_n:
  for +phase: Bool
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  {R.RunSt.n(L.line_in(phase, fa, o, st, l)) == R.RunSt.n(st) : Nat}

def line_in_n(phase, fa, o, st, l):
  match phase:
    case False{}:
      head_n(R.is_chrom_line(B.Line.body(l)), st, o, l)
    case True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      body_n(L.judge(fa, B.Line.body(l)), st, o, l, B.At{R.RunSt.n(st), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

# A line from a state that has not stopped adds one.
law step_n:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +hx: {R.RunSt.halt(st) == False{} : Bool}
  {R.RunSt.n(L.line_step(fa, o, st, l)) == 1n+R.RunSt.n(st) : Nat}

def step_n(fa, o, st, l, hx):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) : {R.RunSt.n(L.line_step.go(_, fa, o, R.RunSt{n, i, h, c, e, la, b, k, out, ns, x}, l)) == 1n+n : Nat}
      line_in_n(i, fa, o, R.RunSt{1n+n, i, h, c, e, la, b, k, out, ns, x}, l)

# A state from which a line leads to a run that has not stopped had not
# stopped.
law step_live:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +hx: {R.RunSt.halt(L.line_step(fa, o, st, l)) == False{} : Bool}
  {R.RunSt.halt(st) == False{} : Bool}

def step_live(fa, o, st, l, hx):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, True{}}:
      hx
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, False{}}:
      {==}

law go_live:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +hx: {R.RunSt.halt(L.run.go(ls, fa, o, st)) == False{} : Bool}
  {R.RunSt.halt(st) == False{} : Bool}

def go_live(ls, fa, o, st, hx):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, True{}}:
      +s = {R.RunSt{n, i, h, c, e, la, b, k, out, ns, True{}} : R.RunSt}
      Equal.trans(Bool, R.RunSt.halt(s), R.RunSt.halt(L.run.go(ls, fa, o, s)), False{},
        Equal.cong(R.RunSt, Bool, z => R.RunSt.halt(z), s, L.run.go(ls, fa, o, s), Equal.sym(R.RunSt, L.run.go(ls, fa, o, s), s, FRM.run_halted(ls, fa, o, s, {==}))), hx)
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +out, +ns, False{}}:
      {==}

law plus_one:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == Nat.add(1n+a, b) : Nat}

def plus_one(a, b):
  match a:
    case 0n:
      {==}
    case 1n+a2:
      %plus_one(a2, b) : {1n+Nat.add(a2, 1n+b) == 1n+_ : Nat}
      {==}

# The run over lines ls ends not stopped: its count went up by |ls|.
law go_n:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +hx: {R.RunSt.halt(L.run.go(ls, fa, o, st)) == False{} : Bool}
  {R.RunSt.n(L.run.go(ls, fa, o, st)) == Nat.add(R.RunSt.n(st), List.length(&2, B.Line, ls)) : Nat}

def go_n(ls, fa, o, st, hx):
  match ls:
    case Nil{}:
      Equal.sym(Nat, Nat.add(R.RunSt.n(st), 0n), R.RunSt.n(st), PB.add_zero(R.RunSt.n(st)))
    case Con{+l, +t}:
      +s1 = L.line_step(fa, o, st, l)
      +h1 = go_live(t, fa, o, s1, hx)
      +e1 = step_n(fa, o, st, l, step_live(fa, o, st, l, h1))
      Equal.trans(Nat, R.RunSt.n(L.run.go(t, fa, o, s1)), Nat.add(R.RunSt.n(s1), List.length(&2, B.Line, t)), Nat.add(R.RunSt.n(st), 1n+List.length(&2, B.Line, t)),
        go_n(t, fa, o, s1, hx),
        Equal.trans(Nat, Nat.add(R.RunSt.n(s1), List.length(&2, B.Line, t)), Nat.add(1n+R.RunSt.n(st), List.length(&2, B.Line, t)), Nat.add(R.RunSt.n(st), 1n+List.length(&2, B.Line, t)),
          Equal.cong(Nat, Nat, z => Nat.add(z, List.length(&2, B.Line, t)), R.RunSt.n(s1), 1n+R.RunSt.n(st), e1),
          Equal.sym(Nat, Nat.add(R.RunSt.n(st), 1n+List.length(&2, B.Line, t)), Nat.add(1n+R.RunSt.n(st), List.length(&2, B.Line, t)), plus_one(R.RunSt.n(st), List.length(&2, B.Line, t)))))

# The run over appended lines
# ===========================

law go_app:
  for +a: List<&2, B.Line>
  for +b: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  {L.run.go(List.append(&2, B.Line, a, b), fa, o, st) == L.run.go(b, fa, o, L.run.go(a, fa, o, st)) : R.RunSt}

def go_app(a, b, fa, o, st):
  match a:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      go_app(t, b, fa, o, L.line_step(fa, o, st, l))

# Two states equal up to settle lead to the same report.
law fin_settle:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +x: R.RunSt
  for +y: R.RunSt
  for +h: {P.settle(x) == P.settle(y) : R.RunSt}
  {R.finish(L.run.go(ls, fa, o, x)) == R.finish(L.run.go(ls, fa, o, y)) : R.Report}

def fin_settle(ls, fa, o, x, y, h):
  Equal.trans(R.Report, R.finish(L.run.go(ls, fa, o, x)), R.finish(L.run.go(ls, fa, o, P.settle(x))), R.finish(L.run.go(ls, fa, o, y)),
    Equal.sym(R.Report, R.finish(L.run.go(ls, fa, o, P.settle(x))), R.finish(L.run.go(ls, fa, o, x)), FRM.settle_inv(ls, fa, o, x)),
    Equal.trans(R.Report, R.finish(L.run.go(ls, fa, o, P.settle(x))), R.finish(L.run.go(ls, fa, o, P.settle(y))), R.finish(L.run.go(ls, fa, o, y)),
      Equal.cong(R.RunSt, R.Report, z => R.finish(L.run.go(ls, fa, o, z)), P.settle(x), P.settle(y), h),
      FRM.settle_inv(ls, fa, o, y)))

# settle, pre, shiftS, segok
# ==========================

law settle_n:
  for +x: R.RunSt
  {R.RunSt.n(P.settle(x)) == R.RunSt.n(x) : Nat}

def settle_n(x):
  match x:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      {==}

law settle_halt:
  for +x: R.RunSt
  {R.RunSt.halt(P.settle(x)) == R.RunSt.halt(x) : Bool}

def settle_halt(x):
  match x:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      {==}

law spec_n:
  for +rp: P.RunP
  {R.RunSt.n(P.specRun(rp)) == P.RunP.n(rp) : Nat}

def spec_n(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law spec_halt:
  for +rp: P.RunP
  {R.RunSt.halt(P.specRun(rp)) == P.RunP.x(rp) : Bool}

def spec_halt(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law pre_pre:
  for +O: String
  for +N: List<&2, B.Note>
  for +t: String
  for +ns: List<&2, B.Note>
  for +x: R.RunSt
  {S.pre(String.append(O, t), List.append(&2, B.Note, N, ns), x) == S.pre(O, N, S.pre(t, ns, x)) : R.RunSt}

def pre_pre(O, N, t, ns, x):
  match x:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns0, +hx}:
      %Equal.sym(String, String.append(String.append(O, t), o), String.append(O, String.append(t, o)), LS.sassoc(O, t, o)) : {R.RunSt{n, i, h, c, e, l, b, k, _, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), ns0), hx} == S.pre(O, N, S.pre(t, ns, R.RunSt{n, i, h, c, e, l, b, k, o, ns0, hx})) : R.RunSt}
      %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), ns0), List.append(&2, B.Note, N, List.append(&2, B.Note, ns, ns0)), PB.append_assoc(B.Note, N, ns, ns0)) : {R.RunSt{n, i, h, c, e, l, b, k, String.append(O, String.append(t, o)), _, hx} == S.pre(O, N, S.pre(t, ns, R.RunSt{n, i, h, c, e, l, b, k, o, ns0, hx})) : R.RunSt}
      {==}

law pre_shift:
  for +c0: String
  for +O: String
  for +N: List<&2, B.Note>
  for +sx: R.RunSt
  for +tx: R.RunSt
  {S.pre(O, N, SD.shiftS(c0, sx, tx)) == SD.shiftS(c0, S.pre(O, N, sx), tx) : R.RunSt}

def pre_shift(c0, O, N, sx, tx):
  match sx tx:
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +txx}:
      +same = R.is_cur(sc, c0)
      +X = String.append(SD.texts(sb), to)
      %Equal.sym(String, String.append(String.append(O, so), X), String.append(O, String.append(so, X)), LS.sassoc(O, so, X)) :
        {S.pre(O, N, SD.shiftS(c0, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sxx}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, txx}))
          == R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))), SD.last_shift(tl, same, sl, SD.last_item(sb), sn), SD.items_shift(sn, tb), SD.cnt_add(sk, tk), _, List.append(&2, B.Note, N, sns), False{}} : R.RunSt}
      {==}

law segok_pre:
  for +w: Nat
  for +c0: String
  for +l: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +sx: R.RunSt
  for +tx: R.RunSt
  {SD.segok(w, c0, l, S.pre(O, N, sx), tx) == SD.segok(w, c0, l, sx, tx) : Bool}

def segok_pre(w, c0, l, O, N, sx, tx):
  match sx tx:
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, +txx}:
      {==}

# segok reads of T's last item only its line and input POS.
law segok_settle:
  for +w: Nat
  for +c0: String
  for +l: Nat
  for +sx: R.RunSt
  for +tx: R.RunSt
  {SD.segok(w, c0, l, sx, P.settle(tx)) == SD.segok(w, c0, l, sx, tx) : Bool}

def segok_settle(w, c0, l, sx, tx):
  match sx tx:
    case R.RunSt{+sn, True{}, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, False{}} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, True{}}:
      {==}
    case R.RunSt{+sn, True{}, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, True{}} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, True{}}:
      {==}
    case R.RunSt{+sn, False{}, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, True{}}:
      {==}
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, None{}, +tb, +tk, +to, +tns, False{}}:
      {==}
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, Some{R.Item{+k, +p, B.At{0n, +c, +s}, +t}}, +tb, +tk, +to, +tns, False{}}:
      {==}
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, Some{R.Item{+k, +p, B.At{1n+m, +c, +s}, +t}}, +tb, +tk, +to, +tns, False{}}:
      {==}

law ls_blank:
  for +tl: Maybe<&2, R.Item>
  for +same: Bool
  for +sl: Maybe<&2, R.Item>
  for +el: Maybe<&2, R.Item>
  for +d: Nat
  {P.blank(SD.last_shift(P.blank(tl), same, sl, el, d)) == P.blank(SD.last_shift(tl, same, sl, el, d)) : Maybe<&2, R.Item>}

def ls_blank(tl, same, sl, el, d):
  match tl same:
    case None{} _:
      {==}
    case Some{R.Item{+k, +p, B.At{0n, +c, +s}, +t}} True{}:
      {==}
    case Some{R.Item{+k, +p, B.At{0n, +c, +s}, +t}} False{}:
      {==}
    case Some{R.Item{+k, +p, B.At{1n+m, +c, +s}, +t}} _:
      {==}

# shiftS of a T that has not stopped, up to settle, reads T up to settle.
law shift_settle:
  for +c0: String
  for +sx: R.RunSt
  for +tx: R.RunSt
  for +hx: {R.RunSt.halt(tx) == False{} : Bool}
  {P.settle(SD.shiftS(c0, sx, P.settle(tx))) == P.settle(SD.shiftS(c0, sx, tx)) : R.RunSt}

def shift_settle(c0, sx, tx, hx):
  match sx tx:
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, False{}}:
      +same = R.is_cur(sc, c0)
      Equal.cong(Maybe<&2, R.Item>, R.RunSt, z => R.RunSt{Nat.add(sn, tn), True{}, sh, tc, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, R.push_cur(sc, se))), z, SD.items_shift(sn, tb), SD.cnt_add(sk, tk), String.append(so, String.append(SD.texts(sb), to)), sns, False{}},
        P.blank(SD.last_shift(P.blank(tl), same, sl, SD.last_item(sb), sn)), P.blank(SD.last_shift(tl, same, sl, SD.last_item(sb), sn)), ls_blank(tl, same, sl, SD.last_item(sb), sn))
    case R.RunSt{+sn, +si, +sh, +sc, +se, +sl, +sb, +sk, +so, +sns, +sxx} R.RunSt{+tn, +ti, +th, +tc, +te, +tl, +tb, +tk, +to, +tns, True{}}:
      Empty.absurd({P.settle(SD.shiftS(c0, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sxx}, P.settle(R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, True{}}))) == P.settle(SD.shiftS(c0, R.RunSt{sn, si, sh, sc, se, sl, sb, sk, so, sns, sxx}, R.RunSt{tn, ti, th, tc, te, tl, tb, tk, to, tns, True{}})) : R.RunSt}, PB.true_ne_false(hx))

# Runs from states equal up to settle stay equal up to settle
# ===========================================================

law settle_bl:
  for +st: R.RunSt
  {P.settle(P.blank_st(st)) == P.settle(st) : R.RunSt}

def settle_bl(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, None{}, +b, +k, +o, +ns, +x}:
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, Some{R.Item{+ik, +ip, +ia, +it}}, +b, +k, +o, +ns, True{}}:
      {==}
    case R.RunSt{+n, +i, +h, +c, +e, Some{R.Item{+ik, +ip, +ia, +it}}, +b, +k, +o, +ns, False{}}:
      {==}

law go_bl:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.RunSt
  for +z: R.RunSt
  for +h: {P.blank_st(y) == P.blank_st(z) : R.RunSt}
  {P.settle(L.run.go(ls, fa, o, y)) == P.settle(L.run.go(ls, fa, o, z)) : R.RunSt}

def go_bl(ls, fa, o, y, z, h):
  match ls:
    case Nil{}:
      Equal.trans(R.RunSt, P.settle(y), P.settle(P.blank_st(y)), P.settle(z), Equal.sym(R.RunSt, P.settle(P.blank_st(y)), P.settle(y), settle_bl(y)),
        Equal.trans(R.RunSt, P.settle(P.blank_st(y)), P.settle(P.blank_st(z)), P.settle(z), Equal.cong(R.RunSt, R.RunSt, q => P.settle(q), P.blank_st(y), P.blank_st(z), h), settle_bl(z)))
    case Con{+l, +t}:
      +Y = L.line_step(fa, o, y, l)
      +Z = L.line_step(fa, o, z, l)
      go_bl(t, fa, o, Y, Z,
        Equal.trans(R.RunSt, P.blank_st(Y), P.blank_st(L.line_step(fa, o, P.blank_st(y), l)), P.blank_st(Z), Equal.sym(R.RunSt, P.blank_st(L.line_step(fa, o, P.blank_st(y), l)), P.blank_st(Y), BL.step_bl(fa, o, y, l)),
          Equal.trans(R.RunSt, P.blank_st(L.line_step(fa, o, P.blank_st(y), l)), P.blank_st(L.line_step(fa, o, P.blank_st(z), l)), P.blank_st(Z),
            Equal.cong(R.RunSt, R.RunSt, q => P.blank_st(L.line_step(fa, o, q, l)), P.blank_st(y), P.blank_st(z), h), BL.step_bl(fa, o, z, l))))

law go_settle:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.RunSt
  for +z: R.RunSt
  for +h: {P.settle(y) == P.settle(z) : R.RunSt}
  {P.settle(L.run.go(ls, fa, o, y)) == P.settle(L.run.go(ls, fa, o, z)) : R.RunSt}

def go_settle(ls, fa, o, y, z, h):
  match y z:
    case R.RunSt{+n, +i, +hh, +c, +e, +l, +b, +k, +ot, +ns, False{}} R.RunSt{+n2, +i2, +hh2, +c2, +e2, +l2, +b2, +k2, +ot2, +ns2, False{}}:
      go_bl(ls, fa, o, R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, False{}}, R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, False{}}, h)
    case R.RunSt{+n, +i, +hh, +c, +e, +l, +b, +k, +ot, +ns, True{}} R.RunSt{+n2, +i2, +hh2, +c2, +e2, +l2, +b2, +k2, +ot2, +ns2, True{}}:
      +Y = {R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, True{}} : R.RunSt}
      +Z = {R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, True{}} : R.RunSt}
      %Equal.sym(R.RunSt, L.run.go(ls, fa, o, Y), Y, FRM.run_halted(ls, fa, o, Y, {==})) : {P.settle(_) == P.settle(L.run.go(ls, fa, o, Z)) : R.RunSt}
      %Equal.sym(R.RunSt, L.run.go(ls, fa, o, Z), Z, FRM.run_halted(ls, fa, o, Z, {==})) : {P.settle(Y) == P.settle(_) : R.RunSt}
      h
    case R.RunSt{+n, +i, +hh, +c, +e, +l, +b, +k, +ot, +ns, True{}} R.RunSt{+n2, +i2, +hh2, +c2, +e2, +l2, +b2, +k2, +ot2, +ns2, False{}}:
      Empty.absurd({P.settle(L.run.go(ls, fa, o, R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, True{}})) == P.settle(L.run.go(ls, fa, o, R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, False{}})) : R.RunSt},
        PB.true_ne_false(Equal.cong(R.RunSt, Bool, q => R.RunSt.halt(q), P.settle(R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, True{}}), P.settle(R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, False{}}), h)))
    case R.RunSt{+n, +i, +hh, +c, +e, +l, +b, +k, +ot, +ns, False{}} R.RunSt{+n2, +i2, +hh2, +c2, +e2, +l2, +b2, +k2, +ot2, +ns2, True{}}:
      Empty.absurd({P.settle(L.run.go(ls, fa, o, R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, False{}})) == P.settle(L.run.go(ls, fa, o, R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, True{}})) : R.RunSt},
        PB.false_ne_true(Equal.cong(R.RunSt, Bool, q => R.RunSt.halt(q), P.settle(R.RunSt{n, i, hh, c, e, l, b, k, ot, ns, False{}}), P.settle(R.RunSt{n2, i2, hh2, c2, e2, l2, b2, k2, ot2, ns2, True{}}), h)))
