import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./proof_window_defs.bend as WD
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN
import ./proof_machine_lines.bend as PL
import ./proof_machine_frame.bend as PF
import ./proof_machine_fasta.bend as PFa
import ./proof_machine_ask.bend as PA
import ./proof_machine_win.bend as W

# The machine proof: driving the machine (L.drive) is the spec (L.run).
#
# Between two driver steps the driver is in one of three states: More (the
# machine waits for input, its queue empty), Ask (a line waits for a reference
# read) or Finish. Good says what each state satisfies relative to a spec state
# S: the machine's bookkeeping is S cleared, the driver collected S's out and
# notes, and the report T is what the spec makes of the lines still to come
# from S. need counts the driver steps left; every step lowers it.

# Definitions
# ===========

# The lines still to come after the queue.
def rest_lines(e: Bool, +pend: String, +cs: List<&2, String>) -> List<&2, B.Line>:
  match e:
    case True{}:
      Nil{}
    case False{}:
      B.Text.lines(String.append(pend, String.concat(cs)))

# Driver steps one line may take at most: one per reference read.
def cost(+fasta: String) -> Nat:
  Nat.add(String.length(fasta), 3n)

def nlines(+pend: String, +cs: List<&2, String>) -> Nat:
  List.length(&2, B.Line, B.Text.lines(String.append(pend, String.concat(cs))))

# Driver steps for what comes after the queue: the pieces, the lines they hold,
# the end of the file, and stopping.
def rest_need(+cc: Nat, e: Bool, +pend: String, +cs: List<&2, String>) -> Nat:
  match e:
    case True{}:
      1n
    case False{}:
      2n+Nat.add(List.length(&2, String, cs), Nat.mul(nlines(pend, cs), cc))

def bud(+cc: Nat, +q: List<&2, B.Line>, +e: Bool, +pend: String, +cs: List<&2, String>) -> Nat:
  Nat.add(Nat.mul(List.length(&2, B.Line, q), cc), rest_need(cc, e, pend, cs))

# A line's window (Norm.want).
def lfs(+l: B.Line) -> List<&2, String>:
  B.Rec.fields(B.Line.body(l))

def lpos(+l: B.Line) -> Nat:
  Nat.sub(B.Rec.pos(lfs(l)), 1n)

def wchrom(+l: B.Line) -> String:
  B.Rec.field(lfs(l), 0n)

def wfrom(+l: B.Line, +back: Nat) -> Nat:
  Nat.sub(lpos(l), back)

def wupto(+l: B.Line) -> Nat:
  Nat.add(lpos(l), String.length(B.Rec.field(lfs(l), 3n)))

def clen_of(+fa: List<&2, B.Contig>, +l: B.Line) -> Nat:
  PFa.mlen(B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))))

# Reads a waiting line may still need after the one asked for: none once the
# window starts at the contig's first letter.
def asks0(+fa: List<&2, B.Contig>, +l: B.Line, +back: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(lpos(l), back), 0n, Nat.add(Nat.sub(clen_of(fa, l), back), 1n))

def need.more(st: Norm.St, +cc: Nat, e: Bool, +cs: List<&2, String>) -> Nat:
  match st:
    case Norm.St{o, rs, pend, q, e2, w}:
      rest_need(cc, e, pend, cs)

def need.ask(+fa: List<&2, B.Contig>, +cc: Nat, st: Norm.St, e: Bool, +cs: List<&2, String>) -> Nat:
  match st:
    case Norm.St{o, rs, pend, q, e2, None{}}:
      0n
    case Norm.St{o, rs, pend, q, e2, Some{Norm.Pending{l, back, fs}}}:
      1n+Nat.add(asks0(fa, l, back), bud(cc, q, e, pend, cs))

def need(+fa: List<&2, B.Contig>, +cc: Nat, d: L.DSt) -> Nat:
  match d:
    case L.DSt{st, nx, cs, e, out, notes, Some{c}}:
      0n
    case L.DSt{st, B.Finish{c}, cs, e, out, notes, None{}}:
      1n
    case L.DSt{st, B.More{}, cs, e, out, notes, None{}}:
      need.more(st, cc, e, cs)
    case L.DSt{st, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      need.ask(fa, cc, st, e, cs)

def GoodM(+fa: List<&2, B.Contig>, +T: R.Report, +o: B.Opts, +rs: R.RunSt, +pend: String, +cs: List<&2, String>, +out: String, +notes: List<&2, B.Note>) -> Type:
  &S: R.RunSt -> ({rs == Norm.RunSt.clear(S) : R.RunSt}
    & ({out == Norm.RunSt.out(S) : String}
    & ({notes == Norm.RunSt.notes(S) : List<&2, B.Note>}
    & ({PF.good(S) == True{} : Bool}
    & ({R.RunSt.halt(S) == False{} : Bool}
    & ({B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
    & {T == R.finish(L.run.go(B.Text.lines(String.append(pend, String.concat(cs))), fa, o, S)) : R.Report}))))))

def GoodA(+fa: List<&2, B.Contig>, +T: R.Report, +o: B.Opts, +rs: R.RunSt, +pend: String, +q: List<&2, B.Line>, +l: B.Line, +back: Nat, +fs: List<&2, String>,
  +ch: String, +a: Nat, +b: Nat, +cs: List<&2, String>, +e: Bool, +out: String, +notes: List<&2, B.Note>) -> Type:
  &S: R.RunSt -> ({rs == Norm.RunSt.clear(S) : R.RunSt}
    & ({out == Norm.RunSt.out(S) : String}
    & ({notes == Norm.RunSt.notes(S) : List<&2, B.Note>}
    & ({PF.good(S) == True{} : Bool}
    & ({R.RunSt.halt(S) == False{} : Bool}
    & ({R.RunSt.inbody(S) == True{} : Bool}
    & ({fs == B.Rec.fields(B.Line.body(l)) : List<&2, String>}
    & ({ch == wchrom(l) : String}
    & ({a == wfrom(l, back) : Nat}
    & ({b == wupto(l) : Nat}
    & ({B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
    & {T == R.finish(L.run.go(l <> List.append(&2, B.Line, q, rest_lines(e, pend, cs)), fa, o, S)) : R.Report})))))))))))

def GM(+fa: List<&2, B.Contig>, +T: R.Report, st: Norm.St, +cs: List<&2, String>, e: Bool, +out: String, +notes: List<&2, B.Note>) -> Type:
  match st:
    case Norm.St{o, rs, pend, q, e2, w}:
      match q:
        case x <> t:
          Empty
        case Nil{}:
          match e2:
            case True{}:
              Empty
            case False{}:
              match w:
                case Some{p}:
                  Empty
                case None{}:
                  match e:
                    case True{}:
                      Empty
                    case False{}:
                      GoodM(fa, T, o, rs, pend, cs, out, notes)

def GA(+fa: List<&2, B.Contig>, +T: R.Report, st: Norm.St, +ch: String, +a: Nat, +b: Nat, +cs: List<&2, String>, e: Bool, +out: String, +notes: List<&2, B.Note>) -> Type:
  match st:
    case Norm.St{o, rs, pend, q, e2, w}:
      match e2:
        case True{}:
          match w:
            case None{}:
              Empty
            case Some{Norm.Pending{l, back, fs}}:
              match e:
                case True{}:
                  GoodA(fa, T, o, rs, pend, q, l, back, fs, ch, a, b, cs, True{}, out, notes)
                case False{}:
                  Empty
        case False{}:
          match w:
            case None{}:
              Empty
            case Some{Norm.Pending{l, back, fs}}:
              match e:
                case True{}:
                  Empty
                case False{}:
                  GoodA(fa, T, o, rs, pend, q, l, back, fs, ch, a, b, cs, False{}, out, notes)

def Good(+fa: List<&2, B.Contig>, +T: R.Report, d: L.DSt) -> Type:
  match d:
    case L.DSt{st, nx, cs, e, out, notes, Some{c}}:
      {R.Report{out, notes, c} == T : R.Report}
    case L.DSt{st, B.Finish{c}, cs, e, out, notes, None{}}:
      {R.Report{out, notes, c} == T : R.Report}
    case L.DSt{st, B.More{}, cs, e, out, notes, None{}}:
      GM(fa, T, st, cs, e, out, notes)
    case L.DSt{st, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      GA(fa, T, st, ch, a, b, cs, e, out, notes)

# A good state with at most bud driver steps left.
def Ok(+fasta: String, +T: R.Report, +D: L.DSt, +bud: Nat) -> Type:
  Good(B.Fasta.parse(fasta), T, D) & {Nat.is_le(need(B.Fasta.parse(fasta), cost(fasta), D), bud) == True{} : Bool}

# A good state after one driver step from a state with nb steps left.
def StepOK(+fasta: String, +T: R.Report, +D: L.DSt, +nb: Nat) -> Type:
  Good(B.Fasta.parse(fasta), T, D) & {Nat.is_le(1n+need(B.Fasta.parse(fasta), cost(fasta), D), nb) == True{} : Bool}

# The driver state after pumping lines from a state with an empty wait.
def PD(+o: B.Opts, +rsm: R.RunSt, +pend: String, +q: List<&2, B.Line>, +e: Bool, +outs: List<&2, String>, +ns: List<&2, B.Note>,
  +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +f: Nat) -> L.DSt:
  L.absorb(Norm.pump(f, Norm.advance(Norm.St{o, rsm, pend, q, e, None{}}), outs, ns), cs, e, O, N)

# The machine's bookkeeping after a body line whose result is r.
def bl(+r: B.Res, +o: B.Opts, +S: R.RunSt, +l: B.Line) -> R.RunSt:
  +fs = B.Rec.fields(B.Line.body(l))
  +rs1 = R.tick(Norm.RunSt.clear(S))
  R.body_line(r, rs1, o, l, B.At{R.RunSt.n(rs1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

def mstep(+fa: List<&2, B.Contig>, +o: B.Opts, +S: R.RunSt, +l: B.Line) -> R.RunSt:
  bl(L.judge(fa, B.Line.body(l)), o, S, l)

# Small lemmas
# ============

law ok_weaken:
  for +fasta: String
  for +T: R.Report
  for +D: L.DSt
  for +b1: Nat
  for +b2: Nat
  for ok: Ok(fasta, T, D, b1)
  for +h: {Nat.is_le(b1, b2) == True{} : Bool}
  Ok(fasta, T, D, b2)

def ok_weaken(fasta, T, D, b1, b2, ok, h):
  match ok:
    case (g, e):
      (g, PN.le_trans(need(B.Fasta.parse(fasta), cost(fasta), D), b1, b2, e, h))

law ok_step:
  for +fasta: String
  for +T: R.Report
  for +D: L.DSt
  for +b: Nat
  for +nb: Nat
  for ok: Ok(fasta, T, D, b)
  for +h: {Nat.is_le(1n+b, nb) == True{} : Bool}
  StepOK(fasta, T, D, nb)

def ok_step(fasta, T, D, b, nb, ok, h):
  match ok:
    case (g, e):
      (g, PN.le_trans(1n+need(B.Fasta.parse(fasta), cost(fasta), D), 1n+b, nb, e, h))

law run_go_halted:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +S: R.RunSt
  for +hh: {R.RunSt.halt(S) == True{} : Bool}
  {L.run.go(ls, fa, o, S) == S : R.RunSt}

def run_go_halted(ls, fa, o, S, hh):
  match ls S:
    case Nil{} _:
      {==}
    case l <> t R.RunSt{n, i, h, c, e, la, b, k, so, sns, True{}}:
      run_go_halted(t, fa, o, R.RunSt{n, i, h, c, e, la, b, k, so, sns, True{}}, hh)
    case l <> t R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}}:
      Empty.absurd({L.run.go(l <> t, fa, o, R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}}) == R.RunSt{n, i, h, c, e, la, b, k, so, sns, False{}} : R.RunSt},
        P.false_ne_true(hh))

law rep_eq:
  for +o1: String
  for +o2: String
  for +n1: List<&2, B.Note>
  for +n2: List<&2, B.Note>
  for +c: Nat
  for eo: {o1 == o2 : String}
  for en: {n1 == n2 : List<&2, B.Note>}
  {R.Report{o1, n1, c} == R.Report{o2, n2, c} : R.Report}

def rep_eq(o1, o2, n1, n2, c, eo, en):
  %eo : {R.Report{o1, n1, c} == R.Report{_, n2, c} : R.Report}
  %en : {R.Report{o1, n1, c} == R.Report{o1, _, c} : R.Report}
  {==}

law rep_eta:
  for +r: R.Report
  {R.Report{R.Report.out(r), R.Report.notes(r), R.Report.code(r)} == r : R.Report}

def rep_eta(r):
  match r:
    case R.Report{o, n, c}:
      {==}

# What pump collects
# ==================

law rev_acc:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, xs, acc) == List.append(&2, A, List.reverse.go(&2, A, xs, Nil{}), acc) : List<&2, A>}

def rev_acc(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      +r = List.reverse.go(&2, A, t, Nil{})
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, [x]), List.append(&2, A, r, [x]), rev_acc(A, t, [x])) :
        {List.reverse.go(&2, A, t, x <> acc) == List.append(&2, A, _, acc) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, r, [x]), acc), List.append(&2, A, r, x <> acc),
        P.append_assoc(A, r, [x], acc)) :
        {List.reverse.go(&2, A, t, x <> acc) == _ : List<&2, A>}
      rev_acc(A, t, x <> acc)

law concat_snoc:
  for +xs: List<&2, String>
  for +x: String
  {String.concat(List.append(&2, String, xs, [x])) == String.append(String.concat(xs), x) : String}

def concat_snoc(xs, x):
  match xs:
    case Nil{}:
      PN.str_nil(x)
    case y <> t:
      %Equal.sym(String, String.concat(List.append(&2, String, t, [x])), String.append(String.concat(t), x), concat_snoc(t, x)) :
        {String.append(y, _) == String.append(String.append(y, String.concat(t)), x) : String}
      Equal.sym(String, String.append(String.append(y, String.concat(t)), x), String.append(y, String.append(String.concat(t), x)),
        PN.str_assoc(y, String.concat(t), x))

# Norm.cat is String.concat.
law cat_go:
  for +t: List<&2, String>
  for +h: String
  {Norm.cat.go(t, h) == String.append(h, String.concat(t)) : String}

def cat_go(t, h):
  match t:
    case Nil{}:
      Equal.sym(String, String.append(h, ""), h, PN.str_nil(h))
    case +y <> +t2:
      %Equal.sym(String, Norm.cat.go(t2, y), String.append(y, String.concat(t2)), cat_go(t2, y)) :
        {String.append(h, _) == String.append(h, String.append(y, String.concat(t2))) : String}
      {==}

law cat_eq:
  for +xs: List<&2, String>
  {Norm.cat(xs) == String.concat(xs) : String}

def cat_eq(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      cat_go(t, x)

law outs_cons:
  for +x: String
  for +outs: List<&2, String>
  {Norm.outs_text(x <> outs) == String.append(Norm.outs_text(outs), x) : String}

def outs_cons(x, outs):
  %Equal.sym(String, Norm.cat(List.reverse(&2, String, x <> outs)), String.concat(List.reverse(&2, String, x <> outs)), cat_eq(List.reverse(&2, String, x <> outs))) :
    {_ == String.append(Norm.outs_text(outs), x) : String}
  %Equal.sym(String, Norm.cat(List.reverse(&2, String, outs)), String.concat(List.reverse(&2, String, outs)), cat_eq(List.reverse(&2, String, outs))) :
    {String.concat(List.reverse(&2, String, x <> outs)) == String.append(_, x) : String}
  %Equal.sym(List<&2, String>, List.reverse.go(&2, String, outs, [x]), List.append(&2, String, List.reverse.go(&2, String, outs, Nil{}), [x]),
    rev_acc(String, outs, [x])) :
    {String.concat(_) == String.append(String.concat(List.reverse(&2, String, outs)), x) : String}
  concat_snoc(List.reverse.go(&2, String, outs, Nil{}), x)

law notes_rev:
  for +n: List<&2, B.Note>
  for +ns: List<&2, B.Note>
  {Norm.notes_list(Norm.rev_onto(n, ns)) == List.append(&2, B.Note, Norm.notes_list(ns), n) : List<&2, B.Note>}

def notes_rev(n, ns):
  match n:
    case Nil{}:
      Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, Norm.notes_list(ns), Nil{}), Norm.notes_list(ns), P.append_nil(B.Note, Norm.notes_list(ns)))
    case x <> t:
      +r = List.reverse.go(&2, B.Note, ns, Nil{})
      %Equal.sym(List<&2, B.Note>, Norm.notes_list(Norm.rev_onto(t, x <> ns)), List.append(&2, B.Note, Norm.notes_list(x <> ns), t), notes_rev(t, x <> ns)) :
        {_ == List.append(&2, B.Note, r, x <> t) : List<&2, B.Note>}
      %Equal.sym(List<&2, B.Note>, List.reverse.go(&2, B.Note, ns, [x]), List.append(&2, B.Note, r, [x]), rev_acc(B.Note, ns, [x])) :
        {List.append(&2, B.Note, _, t) == List.append(&2, B.Note, r, x <> t) : List<&2, B.Note>}
      P.append_assoc(B.Note, r, [x], t)

law HO:
  for +O: String
  for +outs: List<&2, String>
  for +x: String
  for +so: String
  for +hO: {String.append(O, Norm.outs_text(outs)) == so : String}
  {String.append(O, Norm.outs_text(x <> outs)) == String.append(so, x) : String}

def HO(O, outs, x, so, hO):
  %Equal.sym(String, Norm.outs_text(x <> outs), String.append(Norm.outs_text(outs), x), outs_cons(x, outs)) :
    {String.append(O, _) == String.append(so, x) : String}
  %PN.str_assoc(O, Norm.outs_text(outs), x) :
    {_ == String.append(so, x) : String}
  %Equal.sym(String, String.append(O, Norm.outs_text(outs)), so, hO) : {String.append(_, x) == String.append(so, x) : String}
  {==}

law HN:
  for +N: List<&2, B.Note>
  for +ns: List<&2, B.Note>
  for +n: List<&2, B.Note>
  for +sns: List<&2, B.Note>
  for +hN: {List.append(&2, B.Note, N, Norm.notes_list(ns)) == sns : List<&2, B.Note>}
  {List.append(&2, B.Note, N, Norm.notes_list(Norm.rev_onto(n, ns))) == List.append(&2, B.Note, sns, n) : List<&2, B.Note>}

def HN(N, ns, n, sns, hN):
  %Equal.sym(List<&2, B.Note>, Norm.notes_list(Norm.rev_onto(n, ns)), List.append(&2, B.Note, Norm.notes_list(ns), n), notes_rev(n, ns)) :
    {List.append(&2, B.Note, N, _) == List.append(&2, B.Note, sns, n) : List<&2, B.Note>}
  %P.append_assoc(B.Note, N, Norm.notes_list(ns), n) :
    {_ == List.append(&2, B.Note, sns, n) : List<&2, B.Note>}
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, N, Norm.notes_list(ns)), sns, hN) : {List.append(&2, B.Note, _, n) == List.append(&2, B.Note, sns, n) : List<&2, B.Note>}
  {==}

# One line in the spec
# ====================

law ib_tc:
  for +S: R.RunSt
  {R.RunSt.inbody(R.tick(Norm.RunSt.clear(S))) == R.RunSt.inbody(S) : Bool}

def ib_tc(S):
  match S:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      {==}

# A body line: the spec state after it is the machine's, with what was
# written before in front.
law LS_body:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +S: R.RunSt
  for +l: B.Line
  for +hh: {R.RunSt.halt(S) == False{} : Bool}
  for +hi: {R.RunSt.inbody(S) == True{} : Bool}
  {L.line_step(fa, o, S, l) == PF.pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), mstep(fa, o, S, l)) : R.RunSt}

def LS_body(fa, o, S, l, hh, hi):
  match S:
    case R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}}:
      Empty.absurd({L.line_step(fa, o, R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}}, l)
        == PF.pre(so, sns, mstep(fa, o, R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}}, l)) : R.RunSt}, P.true_ne_false(hh))
    case R.RunSt{n, False{}, h, c, ee, la, b, k, so, sns, False{}}:
      Empty.absurd({L.line_step(fa, o, R.RunSt{n, False{}, h, c, ee, la, b, k, so, sns, False{}}, l)
        == PF.pre(so, sns, mstep(fa, o, R.RunSt{n, False{}, h, c, ee, la, b, k, so, sns, False{}}, l)) : R.RunSt}, P.false_ne_true(hi))
    case R.RunSt{n, True{}, h, c, ee, la, b, k, so, sns, False{}}:
      +fs = B.Rec.fields(B.Line.body(l))
      +r = L.judge(fa, B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +tc = {R.RunSt{1n+n, True{}, h, c, ee, la, b, k, "", Nil{}, False{}} : R.RunSt}
      %PF.rs_eq(1n+n, True{}, h, c, ee, la, b, k, String.append(so, ""), so, List.append(&2, B.Note, sns, Nil{}), sns, False{},
        PN.str_nil(so), P.append_nil(B.Note, sns)) :
        {R.body_line(r, _, o, l, at, B.Rec.pos(fs)) == PF.pre(so, sns, R.body_line(r, tc, o, l, at, B.Rec.pos(fs))) : R.RunSt}
      PF.fr_body_line(r, so, sns, tc, o, l, at, B.Rec.pos(fs))

law good_head:
  for +isc: Bool
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +ee: List<&2, String>
  for +la: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: B.Opts
  for +l: B.Line
  {PF.good(R.head_line(isc, R.RunSt{1n+n, False{}, h, c, ee, la, b, k, "", Nil{}, False{}}, o, l)) == True{} : Bool}

def good_head(isc, n, h, c, ee, la, b, k, o, l):
  match isc l:
    case True{} B.Line{bd, term}:
      {==}
    case False{} _:
      {==}

# Arithmetic for the step counts
# ==============================

law bud_pos:
  for +cc: Nat
  for +q: List<&2, B.Line>
  for +e: Bool
  for +pend: String
  for +cs: List<&2, String>
  {Nat.is_le(1n, bud(cc, q, e, pend, cs)) == True{} : Bool}

def bud_pos(cc, q, e, pend, cs):
  match e:
    case True{}:
      PN.le_add_left(1n, Nat.mul(List.length(&2, B.Line, q), cc), 1n, {==})
    case False{}:
      PN.le_add_left(1n, Nat.mul(List.length(&2, B.Line, q), cc), rest_need(cc, False{}, pend, cs), {==})

law bud_cons:
  for +x: Nat
  for +cc: Nat
  for +rn: Nat
  {Nat.is_le(Nat.add(x, rn), Nat.add(Nat.add(cc, x), rn)) == True{} : Bool}

def bud_cons(x, cc, rn):
  P.le_add(x, Nat.add(cc, x), rn, rn, PN.le_add_left(x, cc, x, P.le_refl(x)), P.le_refl(rn))

law bud_assoc:
  for +cc: Nat
  for +x: Nat
  for +rn: Nat
  {Nat.is_le(Nat.add(cc, Nat.add(x, rn)), Nat.add(Nat.add(cc, x), rn)) == True{} : Bool}

def bud_assoc(cc, x, rn):
  %P.add_assoc(cc, x, rn) : {Nat.is_le(_, Nat.add(Nat.add(cc, x), rn)) == True{} : Bool}
  P.le_refl(Nat.add(Nat.add(cc, x), rn))

law sub_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}

def sub_le(a, b):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      P.le_refl(1n+p)
    case 1n+p 1n+q:
      PN.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), PN.le_succ(p))

law le_plus:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(1n+Nat.add(a, 1n), Nat.add(b, 3n)) == True{} : Bool}

def le_plus(a, b, h):
  match a b:
    case 0n _:
      PN.le_add_left(2n, b, 3n, {==})
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+Nat.add(p, 1n), 3n) == True{} : Bool}, P.false_ne_true(h))
    case 1n+p 1n+q:
      le_plus(p, q, h)

law askle.k:
  for +c: Bool
  for +x: Nat
  for +back: Nat
  for +m: Nat
  for +hx: {Nat.is_le(x, m) == True{} : Bool}
  {Nat.is_le(1n+Bool.pick(Nat, c, 0n, Nat.add(Nat.sub(x, back), 1n)), Nat.add(m, 3n)) == True{} : Bool}

def askle.k(c, x, back, m, hx):
  match c:
    case True{}:
      PN.le_add_left(1n, m, 3n, {==})
    case False{}:
      le_plus(Nat.sub(x, back), m, PN.le_trans(Nat.sub(x, back), x, m, sub_le(x, back), hx))

# A line's reads fit in what L.bound allows per line.
law askle:
  for +fasta: String
  for +l: B.Line
  for +back: Nat
  {Nat.is_le(1n+asks0(B.Fasta.parse(fasta), l, back), cost(fasta)) == True{} : Bool}

def askle(fasta, l, back):
  askle.k(Nat.is_le(lpos(l), back), clen_of(B.Fasta.parse(fasta), l), back, String.length(fasta),
    PFa.clen_le(fasta, WD.chrom_of(B.Line.body(l))))

# The end of the run
# ==================

law cat3:
  for +O: String
  for +ot: String
  for +o2: String
  for +so: String
  for +hO: {String.append(O, ot) == so : String}
  {String.append(O, String.append(ot, o2)) == String.append(so, o2) : String}

def cat3(O, ot, o2, so, hO):
  %PN.str_assoc(O, ot, o2) : {_ == String.append(so, o2) : String}
  %Equal.sym(String, String.append(O, ot), so, hO) : {String.append(_, o2) == String.append(so, o2) : String}
  {==}

law app3:
  for +N: List<&2, B.Note>
  for +nl: List<&2, B.Note>
  for +n2: List<&2, B.Note>
  for +sns: List<&2, B.Note>
  for +hN: {List.append(&2, B.Note, N, nl) == sns : List<&2, B.Note>}
  {List.append(&2, B.Note, N, List.append(&2, B.Note, nl, n2)) == List.append(&2, B.Note, sns, n2) : List<&2, B.Note>}

def app3(N, nl, n2, sns, hN):
  %P.append_assoc(B.Note, N, nl, n2) : {_ == List.append(&2, B.Note, sns, n2) : List<&2, B.Note>}
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, N, nl), sns, hN) : {List.append(&2, B.Note, _, n2) == List.append(&2, B.Note, sns, n2) : List<&2, B.Note>}
  {==}

law fin_k:
  for +fasta: String
  for +T: R.Report
  for +st: Norm.St
  for +f: R.Flush
  for +kc: R.Cnt
  for +so: String
  for +sns: List<&2, B.Note>
  for +outs: List<&2, String>
  for +ns: List<&2, B.Note>
  for +cs: List<&2, String>
  for +e: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +bd: Nat
  for +hO: {String.append(O, Norm.outs_text(outs)) == so : String}
  for +hN: {List.append(&2, B.Note, N, Norm.notes_list(ns)) == sns : List<&2, B.Note>}
  for +hT: {T == R.finish.flush(f, so, sns, kc) : R.Report}
  for +hb: {Nat.is_le(1n, bd) == True{} : Bool}
  Ok(fasta, T, L.absorb(Norm.finish.of(R.finish.flush(f, "", Nil{}, kc), st, outs, ns), cs, e, O, N), bd)

def fin_k(fasta, T, st, f, kc, so, sns, outs, ns, cs, e, O, N, bd, hO, hN, hT, hb):
  match f kc:
    case R.Broke{o2, bad, prev} _:
      +nt = {B.Stop{B.Unsorted{}, Some{bad}, prev} : B.Note}
      +ot = Norm.outs_text(outs)
      +nl = Norm.notes_list(ns)
      (Equal.trans(R.Report, R.Report{String.append(O, String.append(ot, o2)), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])), 1n},
        R.Report{String.append(so, o2), List.append(&2, B.Note, sns, [nt]), 1n}, T,
        rep_eq(String.append(O, String.append(ot, o2)), String.append(so, o2), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])),
          List.append(&2, B.Note, sns, [nt]), 1n, cat3(O, ot, o2, so, hO), app3(N, nl, [nt], sns, hN)),
        Equal.sym(R.Report, T, R.Report{String.append(so, o2), List.append(&2, B.Note, sns, [nt]), 1n}, hT)), hb)
    case R.Flushed{o2, l2} R.Cnt{n, ch, sk, wa}:
      +nt = {B.Summary{n, ch, sk, wa} : B.Note}
      +ot = Norm.outs_text(outs)
      +nl = Norm.notes_list(ns)
      (Equal.trans(R.Report, R.Report{String.append(O, String.append(ot, o2)), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])), 0n},
        R.Report{String.append(so, o2), List.append(&2, B.Note, sns, [nt]), 0n}, T,
        rep_eq(String.append(O, String.append(ot, o2)), String.append(so, o2), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])),
          List.append(&2, B.Note, sns, [nt]), 0n, cat3(O, ot, o2, so, hO), app3(N, nl, [nt], sns, hN)),
        Equal.sym(R.Report, T, R.Report{String.append(so, o2), List.append(&2, B.Note, sns, [nt]), 0n}, hT)), hb)

def FING(+fasta: String, +T: R.Report, +o: B.Opts, +S: R.RunSt, +pend: String, +q: List<&2, B.Line>, +e: Bool, +w: Maybe<&2, Norm.Pending>,
  +outs: List<&2, String>, +ns: List<&2, B.Note>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +bd: Nat) -> Type:
  Ok(fasta, T, L.absorb(Norm.finish(Norm.St{o, Norm.RunSt.clear(S), pend, q, e, w}, outs, ns), cs, e, O, N), bd)

# The machine finishing gives the spec's report.
law fin_ok:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +S: R.RunSt
  for +pend: String
  for +q: List<&2, B.Line>
  for +e: Bool
  for +w: Maybe<&2, Norm.Pending>
  for +outs: List<&2, String>
  for +ns: List<&2, B.Note>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +bd: Nat
  for +hO: {String.append(O, Norm.outs_text(outs)) == Norm.RunSt.out(S) : String}
  for +hN: {List.append(&2, B.Note, N, Norm.notes_list(ns)) == Norm.RunSt.notes(S) : List<&2, B.Note>}
  for +hg: {PF.good(S) == True{} : Bool}
  for +hT: {T == R.finish(S) : R.Report}
  for +hb: {Nat.is_le(1n, bd) == True{} : Bool}
  FING(fasta, T, o, S, pend, q, e, w, outs, ns, cs, O, N, bd)

def fin_ok(fasta, T, o, S, pend, q, e, w, outs, ns, cs, O, N, bd, hO, hN, hg, hT, hb):
  match S:
    case R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}}:
      +ot = Norm.outs_text(outs)
      +nl = Norm.notes_list(ns)
      (Equal.trans(R.Report, R.Report{String.append(O, String.append(ot, "")), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, Nil{})), 1n},
        R.Report{so, sns, 1n}, T,
        rep_eq(String.append(O, String.append(ot, "")), so, List.append(&2, B.Note, N, List.append(&2, B.Note, nl, Nil{})), sns, 1n,
          Equal.trans(String, String.append(O, String.append(ot, "")), String.append(O, ot), so,
            Equal.cong(String, String, x => String.append(O, x), String.append(ot, ""), ot, PN.str_nil(ot)), hO),
          Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, List.append(&2, B.Note, nl, Nil{})), List.append(&2, B.Note, N, nl), sns,
            Equal.cong(List<&2, B.Note>, List<&2, B.Note>, x => List.append(&2, B.Note, N, x), List.append(&2, B.Note, nl, Nil{}), nl, P.append_nil(B.Note, nl)), hN)),
        Equal.sym(R.Report, T, R.Report{so, sns, 1n}, hT)), hb)
    case R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, Nil{}, False{}}:
      +ot = Norm.outs_text(outs)
      +nl = Norm.notes_list(ns)
      +nt = {B.Stop{B.NoHeader{}, None{}, None{}} : B.Note}
      (Equal.trans(R.Report, R.Report{String.append(O, String.append(ot, "")), List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])), 1n},
        R.Report{"", [nt], 1n}, T,
        rep_eq(String.append(O, String.append(ot, "")), "", List.append(&2, B.Note, N, List.append(&2, B.Note, nl, [nt])), [nt], 1n,
          Equal.trans(String, String.append(O, String.append(ot, "")), String.append(O, ot), "",
            Equal.cong(String, String, x => String.append(O, x), String.append(ot, ""), ot, PN.str_nil(ot)), hO),
          app3(N, nl, [nt], Nil{}, hN)),
        Equal.sym(R.Report, T, R.Report{"", [nt], 1n}, hT)), hb)
    case R.RunSt{n, False{}, h, c, ee, la, b, k, SCon{x1, x2}, sns, False{}}:
      Empty.absurd(FING(fasta, T, o, R.RunSt{n, False{}, h, c, ee, la, b, k, SCon{x1, x2}, sns, False{}}, pend, q, e, w, outs, ns, cs, O, N, bd),
        P.false_ne_true(hg))
    case R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, y <> ys, False{}}:
      Empty.absurd(FING(fasta, T, o, R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, y <> ys, False{}}, pend, q, e, w, outs, ns, cs, O, N, bd),
        P.false_ne_true(hg))
    case R.RunSt{n, True{}, h, c, ee, la, b, k, so, sns, False{}}:
      fin_k(fasta, T, Norm.St{o, R.RunSt{n, True{}, h, c, ee, la, b, k, "", Nil{}, False{}}, pend, q, e, w}, R.flush(b, la), k, so, sns,
        outs, ns, cs, e, O, N, bd, hO, hN, hT, hb)

# One body line through try_line
# ==============================

def TLG(+fasta: String, +T: R.Report, +o: B.Opts, +m: Maybe<&2, B.Res>, +l: B.Line, +back: Nat, +t: List<&2, B.Line>, +S: R.RunSt, +g: Nat,
  +outs: List<&2, String>, +ns: List<&2, B.Note>, +pend: String, +cs: List<&2, String>, +e: Bool, +O: String, +N: List<&2, B.Note>, +K: Nat) -> Type:
  Ok(fasta, T, L.absorb(Norm.pump(1n+g, Norm.try_line(m, o, Norm.RunSt.clear(S), l, B.Rec.fields(B.Line.body(l)), back, pend, t, e), outs, ns), cs, e, O, N),
    Nat.add(K, bud(cost(fasta), t, e, pend, cs)))

# The driver state after a body line handled with r: pump goes on with the
# rest of the queue.
def WD(+o: B.Opts, +rsm: R.RunSt, +M: R.RunSt, +pend: String, +t: List<&2, B.Line>, +e: Bool, +outs: List<&2, String>, +ns: List<&2, B.Note>,
  +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +g: Nat) -> L.DSt:
  PD(o, rsm, pend, t, e, Norm.RunSt.out(M) <> outs, Norm.rev_onto(Norm.RunSt.notes(M), ns), cs, O, N, g)

# A body line: with a result (which the window law says is judge's), pump
# goes on as the spec (ih); without one, the machine asks for the window.
law TL:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +A: Maybe<&2, Pr.Ans>
  for +l: B.Line
  for +m: Maybe<&2, B.Res>
  for +hm: {Norm.judge_in(A, B.Line.body(l)) == m : Maybe<&2, B.Res>}
  for +htr: {WD.truthful(B.Fasta.parse(fasta), WD.chrom_of(B.Line.body(l)), A) == True{} : Bool}
  for +back: Nat
  for +t: List<&2, B.Line>
  for +S: R.RunSt
  for +g: Nat
  for +outs: List<&2, String>
  for +ns: List<&2, B.Note>
  for +pend: String
  for +cs: List<&2, String>
  for +e: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +hO: {String.append(O, Norm.outs_text(outs)) == Norm.RunSt.out(S) : String}
  for +hN: {List.append(&2, B.Note, N, Norm.notes_list(ns)) == Norm.RunSt.notes(S) : List<&2, B.Note>}
  for +hg: {PF.good(S) == True{} : Bool}
  for +hh: {R.RunSt.halt(S) == False{} : Bool}
  for +hi: {R.RunSt.inbody(S) == True{} : Bool}
  for +hp: {B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
  for +hT: {T == R.finish(L.run.go(l <> List.append(&2, B.Line, t, rest_lines(e, pend, cs)), B.Fasta.parse(fasta), o, S)) : R.Report}
  for +K: Nat
  for hnone: {Norm.judge_in(A, B.Line.body(l)) == None{} : Maybe<&2, B.Res>} -> {Nat.is_le(1n+asks0(B.Fasta.parse(fasta), l, back), K) == True{} : Bool}
  for ih: Ok(fasta, T, WD(o, Norm.RunSt.clear(PF.pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), mstep(B.Fasta.parse(fasta), o, S, l))),
    mstep(B.Fasta.parse(fasta), o, S, l), pend, t, e, outs, ns, cs, O, N, g), bud(cost(fasta), t, e, pend, cs))
  TLG(fasta, T, o, m, l, back, t, S, g, outs, ns, pend, cs, e, O, N, K)

def TL(fasta, T, o, A, l, m, hm, htr, back, t, S, g, outs, ns, pend, cs, e, O, N, hO, hN, hg, hh, hi, hp, hT, K, hnone, ih):
  match m:
    case Some{r}:
      +fa = B.Fasta.parse(fasta)
      +M1 = mstep(fa, o, S, l)
      +bt = bud(cost(fasta), t, e, pend, cs)
      %Equal.sym(B.Res, r, L.judge(fa, B.Line.body(l)), W.window(fa, B.Line.body(l), A, r, htr, hm)) :
        Ok(fasta, T, WD(o, Norm.RunSt.clear(bl(_, o, S, l)), bl(_, o, S, l), pend, t, e, outs, ns, cs, O, N, g), Nat.add(K, bt))
      %PF.clear_pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1) :
        Ok(fasta, T, WD(o, _, M1, pend, t, e, outs, ns, cs, O, N, g), Nat.add(K, bt))
      ok_weaken(fasta, T, WD(o, Norm.RunSt.clear(PF.pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1)), M1, pend, t, e, outs, ns, cs, O, N, g),
        bt, Nat.add(K, bt), ih, PN.le_add_left(bt, K, bt, P.le_refl(bt)))
    case None{}:
      match e:
        case True{}:
          +bt = bud(cost(fasta), t, True{}, pend, cs)
          ((S, ({==}, (hO, (hN, (hg, (hh, (hi, ({==}, ({==}, ({==}, ({==}, (hp, hT)))))))))))),
            P.le_add(1n+asks0(B.Fasta.parse(fasta), l, back), K, bt, bt, hnone(hm), P.le_refl(bt)))
        case False{}:
          +bt = bud(cost(fasta), t, False{}, pend, cs)
          ((S, ({==}, (hO, (hN, (hg, (hh, (hi, ({==}, ({==}, ({==}, ({==}, (hp, hT)))))))))))),
            P.le_add(1n+asks0(B.Fasta.parse(fasta), l, back), K, bt, bt, hnone(hm), P.le_refl(bt)))

# The pump: lines handled within one step
# =======================================

def PLG(+fasta: String, +T: R.Report, +o: B.Opts, +S: R.RunSt, +q: List<&2, B.Line>, +f: Nat, +outs: List<&2, String>, +ns: List<&2, B.Note>,
  +pend: String, +cs: List<&2, String>, +e: Bool, +O: String, +N: List<&2, B.Note>) -> Type:
  Ok(fasta, T, PD(o, Norm.RunSt.clear(S), pend, q, e, outs, ns, cs, O, N, f), bud(cost(fasta), q, e, pend, cs))

# Pumping the queue q from a machine whose bookkeeping is S cleared (with S's
# out and notes collected before) ends in a good state, within the queue's
# budget.
law PL:
  for +q: List<&2, B.Line>
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +S: R.RunSt
  for +f: Nat
  for +outs: List<&2, String>
  for +ns: List<&2, B.Note>
  for +pend: String
  for +cs: List<&2, String>
  for +e: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +hf: {Nat.is_le(1n+List.length(&2, B.Line, q), f) == True{} : Bool}
  for +hO: {String.append(O, Norm.outs_text(outs)) == Norm.RunSt.out(S) : String}
  for +hN: {List.append(&2, B.Note, N, Norm.notes_list(ns)) == Norm.RunSt.notes(S) : List<&2, B.Note>}
  for +hg: {PF.good(S) == True{} : Bool}
  for +hp: {B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
  for +hT: {T == R.finish(L.run.go(List.append(&2, B.Line, q, rest_lines(e, pend, cs)), B.Fasta.parse(fasta), o, S)) : R.Report}
  PLG(fasta, T, o, S, q, f, outs, ns, pend, cs, e, O, N)

def PL(q, fasta, T, o, S, f, outs, ns, pend, cs, e, O, N, hf, hO, hN, hg, hp, hT):
  match q S f:
    case _ _ 0n:
      Empty.absurd(PLG(fasta, T, o, S, q, 0n, outs, ns, pend, cs, e, O, N), P.false_ne_true(hf))
    case _ R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}} 1n+g:
      +Sl = {R.RunSt{n, i, h, c, ee, la, b, k, so, sns, True{}} : R.RunSt}
      +fa = B.Fasta.parse(fasta)
      +ls = List.append(&2, B.Line, q, rest_lines(e, pend, cs))
      fin_ok(fasta, T, o, Sl, pend, q, e, None{}, outs, ns, cs, O, N, bud(cost(fasta), q, e, pend, cs), hO, hN, hg,
        Equal.trans(R.Report, T, R.finish(L.run.go(ls, fa, o, Sl)), R.finish(Sl), hT,
          Equal.cong(R.RunSt, R.Report, x => R.finish(x), L.run.go(ls, fa, o, Sl), Sl, run_go_halted(ls, fa, o, Sl, {==}))),
        bud_pos(cost(fasta), q, e, pend, cs))
    case Nil{} R.RunSt{n, i, h, c, ee, la, b, k, so, sns, False{}} 1n+g:
      match e:
        case True{}:
          fin_ok(fasta, T, o, R.RunSt{n, i, h, c, ee, la, b, k, so, sns, False{}}, pend, Nil{}, True{}, None{}, outs, ns, cs, O, N,
            bud(cost(fasta), Nil{}, True{}, pend, cs), hO, hN, hg, hT, bud_pos(cost(fasta), Nil{}, True{}, pend, cs))
        case False{}:
          ((R.RunSt{n, i, h, c, ee, la, b, k, so, sns, False{}}, ({==}, (hO, (hN, (hg, ({==}, (hp, hT))))))),
            P.le_refl(rest_need(cost(fasta), False{}, pend, cs)))
    case l <> t R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, Nil{}, False{}} 1n+g:
      +S0 = {R.RunSt{n, False{}, h, c, ee, la, b, k, "", Nil{}, False{}} : R.RunSt}
      +S1 = R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(S0), o, l)
      +cc = cost(fasta)
      ih = PL(t, fasta, T, o, S1, g, Norm.RunSt.out(S1) <> outs, Norm.rev_onto(Norm.RunSt.notes(S1), ns), pend, cs, e, O, N,
        hf, HO(O, outs, Norm.RunSt.out(S1), "", hO), HN(N, ns, Norm.RunSt.notes(S1), Nil{}, hN),
        good_head(R.is_chrom_line(B.Line.body(l)), n, h, c, ee, la, b, k, o, l), hp, hT)
      ok_weaken(fasta, T, WD(o, Norm.RunSt.clear(S1), S1, pend, t, e, outs, ns, cs, O, N, g),
        bud(cc, t, e, pend, cs), bud(cc, l <> t, e, pend, cs), ih,
        bud_cons(Nat.mul(List.length(&2, B.Line, t), cc), cc, rest_need(cc, e, pend, cs)))
    case l <> t R.RunSt{n, False{}, h, c, ee, la, b, k, SCon{x1, x2}, sns, False{}} 1n+g:
      Empty.absurd(PLG(fasta, T, o, R.RunSt{n, False{}, h, c, ee, la, b, k, SCon{x1, x2}, sns, False{}}, l <> t, 1n+g, outs, ns, pend, cs, e, O, N),
        P.false_ne_true(hg))
    case l <> t R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, y <> ys, False{}} 1n+g:
      Empty.absurd(PLG(fasta, T, o, R.RunSt{n, False{}, h, c, ee, la, b, k, SNil{}, y <> ys, False{}}, l <> t, 1n+g, outs, ns, pend, cs, e, O, N),
        P.false_ne_true(hg))
    case l <> t R.RunSt{n, True{}, h, c, ee, la, b, k, so, sns, False{}} 1n+g:
      +fa = B.Fasta.parse(fasta)
      +Sl = {R.RunSt{n, True{}, h, c, ee, la, b, k, so, sns, False{}} : R.RunSt}
      +M1 = mstep(fa, o, Sl, l)
      +S2 = PF.pre(so, sns, M1)
      +rest = rest_lines(e, pend, cs)
      +cc = cost(fasta)
      +fs = B.Rec.fields(B.Line.body(l))
      +tc = R.tick(Norm.RunSt.clear(Sl))
      ih = PL(t, fasta, T, o, S2, g, Norm.RunSt.out(M1) <> outs, Norm.rev_onto(Norm.RunSt.notes(M1), ns), pend, cs, e, O, N,
        hf,
        Equal.trans(String, String.append(O, Norm.outs_text(Norm.RunSt.out(M1) <> outs)), String.append(so, Norm.RunSt.out(M1)), Norm.RunSt.out(S2),
          HO(O, outs, Norm.RunSt.out(M1), so, hO),
          Equal.sym(String, Norm.RunSt.out(S2), String.append(so, Norm.RunSt.out(M1)), PF.out_pre(so, sns, M1))),
        Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, Norm.notes_list(Norm.rev_onto(Norm.RunSt.notes(M1), ns))),
          List.append(&2, B.Note, sns, Norm.RunSt.notes(M1)), Norm.RunSt.notes(S2),
          HN(N, ns, Norm.RunSt.notes(M1), sns, hN),
          Equal.sym(List<&2, B.Note>, Norm.RunSt.notes(S2), List.append(&2, B.Note, sns, Norm.RunSt.notes(M1)), PF.notes_pre(so, sns, M1))),
        PF.good_pre(so, sns, M1,
          PF.ib_body_line(L.judge(fa, B.Line.body(l)), tc, o, l, B.At{R.RunSt.n(tc), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))),
        hp,
        Equal.trans(R.Report, T, R.finish(L.run.go(List.append(&2, B.Line, t, rest), fa, o, L.line_step(fa, o, Sl, l))),
          R.finish(L.run.go(List.append(&2, B.Line, t, rest), fa, o, S2)), hT,
          Equal.cong(R.RunSt, R.Report, x => R.finish(L.run.go(List.append(&2, B.Line, t, rest), fa, o, x)), L.line_step(fa, o, Sl, l), S2,
            LS_body(fa, o, Sl, l, {==}, {==}))))
      +jm = Norm.judge_in(None{}, B.Line.body(l))
      ok_weaken(fasta, T, L.absorb(Norm.pump(1n+g, Norm.try_line(jm, o, Norm.RunSt.clear(Sl), l, B.Rec.fields(B.Line.body(l)), 100n, pend, t, e), outs, ns), cs, e, O, N),
        Nat.add(cc, bud(cc, t, e, pend, cs)), bud(cc, l <> t, e, pend, cs),
        TL(fasta, T, o, None{}, l, jm, {==}, {==}, 100n, t, Sl, g, outs, ns, pend, cs, e, O, N, hO, hN, hg, {==}, {==}, hp, hT, cc,
          x => askle(fasta, l, 100n), ih),
        bud_assoc(cc, Nat.mul(List.length(&2, B.Line, t), cc), rest_need(cc, e, pend, cs)))

# A failed read: the window was not enough, so the reads left go down
# ==================================================================

def A0(+fa: List<&2, B.Contig>, +l: B.Line, +back: Nat) -> Maybe<&2, Pr.Ans>:
  Some{M.truth(fa, wchrom(l), wfrom(l, back), wupto(l))}

law some_none:
  for +x: Maybe<&2, B.Res>
  for +hn: {x == None{} : Maybe<&2, B.Res>}
  for +hs: {Maybe.is_some(&2, B.Res, x) == True{} : Bool}
  Empty

def some_none(x, hn, hs):
  match x:
    case None{}:
      P.false_ne_true(hs)
    case Some{r}:
      P.true_ne_false(Equal.cong(Maybe<&2, B.Res>, Bool, y => Maybe.is_some(&2, B.Res, y), Some{r}, None{}, hn))

law no_enough:
  for +fasta: String
  for +l: B.Line
  for +A: Maybe<&2, Pr.Ans>
  for +hn: {Norm.judge_in(A, B.Line.body(l)) == None{} : Maybe<&2, B.Res>}
  for +htr: {WD.truthful(B.Fasta.parse(fasta), WD.chrom_of(B.Line.body(l)), A) == True{} : Bool}
  for +he: {WD.enough(B.Fasta.parse(fasta), B.Line.body(l), A) == True{} : Bool}
  Empty

def no_enough(fasta, l, A, hn, htr, he):
  some_none(Norm.judge_in(A, B.Line.body(l)), hn, W.window_enough(B.Fasta.parse(fasta), B.Line.body(l), A, htr, he))

law okz:
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  for +back: Nat
  for +hle: {Nat.is_le(lpos(l), back) == True{} : Bool}
  {PA.ans_ok(B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))), A0(fa, l, back), wupto(l)) == True{} : Bool}

def okz(fa, l, back, hle):
  +m = B.Fasta.find(fa, WD.chrom_of(B.Line.body(l)))
  %Equal.sym(Nat, wfrom(l, back), 0n, PA.sub_le_zero(lpos(l), back, hle)) :
    {PA.ans_ok(m, Some{M.truth.of(m, _, wupto(l))}, wupto(l)) == True{} : Bool}
  PA.ok_zero(m, wupto(l))

law okn:
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  for +back: Nat
  for +hm: {B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))) == None{} : Maybe<&2, String>}
  {PA.ans_ok(B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))), A0(fa, l, back), wupto(l)) == True{} : Bool}

def okn(fa, l, back, hm):
  %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))), None{}, hm) :
    {PA.ans_ok(_, Some{M.truth.of(_, wfrom(l, back), wupto(l))}, wupto(l)) == True{} : Bool}
  {==}

law sub_gt:
  for +c: Nat
  for +b: Nat
  for +h: {Nat.is_le(c, b) == False{} : Bool}
  {Nat.sub(c, b) == 1n+Nat.sub(c, 1n+b) : Nat}

def sub_gt(c, b, h):
  match c b:
    case 0n _:
      Empty.absurd({Nat.sub(0n, b) == 1n+Nat.sub(0n, 1n+b) : Nat},
        P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, P.le_zero_l(b)), h)))
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, P.sub_zero(p)) : {1n+p == 1n+_ : Nat}
      {==}
    case 1n+p 1n+q:
      sub_gt(p, q, h)

law sub_anti:
  for +c: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.is_le(Nat.sub(c, y), Nat.sub(c, x)) == True{} : Bool}

def sub_anti(c, x, y, h):
  match c x y:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      sub_le(1n+p, y)
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, 0n), Nat.sub(p, q)) == True{} : Bool}, P.false_ne_true(h))
    case 1n+p 1n+q 1n+r:
      sub_anti(p, q, r, h)

law le_b2:
  for +b: Nat
  {Nat.is_le(1n+b, Nat.add(Nat.mul(b, 2n), 1n)) == True{} : Bool}

def le_b2(b):
  match b:
    case 0n:
      {==}
    case 1n+q:
      PN.le_trans(q, 1n+q, Nat.add(Nat.mul(q, 2n), 1n), PN.le_succ(q), le_b2(q))

law arith2:
  for +c: Nat
  for +b: Nat
  for +hw: {Nat.is_le(c, b) == False{} : Bool}
  {Nat.is_le(1n+Nat.add(Nat.sub(c, Nat.add(Nat.mul(b, 2n), 1n)), 1n), Nat.add(Nat.sub(c, b), 1n)) == True{} : Bool}

def arith2(c, b, hw):
  +b2 = Nat.add(Nat.mul(b, 2n), 1n)
  %Equal.sym(Nat, Nat.sub(c, b), 1n+Nat.sub(c, 1n+b), sub_gt(c, b, hw)) :
    {Nat.is_le(1n+Nat.add(Nat.sub(c, b2), 1n), Nat.add(_, 1n)) == True{} : Bool}
  P.le_add(Nat.sub(c, b2), Nat.sub(c, 1n+b), 1n, 1n, sub_anti(c, 1n+b, b2, le_b2(b)), {==})

law askdec.d:
  for +c: Nat
  for +back: Nat
  for +v: Bool
  for +hw: {Nat.is_le(c, back) == False{} : Bool}
  {Nat.is_le(1n+Bool.pick(Nat, v, 0n, Nat.add(Nat.sub(c, Nat.add(Nat.mul(back, 2n), 1n)), 1n)), Nat.add(Nat.sub(c, back), 1n)) == True{} : Bool}

def askdec.d(c, back, v, hw):
  match v:
    case True{}:
      PN.le_add_left(1n, Nat.sub(c, back), 1n, {==})
    case False{}:
      arith2(c, back, hw)

law askdec.c:
  for +l: B.Line
  for +back: Nat
  for +c: Nat
  for +w: Bool
  for +hw: {Nat.is_le(c, back) == w : Bool}
  {Nat.is_le(1n+Bool.pick(Nat, Nat.is_le(lpos(l), Norm.grow.if(w, back, l)), 0n, Nat.add(Nat.sub(c, Norm.grow.if(w, back, l)), 1n)),
    Nat.add(Nat.sub(c, back), 1n)) == True{} : Bool}

def askdec.c(l, back, c, w, hw):
  match w:
    case True{}:
      +p1 = B.Rec.pos(lfs(l))
      %Equal.sym(Bool, Nat.is_le(Nat.sub(p1, 1n), p1), True{}, sub_le(p1, 1n)) :
        {Nat.is_le(1n+Bool.pick(Nat, _, 0n, Nat.add(Nat.sub(c, p1), 1n)), Nat.add(Nat.sub(c, back), 1n)) == True{} : Bool}
      PN.le_add_left(1n, Nat.sub(c, back), 1n, {==})
    case False{}:
      askdec.d(c, back, Nat.is_le(lpos(l), Nat.add(Nat.mul(back, 2n), 1n)), hw)

def ADG(+fa: List<&2, B.Contig>, +l: B.Line, +back: Nat) -> Type:
  {Nat.is_le(1n+asks0(fa, l, Norm.grow(A0(fa, l, back), back, l)), Nat.add(Nat.sub(clen_of(fa, l), back), 1n)) == True{} : Bool}

law askdec.b:
  for +fasta: String
  for +l: B.Line
  for +back: Nat
  for +mf: Maybe<&2, String>
  for +hm: {B.Fasta.find(B.Fasta.parse(fasta), WD.chrom_of(B.Line.body(l))) == mf : Maybe<&2, String>}
  for +hn: {Norm.judge_in(A0(B.Fasta.parse(fasta), l, back), B.Line.body(l)) == None{} : Maybe<&2, B.Res>}
  ADG(B.Fasta.parse(fasta), l, back)

def askdec.b(fasta, l, back, mf, hm, hn):
  match mf:
    case None{}:
      +fa = B.Fasta.parse(fasta)
      +a = A0(fa, l, back)
      Empty.absurd(ADG(fa, l, back),
        no_enough(fasta, l, a, hn, PA.truthful_truth(fa, wchrom(l), wfrom(l, back), wupto(l)), PA.E_main(fa, B.Line.body(l), a, okn(fa, l, back, hm))))
    case Some{r}:
      +fa = B.Fasta.parse(fasta)
      +f = wfrom(l, back)
      +u = wupto(l)
      %Equal.sym(Maybe<&2, String>, B.Fasta.find(fa, WD.chrom_of(B.Line.body(l))), Some{r}, hm) :
        {Nat.is_le(1n+Bool.pick(Nat, Nat.is_le(lpos(l), Norm.grow(Some{M.truth.of(_, f, u)}, back, l)), 0n,
          Nat.add(Nat.sub(PFa.mlen(_), Norm.grow(Some{M.truth.of(_, f, u)}, back, l)), 1n)), Nat.add(Nat.sub(PFa.mlen(_), back), 1n)) == True{} : Bool}
      askdec.c(l, back, String.length(r), Nat.is_le(String.length(r), back), {==})

law askdec.a:
  for +fasta: String
  for +l: B.Line
  for +back: Nat
  for +le: Bool
  for +hle: {Nat.is_le(lpos(l), back) == le : Bool}
  for +hn: {Norm.judge_in(A0(B.Fasta.parse(fasta), l, back), B.Line.body(l)) == None{} : Maybe<&2, B.Res>}
  {Nat.is_le(1n+asks0(B.Fasta.parse(fasta), l, Norm.grow(A0(B.Fasta.parse(fasta), l, back), back, l)), Bool.pick(Nat, le, 0n,
    Nat.add(Nat.sub(clen_of(B.Fasta.parse(fasta), l), back), 1n))) == True{} : Bool}

def askdec.a(fasta, l, back, le, hle, hn):
  match le:
    case True{}:
      +fa = B.Fasta.parse(fasta)
      +a = A0(fa, l, back)
      Empty.absurd({Nat.is_le(1n+asks0(fa, l, Norm.grow(a, back, l)), 0n) == True{} : Bool},
        no_enough(fasta, l, a, hn, PA.truthful_truth(fa, wchrom(l), wfrom(l, back), wupto(l)), PA.E_main(fa, B.Line.body(l), a, okz(fa, l, back, hle))))
    case False{}:
      askdec.b(fasta, l, back, B.Fasta.find(B.Fasta.parse(fasta), WD.chrom_of(B.Line.body(l))), {==}, hn)

# A read that gives no result leaves fewer reads to come.
law askdec:
  for +fasta: String
  for +l: B.Line
  for +back: Nat
  for +hn: {Norm.judge_in(A0(B.Fasta.parse(fasta), l, back), B.Line.body(l)) == None{} : Maybe<&2, B.Res>}
  {Nat.is_le(1n+asks0(B.Fasta.parse(fasta), l, Norm.grow(A0(B.Fasta.parse(fasta), l, back), back, l)), asks0(B.Fasta.parse(fasta), l, back)) == True{} : Bool}

def askdec(fasta, l, back, hn):
  askdec.a(fasta, l, back, Nat.is_le(lpos(l), back), {==}, hn)

# A driver step from an Ask state
# ===============================

def AskG(+fasta: String, +T: R.Report, +o: B.Opts, +rs: R.RunSt, +pend: String, +q: List<&2, B.Line>, +e: Bool, +l: B.Line, +back: Nat, +fs: List<&2, String>,
  +ch: String, +a: Nat, +b: Nat, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>) -> Type:
  +d = {L.DSt{Norm.St{o, rs, pend, q, e, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, e, O, N, None{}} : L.DSt}
  StepOK(fasta, T, L.dstep(B.Fasta.parse(fasta), d), need(B.Fasta.parse(fasta), cost(fasta), d))

def AD(+f: Nat, +st: Norm.St, +a: Maybe<&2, Pr.Ans>, +cs: List<&2, String>, +e: Bool, +O: String, +N: List<&2, B.Note>) -> L.DSt:
  L.absorb(Norm.pump(f, Norm.resolve(st, a), Nil{}, Nil{}), cs, e, O, N)

law add2:
  for +x: Nat
  {Nat.add(x, 2n) == 2n+x : Nat}

def add2(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add2(p) : {1n+Nat.add(p, 2n) == 1n+_ : Nat}
      {==}

law AS.k:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +S: R.RunSt
  for +pend: String
  for +q: List<&2, B.Line>
  for +e: Bool
  for +l: B.Line
  for +back: Nat
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +hO: {O == Norm.RunSt.out(S) : String}
  for +hN: {N == Norm.RunSt.notes(S) : List<&2, B.Note>}
  for +hg: {PF.good(S) == True{} : Bool}
  for +hh: {R.RunSt.halt(S) == False{} : Bool}
  for +hi: {R.RunSt.inbody(S) == True{} : Bool}
  for +hp: {B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
  for +hT: {T == R.finish(L.run.go(l <> List.append(&2, B.Line, q, rest_lines(e, pend, cs)), B.Fasta.parse(fasta), o, S)) : R.Report}
  AskG(fasta, T, o, Norm.RunSt.clear(S), pend, q, e, l, back, B.Rec.fields(B.Line.body(l)), wchrom(l), wfrom(l, back), wupto(l), cs, O, N)

def AS.k(fasta, T, o, S, pend, q, e, l, back, cs, O, N, hO, hN, hg, hh, hi, hp, hT):
  +fa = B.Fasta.parse(fasta)
  +cc = cost(fasta)
  +a0 = A0(fa, l, back)
  +st = {Norm.St{o, Norm.RunSt.clear(S), pend, q, e, Some{Norm.Pending{l, back, B.Rec.fields(B.Line.body(l))}}} : Norm.St}
  +d = {L.DSt{st, B.Ask{wchrom(l), wfrom(l, back), wupto(l)}, cs, e, O, N, None{}} : L.DSt}
  +nb = need(fa, cc, d)
  +nq = List.length(&2, B.Line, q)
  +M1 = mstep(fa, o, S, l)
  +S2 = PF.pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1)
  +rest = rest_lines(e, pend, cs)
  +fs = B.Rec.fields(B.Line.body(l))
  +tc = R.tick(Norm.RunSt.clear(S))
  +hO1 = Equal.trans(String, String.append(O, ""), O, Norm.RunSt.out(S), PN.str_nil(O), hO)
  +hN1 = Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, Nil{}), N, Norm.RunSt.notes(S), P.append_nil(B.Note, N), hN)
  ih = PL(q, fasta, T, o, S2, 1n+nq, Norm.RunSt.out(M1) <> Nil{}, Norm.rev_onto(Norm.RunSt.notes(M1), Nil{}), pend, cs, e, O, N,
    P.le_refl(1n+nq),
    Equal.trans(String, String.append(O, Norm.outs_text(Norm.RunSt.out(M1) <> Nil{})), String.append(Norm.RunSt.out(S), Norm.RunSt.out(M1)), Norm.RunSt.out(S2),
      HO(O, Nil{}, Norm.RunSt.out(M1), Norm.RunSt.out(S), hO1),
      Equal.sym(String, Norm.RunSt.out(S2), String.append(Norm.RunSt.out(S), Norm.RunSt.out(M1)), PF.out_pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1))),
    Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, Norm.notes_list(Norm.rev_onto(Norm.RunSt.notes(M1), Nil{}))),
      List.append(&2, B.Note, Norm.RunSt.notes(S), Norm.RunSt.notes(M1)), Norm.RunSt.notes(S2),
      HN(N, Nil{}, Norm.RunSt.notes(M1), Norm.RunSt.notes(S), hN1),
      Equal.sym(List<&2, B.Note>, Norm.RunSt.notes(S2), List.append(&2, B.Note, Norm.RunSt.notes(S), Norm.RunSt.notes(M1)),
        PF.notes_pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1))),
    PF.good_pre(Norm.RunSt.out(S), Norm.RunSt.notes(S), M1,
      Equal.trans(Bool, R.RunSt.inbody(M1), R.RunSt.inbody(tc), True{},
        PF.ib_body_line(L.judge(fa, B.Line.body(l)), tc, o, l, B.At{R.RunSt.n(tc), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)),
        Equal.trans(Bool, R.RunSt.inbody(tc), R.RunSt.inbody(S), True{}, ib_tc(S), hi))),
    hp,
    Equal.trans(R.Report, T, R.finish(L.run.go(List.append(&2, B.Line, q, rest), fa, o, L.line_step(fa, o, S, l))),
      R.finish(L.run.go(List.append(&2, B.Line, q, rest), fa, o, S2)), hT,
      Equal.cong(R.RunSt, R.Report, x => R.finish(L.run.go(List.append(&2, B.Line, q, rest), fa, o, x)), L.line_step(fa, o, S, l), S2,
        LS_body(fa, o, S, l, hh, hi))))
  %Equal.sym(Nat, Nat.add(nq, 2n), 2n+nq, add2(nq)) : StepOK(fasta, T, AD(_, st, a0, cs, e, O, N), nb)
  +jm = Norm.judge_in(a0, B.Line.body(l))
  +g2 = Norm.grow(a0, back, l)
  +k0 = asks0(fa, l, back)
  ok_step(fasta, T, L.absorb(Norm.pump(2n+nq, Norm.try_line(jm, o, Norm.RunSt.clear(S), l, B.Rec.fields(B.Line.body(l)), g2, pend, q, e), Nil{}, Nil{}), cs, e, O, N),
    Nat.add(k0, bud(cc, q, e, pend, cs)), nb,
    TL(fasta, T, o, a0, l, jm, {==}, PA.truthful_truth(fa, wchrom(l), wfrom(l, back), wupto(l)), g2, q, S, 1n+nq, Nil{}, Nil{}, pend, cs, e, O, N,
      hO1, hN1, hg, hh, hi, hp, hT, k0, hn => askdec(fasta, l, back, hn), ih),
    P.le_refl(nb))

law AS:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +rs: R.RunSt
  for +pend: String
  for +q: List<&2, B.Line>
  for +e: Bool
  for +l: B.Line
  for +back: Nat
  for +ch: String
  for +a: Nat
  for +b: Nat
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +fs: List<&2, String>
  for ga: GoodA(B.Fasta.parse(fasta), T, o, rs, pend, q, l, back, fs, ch, a, b, cs, e, O, N)
  AskG(fasta, T, o, rs, pend, q, e, l, back, fs, ch, a, b, cs, O, N)

def AS(fasta, T, o, rs, pend, q, e, l, back, ch, a, b, cs, O, N, fs, ga):
  match ga:
    case (S, (hrs, (hO, (hN, (hg, (hh, (hi, (hfs, (hch, (ha, (hb, (hp, hT)))))))))))):
      %Equal.sym(R.RunSt, rs, Norm.RunSt.clear(S), hrs) : AskG(fasta, T, o, _, pend, q, e, l, back, fs, ch, a, b, cs, O, N)
      %Equal.sym(List<&2, String>, fs, B.Rec.fields(B.Line.body(l)), hfs) : AskG(fasta, T, o, Norm.RunSt.clear(S), pend, q, e, l, back, _, ch, a, b, cs, O, N)
      %Equal.sym(String, ch, wchrom(l), hch) : AskG(fasta, T, o, Norm.RunSt.clear(S), pend, q, e, l, back, B.Rec.fields(B.Line.body(l)), _, a, b, cs, O, N)
      %Equal.sym(Nat, a, wfrom(l, back), ha) : AskG(fasta, T, o, Norm.RunSt.clear(S), pend, q, e, l, back, B.Rec.fields(B.Line.body(l)), wchrom(l), _, b, cs, O, N)
      %Equal.sym(Nat, b, wupto(l), hb) : AskG(fasta, T, o, Norm.RunSt.clear(S), pend, q, e, l, back, B.Rec.fields(B.Line.body(l)), wchrom(l), wfrom(l, back), _, cs, O, N)
      AS.k(fasta, T, o, S, pend, q, e, l, back, cs, O, N, hO, hN, hg, hh, hi, hp, hT)

# A driver step from a More state
# ===============================

def MoreG(+fasta: String, +T: R.Report, +o: B.Opts, +rs: R.RunSt, +pend: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>) -> Type:
  +d = {L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, False{}, O, N, None{}} : L.DSt}
  StepOK(fasta, T, L.dstep(B.Fasta.parse(fasta), d), need(B.Fasta.parse(fasta), cost(fasta), d))

def CD(+fv: Norm.Fed, +o: B.Opts, +rs: R.RunSt, +t: List<&2, String>, +O: String, +N: List<&2, B.Note>) -> L.DSt:
  +st = {Norm.St{o, rs, "", Nil{}, False{}, None{}} : Norm.St}
  L.absorb(Norm.pump(Norm.St.fuel(Norm.feed.put(fv, st)), Norm.advance(Norm.feed.put(fv, st)), Nil{}, Nil{}), t, False{}, O, N)

law le_s2:
  for +x: Nat
  {Nat.is_le(1n+x, Nat.add(x, 2n)) == True{} : Bool}

def le_s2(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      le_s2(p)

law nb_eof:
  for +cc: Nat
  for +pend: String
  for +q: List<&2, B.Line>
  for +hq: {B.Text.lines(String.append(pend, "")) == q : List<&2, B.Line>}
  {Nat.is_le(1n+bud(cc, q, True{}, "", Nil{}), rest_need(cc, False{}, pend, Nil{})) == True{} : Bool}

def nb_eof(cc, pend, q, hq):
  +x = Nat.mul(List.length(&2, B.Line, q), cc)
  %Equal.sym(Nat, nlines(pend, Nil{}), List.length(&2, B.Line, q),
    Equal.cong(List<&2, B.Line>, Nat, ls => List.length(&2, B.Line, ls), B.Text.lines(String.append(pend, "")), q, hq)) :
    {Nat.is_le(1n+Nat.add(x, 1n), 2n+Nat.mul(_, cc)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, P.add_one(x)) : {Nat.is_le(1n+_, 2n+x) == True{} : Bool}
  P.le_refl(2n+x)

law arith_chunk:
  for +fc: Nat
  for +t1: Nat
  for +rc: Nat
  {Nat.is_le(1n+Nat.add(fc, 2n+Nat.add(t1, rc)), 2n+Nat.add(1n+t1, Nat.add(fc, rc))) == True{} : Bool}

def arith_chunk(fc, t1, rc):
  %Equal.sym(Nat, Nat.add(fc, 2n+Nat.add(t1, rc)), 1n+Nat.add(fc, 1n+Nat.add(t1, rc)), P.add_succ(fc, 1n+Nat.add(t1, rc))) :
    {Nat.is_le(1n+_, 3n+Nat.add(t1, Nat.add(fc, rc))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(fc, 1n+Nat.add(t1, rc)), 1n+Nat.add(fc, Nat.add(t1, rc)), P.add_succ(fc, Nat.add(t1, rc))) :
    {Nat.is_le(2n+_, 3n+Nat.add(t1, Nat.add(fc, rc))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(fc, Nat.add(t1, rc)), Nat.add(t1, Nat.add(fc, rc)), P.add_left_comm(fc, t1, rc)) :
    {Nat.is_le(3n+_, 3n+Nat.add(t1, Nat.add(fc, rc))) == True{} : Bool}
  P.le_refl(3n+Nat.add(t1, Nat.add(fc, rc)))

law nb_chunk:
  for +cc: Nat
  for +f: Nat
  for +t1: Nat
  for +r2: Nat
  for +n0: Nat
  for +hn: {n0 == Nat.add(f, r2) : Nat}
  {Nat.is_le(1n+Nat.add(Nat.mul(f, cc), 2n+Nat.add(t1, Nat.mul(r2, cc))), 2n+Nat.add(1n+t1, Nat.mul(n0, cc))) == True{} : Bool}

def nb_chunk(cc, f, t1, r2, n0, hn):
  +lhs = {1n+Nat.add(Nat.mul(f, cc), 2n+Nat.add(t1, Nat.mul(r2, cc))) : Nat}
  %Equal.sym(Nat, n0, Nat.add(f, r2), hn) : {Nat.is_le(lhs, 2n+Nat.add(1n+t1, Nat.mul(_, cc))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(f, r2), cc), Nat.add(Nat.mul(f, cc), Nat.mul(r2, cc)), PN.mul_add_r(f, r2, cc)) :
    {Nat.is_le(lhs, 2n+Nat.add(1n+t1, _)) == True{} : Bool}
  arith_chunk(Nat.mul(f, cc), t1, Nat.mul(r2, cc))

law MS.k:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +S: R.RunSt
  for +pend: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +hO: {O == Norm.RunSt.out(S) : String}
  for +hN: {N == Norm.RunSt.notes(S) : List<&2, B.Note>}
  for +hg: {PF.good(S) == True{} : Bool}
  for +hp: {B.Text.lines(pend) == B.Text.last(pend) : List<&2, B.Line>}
  for +hT: {T == R.finish(L.run.go(B.Text.lines(String.append(pend, String.concat(cs))), B.Fasta.parse(fasta), o, S)) : R.Report}
  MoreG(fasta, T, o, Norm.RunSt.clear(S), pend, cs, O, N)

def MS.k(fasta, T, o, S, pend, cs, O, N, hO, hN, hg, hp, hT):
  match cs:
    case Nil{}:
      +fa = B.Fasta.parse(fasta)
      +cc = cost(fasta)
      +q = B.Text.last(pend)
      +hq = Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(pend, "")), B.Text.lines(pend), q,
        Equal.cong(String, List<&2, B.Line>, s => B.Text.lines(s), String.append(pend, ""), pend, PN.str_nil(pend)), hp)
      +hq2 = Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(pend, "")), q, List.append(&2, B.Line, q, Nil{}), hq,
        Equal.sym(List<&2, B.Line>, List.append(&2, B.Line, q, Nil{}), q, P.append_nil(B.Line, q)))
      ok_step(fasta, T, PD(o, Norm.RunSt.clear(S), "", q, True{}, Nil{}, Nil{}, Nil{}, O, N, Nat.add(List.length(&2, B.Line, q), 2n)),
        bud(cc, q, True{}, "", Nil{}), rest_need(cc, False{}, pend, Nil{}),
        PL(q, fasta, T, o, S, Nat.add(List.length(&2, B.Line, q), 2n), Nil{}, Nil{}, "", Nil{}, True{}, O, N,
          le_s2(List.length(&2, B.Line, q)),
          Equal.trans(String, String.append(O, ""), O, Norm.RunSt.out(S), PN.str_nil(O), hO),
          Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, Nil{}), N, Norm.RunSt.notes(S), P.append_nil(B.Note, N), hN),
          hg, {==},
          Equal.trans(R.Report, T, R.finish(L.run.go(B.Text.lines(String.append(pend, "")), fa, o, S)),
            R.finish(L.run.go(List.append(&2, B.Line, q, Nil{}), fa, o, S)), hT,
            Equal.cong(List<&2, B.Line>, R.Report, ls => R.finish(L.run.go(ls, fa, o, S)), B.Text.lines(String.append(pend, "")),
              List.append(&2, B.Line, q, Nil{}), hq2))),
        nb_eof(cc, pend, q, hq))
    case c <> t:
      +fa = B.Fasta.parse(fasta)
      +cc = cost(fasta)
      +x = String.append(pend, c)
      +ct = String.concat(t)
      +fl = PL.FL(x)
      +fr = PL.FR(x)
      +nb = rest_need(cc, False{}, pend, c <> t)
      +rest2 = B.Text.lines(String.append(fr, ct))
      +hc = Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(pend, String.append(c, ct))), B.Text.lines(String.append(x, ct)),
        List.append(&2, B.Line, fl, rest2),
        Equal.cong(String, List<&2, B.Line>, s => B.Text.lines(s), String.append(pend, String.append(c, ct)), String.append(x, ct),
          Equal.sym(String, String.append(x, ct), String.append(pend, String.append(c, ct)), PN.str_assoc(pend, c, ct))),
        PL.L1(x, ct))
      %Equal.sym(Norm.Fed, Norm.feed.start(PL.split(x)), Norm.Fed{fl, fr}, PL.L2(x)) : StepOK(fasta, T, CD(_, o, Norm.RunSt.clear(S), t, O, N), nb)
      ok_step(fasta, T, PD(o, Norm.RunSt.clear(S), fr, fl, False{}, Nil{}, Nil{}, t, O, N, Nat.add(List.length(&2, B.Line, fl), 2n)),
        bud(cc, fl, False{}, fr, t), nb,
        PL(fl, fasta, T, o, S, Nat.add(List.length(&2, B.Line, fl), 2n), Nil{}, Nil{}, fr, t, False{}, O, N,
          le_s2(List.length(&2, B.Line, fl)),
          Equal.trans(String, String.append(O, ""), O, Norm.RunSt.out(S), PN.str_nil(O), hO),
          Equal.trans(List<&2, B.Note>, List.append(&2, B.Note, N, Nil{}), N, Norm.RunSt.notes(S), P.append_nil(B.Note, N), hN),
          hg, PL.L3(x),
          Equal.trans(R.Report, T, R.finish(L.run.go(B.Text.lines(String.append(pend, String.append(c, ct))), fa, o, S)),
            R.finish(L.run.go(List.append(&2, B.Line, fl, rest2), fa, o, S)), hT,
            Equal.cong(List<&2, B.Line>, R.Report, ls => R.finish(L.run.go(ls, fa, o, S)), B.Text.lines(String.append(pend, String.append(c, ct))),
              List.append(&2, B.Line, fl, rest2), hc))),
        nb_chunk(cc, List.length(&2, B.Line, fl), List.length(&2, String, t), nlines(fr, t), nlines(pend, c <> t),
          Equal.trans(Nat, nlines(pend, c <> t), List.length(&2, B.Line, List.append(&2, B.Line, fl, rest2)),
            Nat.add(List.length(&2, B.Line, fl), nlines(fr, t)),
            Equal.cong(List<&2, B.Line>, Nat, ls => List.length(&2, B.Line, ls), B.Text.lines(String.append(pend, String.append(c, ct))),
              List.append(&2, B.Line, fl, rest2), hc),
            P.length_append(B.Line, fl, rest2))))

law MS:
  for +fasta: String
  for +T: R.Report
  for +o: B.Opts
  for +rs: R.RunSt
  for +pend: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for gm: GoodM(B.Fasta.parse(fasta), T, o, rs, pend, cs, O, N)
  MoreG(fasta, T, o, rs, pend, cs, O, N)

def MS(fasta, T, o, rs, pend, cs, O, N, gm):
  match gm:
    case (S, (hrs, (hO, (hN, (hg, (hh, (hp, hT))))))):
      %Equal.sym(R.RunSt, rs, Norm.RunSt.clear(S), hrs) : MoreG(fasta, T, o, _, pend, cs, O, N)
      MS.k(fasta, T, o, S, pend, cs, O, N, hO, hN, hg, hp, hT)

# Driving: every step keeps the state good and lowers need
# ========================================================

def STG(+fasta: String, +T: R.Report, +d: L.DSt, +f: Nat) -> Type:
  +d2 = L.dstep(B.Fasta.parse(fasta), d)
  Good(B.Fasta.parse(fasta), T, d2) & {Nat.is_le(need(B.Fasta.parse(fasta), cost(fasta), d2), f) == True{} : Bool}

law step_from:
  for +fasta: String
  for +T: R.Report
  for +d: L.DSt
  for +f: Nat
  for so: StepOK(fasta, T, L.dstep(B.Fasta.parse(fasta), d), need(B.Fasta.parse(fasta), cost(fasta), d))
  for +hb: {Nat.is_le(need(B.Fasta.parse(fasta), cost(fasta), d), 1n+f) == True{} : Bool}
  STG(fasta, T, d, f)

def step_from(fasta, T, d, f, so, hb):
  match so:
    case (g2, e2):
      +fa = B.Fasta.parse(fasta)
      +cc = cost(fasta)
      (g2, PN.le_trans(1n+need(fa, cc, L.dstep(fa, d)), need(fa, cc, d), 1n+f, e2, hb))

law STEP:
  for +fasta: String
  for +T: R.Report
  for +d: L.DSt
  for +f: Nat
  for g: Good(B.Fasta.parse(fasta), T, d)
  for +hb: {Nat.is_le(need(B.Fasta.parse(fasta), cost(fasta), d), 1n+f) == True{} : Bool}
  STG(fasta, T, d, f)

def STEP(fasta, T, d, f, g, hb):
  match d:
    case L.DSt{st, nx, cs, e, out, notes, Some{c}}:
      (g, P.le_zero_l(f))
    case L.DSt{st, B.Finish{c}, cs, e, out, notes, None{}}:
      (g, P.le_zero_l(f))
    case L.DSt{Norm.St{o, rs, pend, x <> t, e2, w}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, True{}, w}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, Some{p}}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, True{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, False{}, out, notes, None{}}:
      step_from(fasta, T, L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, False{}, out, notes, None{}}, f,
        MS(fasta, T, o, rs, pend, cs, out, notes, g), hb)
    case L.DSt{Norm.St{o, rs, pend, q, True{}, None{}}, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}:
      step_from(fasta, T, L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}, f,
        AS(fasta, T, o, rs, pend, q, True{}, l, back, ch, a, b, cs, out, notes, fs, g), hb)
    case L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, None{}}, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}:
      step_from(fasta, T, L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}, f,
        AS(fasta, T, o, rs, pend, q, False{}, l, back, ch, a, b, cs, out, notes, fs, g), hb)

def ZG(+T: R.Report, +d: L.DSt) -> Type:
  {L.result(d) == Some{T} : Maybe<&2, R.Report>}

# Out of steps, a good state has stopped with the spec's report.
law Z:
  for +fasta: String
  for +T: R.Report
  for +d: L.DSt
  for g: Good(B.Fasta.parse(fasta), T, d)
  for +hb: {Nat.is_le(need(B.Fasta.parse(fasta), cost(fasta), d), 0n) == True{} : Bool}
  ZG(T, d)

def Z(fasta, T, d, g, hb):
  match d:
    case L.DSt{st, nx, cs, e, out, notes, Some{c}}:
      Equal.cong(R.Report, Maybe<&2, R.Report>, x => Some{x}, R.Report{out, notes, c}, T, g)
    case L.DSt{st, B.Finish{c}, cs, e, out, notes, None{}}:
      Empty.absurd(ZG(T, L.DSt{st, B.Finish{c}, cs, e, out, notes, None{}}), P.false_ne_true(hb))
    case L.DSt{Norm.St{o, rs, pend, x <> t, e2, w}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, True{}, w}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, Some{p}}, B.More{}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, True{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, False{}, out, notes, None{}}:
      Empty.absurd(ZG(T, L.DSt{Norm.St{o, rs, pend, Nil{}, False{}, None{}}, B.More{}, cs, False{}, out, notes, None{}}), P.false_ne_true(hb))
    case L.DSt{Norm.St{o, rs, pend, q, True{}, None{}}, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}:
      Empty.absurd(ZG(T, L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}),
        P.false_ne_true(hb))
    case L.DSt{Norm.St{o, rs, pend, q, True{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, None{}}, B.Ask{ch, a, b}, cs, e, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, True{}, out, notes, None{}}:
      match g:
    case L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}:
      Empty.absurd(ZG(T, L.DSt{Norm.St{o, rs, pend, q, False{}, Some{Norm.Pending{l, back, fs}}}, B.Ask{ch, a, b}, cs, False{}, out, notes, None{}}),
        P.false_ne_true(hb))

# Driving a good state with enough fuel gives the spec's report.
law drive_good:
  for +fuel: Nat
  for +fasta: String
  for +T: R.Report
  for +d: L.DSt
  for gh: Ok(fasta, T, d, fuel)
  {L.result(L.drive(fuel, B.Fasta.parse(fasta), d)) == Some{T} : Maybe<&2, R.Report>}

def drive_good(fuel, fasta, T, d, gh):
  match fuel:
    case 0n:
      match gh:
        case (g, hb):
          Z(fasta, T, d, g, hb)
    case 1n+f:
      match gh:
        case (g, hb):
          drive_good(f, fasta, T, L.dstep(B.Fasta.parse(fasta), d), STEP(fasta, T, d, f, g, hb))

# The start
# =========

law arith_start:
  for +l: Nat
  for +y: Nat
  for +y2: Nat
  for +h: {Nat.is_le(y, y2) == True{} : Bool}
  {Nat.is_le(2n+Nat.add(l, y), Nat.add(Nat.add(l, 3n), y2)) == True{} : Bool}

def arith_start(l, y, y2, h):
  match l:
    case 0n:
      PN.le_succ_r(y, y2, h)
    case 1n+p:
      arith_start(p, y, y2, h)

law lines_le:
  for +vcf: String
  for +cs: List<&2, String>
  for +h: {String.concat(cs) == vcf : String}
  {Nat.is_le(nlines("", cs), 1n+String.length(vcf)) == True{} : Bool}

def lines_le(vcf, cs, h):
  %h : {Nat.is_le(nlines("", cs), 1n+String.length(_)) == True{} : Bool}
  PL.N2(String.concat(cs))

# The first state is good, and the bound is enough.
law start_ok:
  for +o: B.Opts
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +h: {String.concat(cs) == vcf : String}
  Ok(fasta, L.run(fasta, vcf, o), L.DSt{Norm.St{o, R.start_st(), "", Nil{}, False{}, None{}}, B.More{}, cs, False{}, "", Nil{}, None{}},
    L.bound(fasta, vcf, cs))

def start_ok(o, fasta, vcf, cs, h):
  +fa = B.Fasta.parse(fasta)
  +cc = cost(fasta)
  +n = nlines("", cs)
  ((R.start_st(), ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    Equal.cong(String, R.Report, v => R.finish(L.run.go(B.Text.lines(v), fa, o, R.start_st())), vcf, String.concat(cs),
      Equal.sym(String, String.concat(cs), vcf, h))))))))),
    arith_start(List.length(&2, String, cs), Nat.mul(n, cc), Nat.mul(1n+String.length(vcf), cc),
      PN.le_mul_r(n, 1n+String.length(vcf), cc, lines_le(vcf, cs, h))))
