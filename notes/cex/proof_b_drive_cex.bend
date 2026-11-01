import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import lawful-bytes@0.1.1.0/bytes.bend as BY

# Counterexamples to proof_b_drive.bend's pump_ok, step_eof, step_ref,
# step_chunk (cases 1, 2) and start_ok (case 3) as stated (`bend proof_b_drive_cex.bend`;
# notes/bytes_proofs_drive.md explains them). The statements allow any O and
# N collected by the driver, also before the #CHROM line, where run.bend's
# report does not keep them (finish before #CHROM writes nothing; head_line
# writes the header over out).
#
# First case (pump_ok; step_eof and step_ref reach the same pump):
# The state: the byte run as it starts (before the #CHROM line), no source,
# an empty line end, at the end of the file, nothing asked: S.WF holds
# (RunInv as run_start promises it for NR.start()), measure is 1, f = 1.
# The driver has collected O = "x" (N = []).
#
# The machine: advance is Idle, idle at the end of the file finishes: the
# run ends with NO_HEADER, code 1, writing nothing; the step hands out ""
# and [NO_HEADER]. StepG's Finish case asks for
#   Report{O ++ "", N ++ [NO_HEADER], 1} == T,
# where T = S.report(fa, cs, O, N, p) = R.finish(L.run.go([], fa, o,
# S.pre(O, N, R.start_st()))) = Report{"", [NO_HEADER], 1}: run.bend's
# finish before the #CHROM line ignores what was written (out "").

def opts() -> B.Opts:
  B.Opts{False{}, 1n, Nil{}}

def st0() -> Norm.St:
  Norm.St{opts(), Norm.MB{NR.start()}, Nil{}, Norm.PB{BY.empty(0n)}, True{}, 100n, Norm.WNone{}, None{}, False{}}

# S.pre, restated (proof_b_sim.bend).
def pre(+O: String, +N: List<&2, B.Note>, st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x}

# T, with L.run.go over no lines (B.Text.lines("") is [], printed by main)
# written out: run.go(Nil, fa, o, st) = st. (LAWS.bend is not imported: its
# open laws stop the file from running.)
def T() -> R.Report:
  R.finish(pre("x", Nil{}, R.start_st()))

def nx_code(nx: Pr.Next) -> Maybe<&2, Nat>:
  match nx:
    case Pr.Finish{c}:
      Some{c}
    case _:
      None{}

def drv(m: Maybe<&2, String>, c: Maybe<&2, Nat>, ns: List<&2, B.Note>) -> Maybe<&2, R.Report>:
  match m c:
    case Some{t} Some{c}:
      Some{R.Report{String.append("x", t), List.append(&2, B.Note, Nil{}, ns), c}}
    case _ _:
      None{}

# What the driver ends with: Report{O ++ t, N ++ ns, c}, for a Finish step.
def driver(s: Norm.Step) -> Maybe<&2, R.Report>:
  match s:
    case Norm.Step{st, b, ns, nx}:
      drv(E.out(b), nx_code(nx), ns)

def rep_out(r: R.Report) -> String:
  R.Report.out(r)

# Second case (step_chunk): the same run, not at the end of the file, given
# the piece "#CHROM\n". The step writes the header (More); the driver then
# holds O ++ t. The spec's run over the same line from pre(O, N, start)
# writes the header over out (run.bend's head_line), so O is lost: the
# report T2 has out = the header alone, while every later report the driver
# makes starts with O ++ t ("x" then the header).
def st1() -> Norm.St:
  Norm.St{opts(), Norm.MB{NR.start()}, Nil{}, Norm.PB{BY.empty(0n)}, False{}, 100n, Norm.WNone{}, None{}, False{}}

def step_out(s: Norm.Step) -> Maybe<&2, String>:
  match s:
    case Norm.Step{st, b, ns, nx}:
      E.out(b)

# L.line_step for this line, written out: line_in False = head_line.
def T2() -> R.Report:
  +l = {B.Line{"#CHROM", "\n"} : B.Line}
  R.finish(R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(pre("x", Nil{}, R.start_st())), opts(), l))

# The driver's report, then T: their out fields differ ("x" vs "").
# Third case (start_ok): a command line B.Args.parse accepts whose VCF path
# holds a character above 255. The options' arguments (argv after "norm")
# are then not bytes, so S.WF, hence more_ok, fails for every p with
# mkSt(fa, p) equal to the start state (that equality fixes p's options).
# start_ok has no hypothesis that argv is bytes (the law machine has one:
# E.texts_ok).
def argv3() -> List<&2, String>:
  ["norm", "-f", "r.fa", SCon{Chr{256}, ".vcf"}]

def args3(m: Maybe<&2, B.Cfg>) -> Maybe<&2, Bool>:
  match m:
    case Some{B.Cfg{B.Opts{s, w, a}, r, v}}:
      Some{E.all_bytes(a)}
    case None{}:
      None{}

# Printed: lines("") has 0 lines; the driver's report and T (out "x" vs
# ""); then the second case's step output t and T2's out (the header, not
# "x" ++ t); then the third case: parse accepts, and the arguments are
# not bytes (Some{False}).
def main() -> ((Nat & (Maybe<&2, R.Report> & R.Report)) & (Maybe<&2, String> & String)) & Maybe<&2, Bool>:
  (((List.length(&2, B.Line, B.Text.lines("")), (driver(Norm.pump(2n, Norm.advance(st0()))), T())),
    (step_out(Norm.step(st1(), Pr.Chunk{E.enc("#CHROM\n")})), R.Report.out(T2()))),
    args3(B.Args.parse(argv3())))
