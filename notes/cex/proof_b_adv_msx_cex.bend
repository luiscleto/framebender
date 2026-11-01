import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# (Copied from proof_b_adv_cex.bend for case H; see the end.)
# Counterexamples to proof_b_sim.bend's adv_ok as stated (its WF and mkSt
# are copied below for a String-mode state with no window: importing that
# file would import other areas' open TODOs), run on concrete
# values (`bend proof_b_adv_cex.bend`; notes/bytes_proofs_adv.md explains
# them). main prints, for each case, the facts that make it a counterexample.
# Round 1 (A-D) is fixed in proof_b_sim.bend / norm.bend: the copies of WF
# below are the round-1 WF (A, B, D still show what the old WF allowed; C,
# run on the new norm.bend, now prints asked_none = True). Round 2: E, F, G
# hold against the current WF too (its new clauses are true of them).
#   A: eof, and the last source has no LF: advance moves its text to pend
#      (Went), but WF asks for an empty pend after the end of the file.
#   B: String mode whose held header is not bytes: the #CHROM line writes it
#      to qs (Went), but WF's md_ok asks qs to be bytes.
#   D: as B with a held header of bytes, but an option argument (o.args,
#      written in the added header lines) that is not bytes.
#   E: String mode in the body, its run state's out not empty ("x"): the
#      report ignores it (smd sets out to qs's text), but after one line
#      ms.out moves it into qs, so the next state's report has it.
#   F: String mode before the #CHROM line, O = "y" collected by the driver
#      (adv_ok allows any O): the spec's #CHROM line replaces out, dropping O;
#      the next state's report keeps it in front.
#   G: the same with O = "" and qs = ["y"] (WF allows text in qs before the
#      #CHROM line).
#   C: byte mode, an SL source, asked = Some: advance goes to the String
#      mode (Went) keeping asked, but AdvG's Went asks for asked = None.

# proof_b_sim.bend's StP, mkSt and WF, for MSP states and the window WPNone.
type StP is Data:
  StP{o: B.Opts, s: R.RunSt, qs: List<&2, String>, ql: Nat, src: List<&2, P.SrcP>, pd: P.PdP, eof: Bool}

def mkSt(+p: StP) -> Norm.St:
  match p:
    case StP{o, s, qs, ql, +src, +pd, eof}:
      Norm.St{o, Norm.MS{s, qs, ql, None{}}, P.mkSrcs(src), P.mkPd(pd), eof, 100n, Norm.WNone{}, None{}, False{}}

def ends_lf(+s: String) -> Bool:
  String.is_empty(s) || String.ends_with(s, "\n")

def srcs_ok(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case Con{+sp, Nil{}}:
      P.src_ok(sp)
    case Con{+sp, +t}:
      P.src_ok(sp) && ends_lf(P.srctext(sp)) && srcs_ok(t)

def src_empty(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case _:
      False{}

def WF(+p: StP) -> Bool:
  match p:
    case StP{o, s, +qs, +ql, +src, +pd, +eof}:
      (Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))) && E.is_bytes(Norm.cat(List.reverse(&2, String, qs))))
        && srcs_ok(src) && P.pd_ok(pd) && P.nolf(P.pdtext(pd))
        && (src_empty(src) || String.is_empty(P.pdtext(pd)))
        && (Bool.not(eof) || String.is_empty(P.pdtext(pd)))

def opts() -> B.Opts:
  B.Opts{False{}, 1000n, Nil{}}

# The mirror of E.enc(s) (proof_b_enc.bend's enc_t, copied).
def ttree(+d: Nat, +ws: List<&2, U32>) -> AT.Tree<U32>:
  match d:
    case 0n:
      AT.TLeaf{Maybe.default(&2, U32, List.get(&2, U32, ws, 0n), 0)}
    case 1n+p:
      AT.TNode{ttree(p, List.take(&2, U32, ws, Nat.pow(2n, p))), ttree(p, List.drop(&2, U32, ws, Nat.pow(2n, p)))}

def enc_t(+s: String) -> AT.Tree<U32>:
  ttree(E.depth(String.length(s)), E.words(E.codes(s)))

def srcb(+s: String) -> P.SrcP:
  P.SBP{U32.from_nat(String.length(s)), enc_t(s), E.depth(String.length(s)), 0}

def pd0() -> P.PdP:
  P.PBP{0, enc_t(""), 0n}

# A String-mode run state with held header h, not stopped.
def rs(+h: String) -> R.RunSt:
  R.RunSt{0n, False{}, h, None{}, Nil{}, None{}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}

type Wt is Data:
  Wt{eof: Bool, pend: String, qs_bytes: Bool, asked_none: Bool}
  NotWent{}

type Res is Data:
  Res{wfA: Bool, a: Wt, wfB: Bool, b: Wt, c: Wt, wfD: Bool, d: Wt, wfE: Bool, e1: R.Report, e2: Maybe<&2, R.Report>, wfF: Bool, f1: R.Report, f2: Maybe<&2, R.Report>, wfG: Bool, g1: R.Report, g2: Maybe<&2, R.Report>}

def pdt(pd: Norm.Pd) -> String:
  match pd:
    case Norm.PB{b}:
      Norm.text_of(b)
    case Norm.PS{s}:
      s

def mdb(md: Norm.Md) -> Bool:
  match md:
    case Norm.MS{s, qs, ql, c}:
      E.is_bytes(Norm.cat(List.reverse(&2, String, qs)))
    case Norm.MB{r}:
      True{}

# What a Went step leads to: (eof, pend's text, qs are bytes, asked is None).
def went(a: Norm.Adv) -> Wt:
  match a:
    case Norm.Went{Norm.St{o, md, src, pend, eof, back, win, asked, fneed}}:
      Wt{eof, pdt(pend), mdb(md), Maybe.is_none(&2, List<&2, Pr.Req>, asked)}
    case _:
      NotWent{}

# A: String mode, eof True, one source "abc" (no LF), pend empty.
def pA() -> StP:
  StP{opts(), rs(""), Nil{}, 0n, [srcb("abc")], pd0(), True{}}

# B: String mode, held header one Char of code 256, the #CHROM line as text.
def pB() -> StP:
  StP{opts(), rs(SCon{Chr{256}, SNil{}}), Nil{}, 0n, [P.SLP{"#CHROM"}], pd0(), False{}}

# D: String mode, empty held header, one option argument of code 256.
def pD() -> StP:
  StP{B.Opts{False{}, 1000n, [SCon{Chr{256}, SNil{}}]}, rs(""), Nil{}, 0n, [P.SLP{"#CHROM"}], pd0(), False{}}


# E: String mode in the body, out "x", one malformed body line "a".
def rsE() -> R.RunSt:
  R.RunSt{0n, True{}, "", None{}, Nil{}, None{}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "x", Nil{}, False{}}

def pE() -> StP:
  StP{opts(), rsE(), Nil{}, 0n, [P.SLP{"a"}], pd0(), False{}}

def with_out(st: R.RunSt, +out: String) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}

# proof_b_sim.bend's report for pE (O, N empty, no pieces to come), and for
# the String-mode state advance leads to (its sources are then empty).
# (L.run.go on the one line "a": L.line_step is R.body_line of L.judge, and
# L.judge of a malformed line is L.res(Broken), copied here: importing
# LAWS.bend would import its open laws.)
def repE() -> R.Report:
  +l = B.Text.line("a")
  +fs = B.Rec.fields("a")
  +s1 = R.tick(with_out(rsE(), ""))
  R.finish(R.body_line(B.Res{B.Broken{}, B.Rec.pos(fs), "a", False{}}, s1, opts(), l, B.At{R.RunSt.n(s1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)))

def rep2(a: Norm.Adv) -> Maybe<&2, R.Report>:
  match a:
    case Norm.Went{Norm.St{o, Norm.MS{s, qs, ql, c}, Nil{}, pend, eof, back, win, asked, fneed}}:
      Some{R.finish(with_out(s, Norm.cat(List.reverse(&2, String, qs))))}
    case _:
      None{}


# F, G: before the #CHROM line, then the #CHROM line.
def rsH() -> R.RunSt:
  R.RunSt{0n, False{}, "", None{}, Nil{}, None{}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}

def pF() -> StP:
  StP{opts(), rsH(), Nil{}, 0n, [P.SLP{"#CHROM"}], pd0(), False{}}

def pG() -> StP:
  StP{opts(), rsH(), ["y"], 1n, [P.SLP{"#CHROM"}], pd0(), False{}}

# The spec's report from a state with out q (O and qs's text) in front:
# L.line_step of the #CHROM line is R.head_line(True) after a tick.
def repH(+q: String) -> R.Report:
  R.finish(R.head_line(True{}, R.tick(with_out(rsH(), q)), opts(), B.Text.line("#CHROM")))

def pre_out(+O: String, m: Maybe<&2, R.Report>) -> Maybe<&2, R.Report>:
  match m:
    case Some{R.Report{o, ns, c}}:
      Some{R.Report{O ++ o, ns, c}}
    case None{}:
      None{}

# C: the byte mode's start run (run_start: RunInv holds of its picture), an
# SL source, one read asked.
def stC() -> Norm.St:
  Norm.St{opts(), Norm.MB{NR.start()}, [Norm.SL{"x"}], Norm.PB{BY.empty(0n)}, False{}, 100n, Norm.WNone{}, Some{[Pr.Req{"c", 0n, 1n}]}, False{}}


# H: String mode in the body, out "", one text-line source holding two lines
# ("x\ny": WF's src_ok asks only that it is bytes). Both lines are malformed
# (no tabs). The machine judges "x\ny" as one line; the spec reads two lines,
# stops at "x" and never reads "y". The stop's message names the line's
# CHROM field: "x\ny" for the machine, "x" for the spec.
def rsI() -> R.RunSt:
  R.RunSt{0n, True{}, "", None{}, Nil{}, None{}, Nil{}, R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, False{}}

def qH() -> String:
  SCon{'x', SCon{'\n', SCon{'y', SNil{}}}}

def pH() -> StP:
  StP{opts(), rsI(), Nil{}, 0n, [P.SLP{qH()}], pd0(), False{}}

# The spec's report for pH: L.run.go on lines("x\ny\n") = ["x", "y"]; L.judge
# of a malformed line is Broken (copied as in repE); after the stop, "y"
# changes nothing (the run is halted).
def repH2() -> R.Report:
  +l = B.Text.line("x")
  +fs = B.Rec.fields("x")
  +s1 = R.tick(rsI())
  R.finish(R.body_line(B.Res{B.Broken{}, B.Rec.pos(fs), "x", False{}}, s1, opts(), l, B.At{R.RunSt.n(s1), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)))

type ResH is Data:
  ResH{wf: Bool, lines: Nat, spec: R.Report, next: Maybe<&2, R.Report>}

def main() -> ResH:
  ResH{WF(pH()), List.length(&2, B.Line, B.Text.lines(P.srcstext([P.SLP{qH()}]))), repH2(), rep2(Norm.advance(mkSt(pH())))}
