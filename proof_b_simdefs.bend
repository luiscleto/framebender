import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_rundefs.bend as PR

# The simulation's definitions (phase B): the machine's state between two
# lines stands for a spec state, and handling one line is L.line_step. This
# file fixes the picture of the machine's state (StP), what a good state is
# (WF), what it stands for (report), and what advance must give (AdvG). The
# per-line lemma adv_ok is in proof_b_sim.bend.

# ---------------------------------------------------------------------------
# Pictures
# ---------------------------------------------------------------------------

# The run: on bytes (a run picture), or the String mode's fields as they are.
type MdP is Data:
  MBP{rp: P.RunP}
  MSP{s: R.RunSt, qs: List<&2, String>, ql: Nat, code: Maybe<&2, Nat>}

# The machine's state: every field as is, the run, sources and line end as
# pictures, the window as its picture (built truthfully from fa), the
# header's definitions read so far (-m).
type StP is Data:
  StP{o: B.Opts, md: MdP, src: List<&2, P.SrcP>, pd: P.PdP, eof: Bool, back: Nat, wp: PC.WP, asked: Maybe<&2, List<&2, Pr.Req>>, fneed: Bool, dfs: B.Defs}

def mkMd(+m: MdP) -> Norm.Md:
  match m:
    case MBP{+rp}:
      Norm.MB{P.mkRun(rp)}
    case MSP{s, qs, ql, code}:
      Norm.MS{s, qs, ql, code}

def mkSt(+fa: List<&2, B.Contig>, +p: StP) -> Norm.St:
  match p:
    case StP{o, +md, +src, +pd, eof, back, +wp, asked, fneed, dfs}:
      Norm.St{o, mkMd(md), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}

# ---------------------------------------------------------------------------
# What a state stands for
# ---------------------------------------------------------------------------

def with_out(st: R.RunSt, +out: String) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}

# The run's state this step: out is what it holds to hand out.
def smd(+m: MdP) -> R.RunSt:
  match m:
    case MBP{+rp}:
      P.specRun(rp)
    case MSP{s, +qs, ql, code}:
      with_out(s, Norm.cat(List.reverse(&2, String, qs)))

# A state with O written and the messages N given before it (what the driver
# collected).
def pre(+O: String, +N: List<&2, B.Note>, st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x}

def concat_if(e: Bool, +cs: List<&2, String>) -> String:
  match e:
    case True{}:
      ""
    case False{}:
      String.concat(cs)

# A record source (-m): the records of a split line.
def is_rec(+sp: P.SrcP) -> Bool:
  match sp:
    case P.SPP{len, t, d, at}:
      True{}
    case P.SRP{l}:
      True{}
    case _:
      False{}

# The sources after the records of a split line (the input's own lines), and
# those records (they come first: norm_seq.bend puts them before the rest).
def plain(+sps: List<&2, P.SrcP>) -> List<&2, P.SrcP>:
  match sps:
    case Nil{}:
      Nil{}
    case Con{P.SPP{len, t, d, at}, +r}:
      plain(r)
    case Con{P.SRP{l}, +r}:
      plain(r)
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      Con{P.SBP{len, t, d, at}, r}
    case Con{P.SLP{+q}, +r}:
      Con{P.SLP{q}, r}

def recs(+sps: List<&2, P.SrcP>) -> List<&2, P.SrcP>:
  match sps:
    case Nil{}:
      Nil{}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      Con{P.SPP{len, t, d, at}, recs(r)}
    case Con{P.SRP{+l}, +r}:
      Con{P.SRP{l}, recs(r)}
    case Con{P.SBP{len, t, d, at}, r}:
      Nil{}
    case Con{P.SLP{q}, r}:
      Nil{}

# The text still to come: the sources' (after any records), the line end's,
# then (before the end of the file) the pieces not given yet.
def intext(+p: StP, +cs: List<&2, String>) -> String:
  match p:
    case StP{o, md, +src, +pd, +eof, back, wp, asked, fneed, dfs}:
      String.append(P.srcstext(plain(src)), String.append(P.pdtext(pd), concat_if(eof, cs)))

def StP.o(p: StP) -> B.Opts:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      o

def StP.md(p: StP) -> MdP:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      md

def StP.src(p: StP) -> List<&2, P.SrcP>:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      src

def StP.dfs(p: StP) -> B.Defs:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      dfs

# A record of a split line, from the run as it is: handled as a line with the
# run unticked (its line was counted once, when it was split), or nothing
# once the run has stopped (norm_seq.bend: sp.b, sp.s, the SR source).
def rstep.if(halt: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt, +l: B.Line) -> R.RunSt:
  match halt:
    case True{}:
      st
    case False{}:
      L.line_step(fa, defs, o, Norm.rs_untick(st), l)

def rstep(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
  rstep.if(R.RunSt.halt(st), fa, defs, o, st, l)

def rgo(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  match ls:
    case Nil{}:
      st
    case +l <> t:
      rgo(t, fa, defs, o, rstep(fa, defs, o, st, l))

# The records waiting (record sources, in order), each a step rstep.
def RG(rs: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
  match rs:
    case Nil{}:
      st
    case Con{P.SPP{+len, +t, +d, +at}, r}:
      RG(r, fa, defs, o, rgo(B.Text.lines(P.srctext(P.SPP{len, t, d, at})), fa, defs, o, st))
    case Con{P.SRP{+l}, r}:
      RG(r, fa, defs, o, rstep(fa, defs, o, st, l))
    case Con{sp, r}:
      st

# The header's definitions run reads (L.defs): those read so far, then
# those of the lines still to come before the #CHROM line.
def DEFS(+p: StP, +cs: List<&2, String>) -> B.Defs:
  L.defs.go(B.Text.lines(intext(p, cs)), R.RunSt.inbody(smd(StP.md(p))), StP.dfs(p))

# The report a state leads to, with O and N collected by the driver and cs
# the pieces not given yet: the spec's run over the lines still to come, from
# the state the machine stands for (a finished String mode: its report).
def report.md(m: MdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: StP) -> R.Report:
  match m:
    case MSP{s, +qs, ql, Some{+c}}:
      R.Report{String.append(O, Norm.cat(List.reverse(&2, String, qs))), List.append(&2, B.Note, N, P.RunSt.notes(s)), c}
    case m:
      R.finish(L.run.go(B.Text.lines(intext(p, cs)), fa, DEFS(p, cs), StP.o(p), RG(recs(StP.src(p)), fa, DEFS(p, cs), StP.o(p), pre(O, N, smd(StP.md(p))))))

def report(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: StP) -> R.Report:
  report.md(StP.md(p), fa, cs, O, N, p)

# ---------------------------------------------------------------------------
# A good state
# ---------------------------------------------------------------------------

def ends_lf(+s: String) -> Bool:
  String.is_empty(s) || String.ends_with(s, "\n")

# Every source is good, and every one but the last holds whole lines.
def srcs_ok(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case Con{+sp, Nil{}}:
      P.src_ok(sp)
    case Con{+sp, +t}:
      P.src_ok(sp) && ends_lf(P.srctext(sp)) && srcs_ok(t)

def opts_args(o: B.Opts) -> List<&2, String>:
  match o:
    case B.Opts{s, w, m, z, a}:
      a

def md_ok(+m: MdP) -> Bool:
  match m:
    case MBP{+rp}:
      PR.RunInv(rp)
    case MSP{+s, +qs, +ql, code}:
      Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))) && E.is_bytes(Norm.cat(List.reverse(&2, String, qs))) && P.st_bytes(s)
        && String.is_empty(P.RunSt.out(s))
        && (R.RunSt.inbody(s) || String.is_empty(Norm.cat(List.reverse(&2, String, qs))))
        && (R.RunSt.inbody(s) || List.is_empty(&2, B.Note, P.RunSt.notes(s)))

def src_empty(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case _:
      False{}

# A good state: run, sources, line end and window as the machine keeps them;
# the line end has no LF and is empty while there are sources or after the
# end of the file, when the sources' text ends with an LF; the options'
# arguments (echoed in the header) are bytes.
# In the byte mode a window's contig name is a byte-mode line's CHROM: bytes,
# at most 2^28 of them (cache's against_hit needs both).
def mb_win.k(+wp: PC.WP) -> Bool:
  match wp:
    case PC.WPKnown{+c, a, b}:
      E.is_bytes(c) && Norm.len_le(c, 268435456)
    case _:
      True{}

def mb_win(+md: MdP, +wp: PC.WP) -> Bool:
  match md:
    case MBP{rp}:
      mb_win.k(wp)
    case MSP{s, qs, ql, code}:
      True{}

# A record of a split line has one ALT (fewer than two), so it is not split
# again.
def one_alt(+l: B.Line) -> Bool:
  Nat.is_lt(L.n_alts(B.Line.body(l)), 2n)

def all_one(ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      one_alt(l) && all_one(t)

# A record buffer's text: whole lines, each a record (one ALT).
def rtok(+s: String) -> Bool:
  ends_lf(s) && all_one(B.Text.lines(s))

# Record sources (-m) come first, each holding whole lines of one ALT each;
# while any waits, the run is in the body and has counted their line
# (n >= 1).
def no_recs(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case Con{+sp, +t}:
      Bool.not(is_rec(sp)) && no_recs(t)

def recs_first(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      rtok(P.srctext(P.SPP{len, t, d, at})) && recs_first(r)
    case Con{P.SRP{+l}, +r}:
      one_alt(l) && recs_first(r)
    case Con{+sp, +r}:
      no_recs(r)

def recs_run(+md: MdP, +sps: List<&2, P.SrcP>) -> Bool:
  List.is_empty(&2, P.SrcP, recs(sps)) || (R.RunSt.inbody(smd(md)) && Nat.is_le(1n, R.RunSt.n(smd(md))))

def WF(+fa: List<&2, B.Contig>, +p: StP) -> Bool:
  match p:
    case StP{o, +md, +src, +pd, +eof, back, +wp, asked, fneed, dfs}:
      md_ok(md) && srcs_ok(src) && P.pd_ok(pd) && P.nolf(P.pdtext(pd))
        && (src_empty(src) || String.is_empty(P.pdtext(pd)))
        && (Bool.not(eof) || (String.is_empty(P.pdtext(pd)) && ends_lf(P.srcstext(src))))
        && PC.wp_ok(fa, wp) && mb_win(md, wp)
        && (E.all_bytes(opts_args(o)) && recs_first(src) && recs_run(md, src))

# A measure of the work left in a state's input, as the pump's fuel counts
# it (norm.bend, fuel.src): a byte source's bytes left plus 2, a text line 2,
# and 1 more in the byte mode (for a switch to the String mode). Each handled
# line, each source given up and each change of form lowers it.
def msrc1(+sp: P.SrcP) -> Nat:
  match sp:
    case P.SBP{+len, t, d, +at}:
      Nat.add(U32.to_nat((len - at : U32)), 2n)
    case P.SLP{p}:
      2n
    case P.SPP{len, t, d, at}:
      0n
    case P.SRP{l}:
      0n

# The same for the records of split lines (they are not the input's own
# text: a split line may make more record bytes than it had).
def mrec1(+sp: P.SrcP) -> Nat:
  match sp:
    case P.SPP{+len, t, d, +at}:
      Nat.add(U32.to_nat((len - at : U32)), 2n)
    case P.SRP{l}:
      2n
    case _:
      0n

def mrec(+sps: List<&2, P.SrcP>) -> Nat:
  match sps:
    case Nil{}:
      0n
    case Con{+sp, t}:
      Nat.add(mrec1(sp), mrec(t))

def msrc(+sps: List<&2, P.SrcP>) -> Nat:
  match sps:
    case Nil{}:
      0n
    case Con{+sp, t}:
      Nat.add(msrc1(sp), msrc(t))

def measure(+p: StP) -> Nat:
  match p:
    case StP{o, MBP{rp}, +src, pd, eof, back, wp, asked, fneed, dfs}:
      Nat.add(msrc(src), 1n)
    case StP{o, MSP{s, qs, ql, c}, +src, pd, eof, back, wp, asked, fneed, dfs}:
      msrc(src)

def StP.eof(p: StP) -> Bool:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      eof

def StP.asked(p: StP) -> Maybe<&2, List<&2, Pr.Req>>:
  match p:
    case StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}:
      asked

# The reads of one window, from the first read's contig and start to the
# last read's end (rs == rq(rs): rs is [] or Norm.parts of a window, as every
# Want the machine makes is).
def rq(rs: List<&2, Pr.Req>) -> List<&2, Pr.Req>:
  match rs:
    case Nil{}:
      Nil{}
    case Pr.Req{c, a, b} <> t:
      Norm.parts(c, a, Norm.last_b(t, b))

# In the byte mode, the reads' contig is a byte-mode line's CHROM: bytes, at
# most 2^28 of them (so the window they make keeps mb_win).
def mb_reqs.k(rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Pr.Req{+c, a, b} <> t:
      E.is_bytes(c) && Norm.len_le(c, 268435456)

def mb_reqs(+md: MdP, rs: List<&2, Pr.Req>) -> Bool:
  match md:
    case MBP{rp}:
      mb_reqs.k(rs)
    case MSP{s, qs, ql, code}:
      True{}

# What a step's Ask leaves as asked: the reads, or nothing for an empty Ask.
def asked_of(rs: List<&2, Pr.Req>) -> Maybe<&2, List<&2, Pr.Req>>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      Some{r <> t}

# Less work left: less of the input's own text, or as much and fewer records
# (a split line leaves its records, which may be longer than it was).
def less(+p2: StP, +p: StP) -> Bool:
  Nat.is_lt(measure(p2), measure(p)) || (Nat.is_eq(measure(p2), measure(p)) && Nat.is_lt(mrec(StP.src(p2)), mrec(StP.src(p))))

# ---------------------------------------------------------------------------
# One line
# ---------------------------------------------------------------------------

# The run has stopped (byte mode: halted; String mode: halted or finished).
def stopped(+m: MdP) -> Bool:
  match m:
    case MBP{+rp}:
      P.RunP.x(rp)
    case MSP{+s, qs, ql, code}:
      R.RunSt.halt(s) || Maybe.is_some(&2, Nat, code)

# Nothing is written or noted before the #CHROM line: run.bend's #CHROM line
# replaces what was written (the guard step_pre has too).
def guard(+O: String, +N: List<&2, B.Note>, +p: StP) -> Bool:
  R.RunSt.inbody(smd(StP.md(p))) || (String.is_empty(O) && List.is_empty(&2, B.Note, N))

# What advance did in the byte mode (byte mode before and after): the
# lines it handled, taken from the front of the text still to come, moved
# into the run. In every case the definitions of the text still to come
# are kept (S.DEFS; the threads machine gives Q's to its tasks).
# (m and m2 are p's and p2's runs: a match needs them as parameters.)
def Moved.md(+m: MdP, +m2: MdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: StP, +p2: StP) -> Type:
  match m m2:
    case MBP{+rp} MBP{+rp2}:
      &ls: List<&2, B.Line> -> ({B.Text.lines(intext(p, cs)) == List.append(&2, B.Line, ls, B.Text.lines(intext(p2, cs))) : List<&2, B.Line>}
        & ({P.settle(RG(recs(StP.src(p2)), fa, DEFS(p, cs), StP.o(p), P.specRun(rp2))) == P.settle(L.run.go(ls, fa, DEFS(p, cs), StP.o(p), RG(recs(StP.src(p)), fa, DEFS(p, cs), StP.o(p), P.specRun(rp)))) : R.RunSt}
        & {DEFS(p2, cs) == DEFS(p, cs) : B.Defs}))
    case _ _:
      {DEFS(p2, cs) == DEFS(p, cs) : B.Defs}

def Moved(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: StP, +p2: StP) -> Type:
  Moved.md(StP.md(p), StP.md(p2), fa, cs, p, p2)

# What advance did to the input (from the byte mode): unless the rest of the
# first source (a buffer) holds no LF, that source is the same buffer, from
# some point on, before the same later sources (after the records of a line
# split on its bytes, if any: plain drops them); when the first source holds
# records, the plain sources are those after it. In any other case nothing is
# claimed. (Phase F: a task takes its piece back from Q's input.)
def Kept.sp(+sp: P.SrcP, +rest: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>) -> Type:
  match sp:
    case P.SBP{+len, +t, +d, +at}:
      {P.nolf(P.srctext(P.SBP{len, t, d, at})) == False{} : Bool} -> (&at2: U32 -> {plain(s2) == Con{P.SBP{len, t, d, at2}, rest} : List<&2, P.SrcP>})
    case P.SLP{+q}:
      Unit
    case P.SPP{+len, +t, +d, +at}:
      {plain(s2) == plain(rest) : List<&2, P.SrcP>}
    case P.SRP{+l}:
      {plain(s2) == plain(rest) : List<&2, P.SrcP>}

def Kept.s(+s1: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>) -> Type:
  match s1:
    case Nil{}:
      Unit
    case Con{+sp, +rest}:
      Kept.sp(sp, rest, s2)

def Kept.md(+m: MdP, +s1: List<&2, P.SrcP>, +s2: List<&2, P.SrcP>) -> Type:
  match m:
    case MBP{+rp}:
      Kept.s(s1, s2)
    case MSP{+s, +qs, +ql, +code}:
      Unit

def Kept(+p: StP, +p2: StP) -> Type:
  Kept.md(StP.md(p), StP.src(p), StP.src(p2))

# What advance leads to, for a good state p standing for report T: a good
# state standing for T again (the lines it handled moved into its run), and
#   Went: with less work left; Want: asking reads it keeps as asked, each
#   within 2^31 letters; Idle: no source left; Ended: the run stopped (or
#   the String mode finished); Yield: the step wrote 2^30 bytes or more.
def AdvG(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: StP, a: Norm.Adv) -> Type:
  match a:
    case Norm.Went{st}:
      &p2: StP -> ({st == mkSt(fa, p2) : Norm.St} & ({WF(fa, p2) == True{} : Bool} & ({report(fa, cs, O, N, p2) == T : R.Report}
        & ({less(p2, p) == True{} : Bool} & ({StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>} & ({StP.eof(p2) == StP.eof(p) : Bool} & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & (Moved(fa, cs, p, p2) & Kept(p, p2))))))))))
    case Norm.Want{st, reqs}:
      &p2: StP -> ({st == mkSt(fa, p2) : Norm.St} & ({WF(fa, p2) == True{} : Bool} & ({report(fa, cs, O, N, p2) == T : R.Report}
        & ({E.reqs_ok(reqs) == True{} : Bool} & ({reqs == rq(reqs) : List<&2, Pr.Req>} & ({StP.asked(p2) == asked_of(reqs) : Maybe<&2, List<&2, Pr.Req>>} & ({stopped(StP.md(p2)) == False{} : Bool} & ({mb_reqs(StP.md(p2), reqs) == True{} : Bool} & ({StP.eof(p2) == StP.eof(p) : Bool} & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & (Moved(fa, cs, p, p2) & Kept(p, p2)))))))))))))
    case Norm.Idle{st}:
      &p2: StP -> ({st == mkSt(fa, p2) : Norm.St} & ({WF(fa, p2) == True{} : Bool} & ({report(fa, cs, O, N, p2) == T : R.Report}
        & ({src_empty(StP.src(p2)) == True{} : Bool} & ({StP.asked(p2) == StP.asked(p) : Maybe<&2, List<&2, Pr.Req>>} & ({StP.eof(p2) == StP.eof(p) : Bool} & ({stopped(StP.md(p2)) == False{} : Bool} & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & (Moved(fa, cs, p, p2) & Kept(p, p2)))))))))))
    case Norm.Ended{st}:
      &p2: StP -> ({st == mkSt(fa, p2) : Norm.St} & ({WF(fa, p2) == True{} : Bool} & ({report(fa, cs, O, N, p2) == T : R.Report}
        & ({StP.asked(p2) == StP.asked(p) : Maybe<&2, List<&2, Pr.Req>>} & ({stopped(StP.md(p2)) == True{} : Bool} & ({StP.eof(p2) == StP.eof(p) : Bool} & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & ({DEFS(p2, cs) == DEFS(p, cs) : B.Defs} & Kept(p, p2))))))))))
    case Norm.Yield{st}:
      &p2: StP -> ({st == mkSt(fa, p2) : Norm.St} & ({WF(fa, p2) == True{} : Bool} & ({report(fa, cs, O, N, p2) == T : R.Report}
        & ({StP.asked(p2) == StP.asked(p) : Maybe<&2, List<&2, Pr.Req>>} & ({stopped(StP.md(p2)) == False{} : Bool} & ({StP.eof(p2) == StP.eof(p) : Bool} & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & ({DEFS(p2, cs) == DEFS(p, cs) : B.Defs} & Kept(p, p2))))))))))
