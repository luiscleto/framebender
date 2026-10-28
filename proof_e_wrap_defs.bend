import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_e_task.bend as PT

# Phase E, area "wrap": the parallel machine's picture, what a good state is
# and what it stands for, and what a step must give (notes/parallel_proofs.md,
# "Area E"). Q's picture is phase B's S.StP; the batch is pictured by the
# pieces' texts, a planned batch (PT.Pc) and the tasks' results (PT.TOutP).

# ---------------------------------------------------------------------------
# Pictures
# ---------------------------------------------------------------------------

# The batch: none; collecting (the pieces' texts, newest first, as the code
# holds them, and how many); waiting for the answers (the planned pieces);
# combining (the pieces left, their results, whether the file ended, and
# whether Q is in the middle of a piece).
type BatP is Data:
  BNoneP{}
  BColP{hs: List<&2, String>, k: Nat}
  BAskP{ps: List<&2, PT.Pc>, eofp: Bool}
  BCombP{ps: List<&2, PT.Pc>, xs: List<&2, PT.TOutP>, eofp: Bool, seq: Bool}

type WPic is Data:
  WPic{p: S.StP, bat: BatP}

def mkBat(+fa: List<&2, B.Contig>, +b: BatP) -> W.Bat:
  match b:
    case BNoneP{}:
      W.BNone{}
    case BColP{+hs, k}:
      W.BCol{PT.encs(hs), k}
    case BAskP{+ps, e}:
      W.BAsk{PT.mkPls(ps), e}
    case BCombP{+ps, +xs, e, s}:
      W.BComb{PT.mkTOuts(fa, ps, xs), e, s}

def mkWSt(+fa: List<&2, B.Contig>, +x: WPic) -> W.St:
  match x:
    case WPic{+p, +b}:
      W.St{S.mkSt(fa, p), mkBat(fa, b)}

# The pieces the batch holds, in file order (they come before the driver's).
def held(+b: BatP) -> List<&2, String>:
  match b:
    case BNoneP{}:
      Nil{}
    case BColP{+hs, k}:
      List.reverse(&2, String, hs)
    case BAskP{+ps, e}:
      PT.texts(ps)
    case BCombP{+ps, xs, e, s}:
      PT.texts(ps)

def WPic.p(x: WPic) -> S.StP:
  match x:
    case WPic{p, b}:
      p

def WPic.bat(x: WPic) -> BatP:
  match x:
    case WPic{p, b}:
      b

# What a state stands for: Q's report with the held pieces before cs.
def wreport(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WPic) -> R.Report:
  match x:
    case WPic{+p, +b}:
      S.report(fa, List.append(&2, String, held(b), cs), O, N, p)

# ---------------------------------------------------------------------------
# A good state
# ---------------------------------------------------------------------------

# Q as phase B's driver invariant has it before next nx (ef: the driver's
# end-of-file flag): More: waiting for input; Ask: what it asked.
def QNext(+fa: List<&2, B.Contig>, +p: S.StP, nx: Pr.Next, +ef: Bool) -> Type:
  match nx:
    case Pr.More{}:
      {DR.more_ok(fa, p) == True{} : Bool} & {ef == False{} : Bool}
    case Pr.Ask{+rs}:
      {S.WF(fa, p) == True{} : Bool} & ({E.reqs_ok(rs) == True{} : Bool} & ({rs == S.rq(rs) : List<&2, Pr.Req>}
        & ({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool} & ({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>} & {S.StP.eof(p) == ef : Bool}))))
    case Pr.Finish{c}:
      Empty

# A batch closed by the end of the file: the driver gave it (ef) and has no
# piece left.
def EofOK(e: Bool, +ef: Bool, +cs: List<&2, String>) -> Type:
  match e:
    case True{}:
      {ef == True{} : Bool} & {cs == Nil{} : List<&2, String>}
    case False{}:
      {ef == False{} : Bool}

def next_is_more(nx: Pr.Next) -> Bool:
  match nx:
    case Pr.More{}:
      True{}
    case _:
      False{}

# The batch, by phase (nx: what the step asked of the driver). While Q waits
# quietly (collecting, asking, between pieces), its run has not stopped.
def PhaseOK(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +b: BatP, +nx: Pr.Next, +ef: Bool) -> Type:
  match b:
    case BNoneP{}:
      QNext(fa, p, nx, ef)
    case BColP{+hs, +k}:
      {nx == Pr.More{} : Pr.Next} & ({DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({ef == False{} : Bool} & {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool})))
    case BAskP{+ps, +e}:
      {nx == Pr.Ask{PT.reqs_of(ps)} : Pr.Next} & ({DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool}
        & (PT.PcsOK(ps, cs) & EofOK(e, ef, cs)))))
    case BCombP{+ps, +xs, +e, False{}}:
      {nx == Pr.Ask{Nil{}} : Pr.Next} & ({DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool}
        & (PT.PcsOK(ps, cs) & (PT.BatchOK(fa, S.StP.o(p), ps, xs, cs) & EofOK(e, ef, cs)))))
    case BCombP{+ps, +xs, +e, True{}}:
      QNext(fa, p, nx, False{}) & ({next_is_more(nx) == False{} : Bool}
        & (PT.PcsOK(ps, cs) & (PT.BatchOK(fa, S.StP.o(p), ps, xs, cs) & EofOK(e, ef, cs))))

# A good wrapper state before next nx, standing for report T with O and N
# collected by the driver and cs the pieces not given yet (ef: the driver's
# end-of-file flag): the held pieces are bytes, each at most 2^31; Q's
# guard; the report; the phase.
def InvW(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WPic, +nx: Pr.Next, +ef: Bool) -> Type:
  match x:
    case WPic{+p, +b}:
      {E.all_bytes(held(b)) && E.pieces_ok(held(b)) == True{} : Bool}
        & ({S.guard(O, N, p) == True{} : Bool} & ({wreport(fa, cs, O, N, WPic{p, b}) == T : R.Report}
        & PhaseOK(fa, cs, p, b, nx, ef)))

# What a step ends with, for a good state standing for T: the step's buffer
# reads as text t, and a good state before the step's next (or, at Finish,
# the report).
def StepGW(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, st: W.Step) -> Type:
  match st:
    case W.Step{s, b, ns, Pr.More{}}:
      &t: String -> &x2: WPic -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == mkWSt(fa, x2) : W.St}
        & InvW(fa, T, cs, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.More{}, ef)))
    case W.Step{s, b, ns, Pr.Ask{rs}}:
      &t: String -> &x2: WPic -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == mkWSt(fa, x2) : W.St}
        & InvW(fa, T, cs, String.append(O, t), List.append(&2, B.Note, N, ns), x2, Pr.Ask{rs}, ef)))
    case W.Step{s, b, ns, Pr.Finish{c}}:
      &t: String -> ({E.out(b) == Some{t} : Maybe<&2, String>} & {R.Report{String.append(O, t), List.append(&2, B.Note, N, ns), c} == T : R.Report})

# The program's first state and paths (MACHINE.bend's launch reads them).
def wstart_st(b: W.Begin) -> W.St:
  match b:
    case W.Begin{st, r, v}:
      st
    case W.Usage{}:
      W.St{DR.start_st(Norm.Usage{}), W.BNone{}}

def wstart_paths(b: W.Begin) -> Maybe<&2, DR.Paths>:
  match b:
    case W.Begin{st, r, v}:
      Some{DR.Paths{r, v}}
    case W.Usage{}:
      None{}
