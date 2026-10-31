import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA

# The drive area's definitions (the deliverables are in proof_b_drive.bend;
# helper files import this one, so there is no import cycle).

# What a step ends with, for a good state p standing for report T with O and
# N collected: the step's buffer reads as text t (E.out), and
#   More: a good state with no source, before the end of the file;
#   Ask{rs}: a good state that asked rs (each within 2^31 letters, one
#     window's parts: S.rq), or nothing (rs = [], it asked nothing);
#   Finish{c}: the report is O ++ t, N ++ ns, c;
# with the driver's O ++ t and N ++ ns standing for T.
def StepG(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, st: Norm.Step) -> Type:
  match st:
    case Norm.Step{s, b, ns, Pr.More{}}:
      &t: String -> &p2: S.StP -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == S.mkSt(fa, p2) : Norm.St}
        & ({S.WF(fa, p2) == True{} : Bool} & ({S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
        & ({S.src_empty(S.StP.src(p2)) == True{} : Bool} & ({S.StP.eof(p2) == False{} : Bool} & {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}))))))
    case Norm.Step{s, b, ns, Pr.Ask{rs}}:
      &t: String -> &p2: S.StP -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == S.mkSt(fa, p2) : Norm.St}
        & ({S.WF(fa, p2) == True{} : Bool} & ({S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
        & ({E.reqs_ok(rs) == True{} : Bool} & ({rs == S.rq(rs) : List<&2, Pr.Req>} & ({S.mb_reqs(S.StP.md(p2), rs) == True{} : Bool} & ({S.StP.asked(p2) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>} & {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}))))))))
    case Norm.Step{s, b, ns, Pr.Finish{c}}:
      &t: String -> ({E.out(b) == Some{t} : Maybe<&2, String>} & {R.Report{String.append(O, t), List.append(&2, B.Note, N, ns), c} == T : R.Report})

# A state waiting for more input (Step's More): good, no source, not at the
# end of the file, nothing asked.
def more_ok(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  S.WF(fa, p) && S.src_empty(S.StP.src(p)) && Bool.not(S.StP.eof(p)) && Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p))

def start_st(+dfs: B.Defs, b: Norm.Begin) -> Norm.St:
  match b:
    case Norm.Begin{st, r, v}:
      st
    case Norm.Usage{}:
      Norm.St{B.Opts{True{}, 1n, False{}, False{}, Nil{}}, Norm.MS{R.start_st(), Nil{}, 0n, None{}}, Nil{}, Norm.PS{""}, False{}, 0n, Norm.WNone{}, None{}, False{}, dfs}


type Paths is Data:
  Paths{ref: String, vcf: String}

def start_paths(b: Norm.Begin) -> Maybe<&2, Paths>:
  match b:
    case Norm.Begin{st, r, v}:
      Some{Paths{r, v}}
    case Norm.Usage{}:
      None{}
