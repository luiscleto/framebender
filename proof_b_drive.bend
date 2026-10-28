import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drivedefs.bend as DD
import ./proof_b_drive_pump.bend as DP
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_start.bend as DST
import ./proof_b_drive_chunk.bend as DC

# The simulation's step level: a step's pump ends in a good state that
# stands for the same report, with a well-formed output buffer, and what the
# step wrote and said moved to the driver's side. (Partial correctness; the
# step and read budget, M.bound, comes on top: notes/bytes_proofs.md.)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# Pumping from a good state, with fuel for its work, ends a step well.
def pump_ok(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +f: Nat,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}) ->
  DD.StepG(fa, T, cs, O, N, Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p)))):
  DP.pump_ok_h(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf)

# A piece of the VCF file (bytes, at most 2^31 of them).
def step_chunk(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DD.StepG(fa, T, cs, O, N, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})):
  DC.step_chunk_h(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg)

# The end of the file.
def step_eof(+fa: List<&2, B.Contig>, +T: R.Report, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DD.StepG(fa, T, Nil{}, O, N, Norm.step(S.mkSt(fa, p), Pr.Eof{})):
  DS.step_eof_h(fa, T, O, N, p, hb, hm, hr, hg)

# The truthful answers to what the state asked (rs; [] for an empty Ask).
def step_ref(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +rs: List<&2, Pr.Req>,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  hq: {E.reqs_ok(rs) == True{} : Bool},
  hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DD.StepG(fa, T, cs, O, N, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})):
  DS.step_ref_h(fa, T, cs, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg)

# The program starts in a state waiting for input that stands for the
# spec's whole run (with nothing collected yet).
def start_ok(+fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>,
  ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  hab: {E.all_bytes(argv) == True{} : Bool}) ->
  &p: S.StP -> ({DD.start_st(Norm.start(argv)) == S.mkSt(fa, p) : Norm.St}
  & ({DD.start_paths(Norm.start(argv)) == Some{DD.Paths{ref, vcfpath}} : Maybe<&2, DD.Paths>}
  & ({DD.more_ok(fa, p) == True{} : Bool}
  & ({S.report(fa, cs, "", Nil{}, p) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}
  & {S.guard("", Nil{}, p) == True{} : Bool})))):
  DST.start_ok_g(fa, argv, o, ref, vcfpath, cs, ha, hab)
