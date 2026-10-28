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
import ./proof_b_drivedefs.bend as DD
import ./proof_b_budget_need.bend as BN
import ./proof_b_bud_fin.bend as BF
import ./proof_b_bud_start.bend as BSt
import ./proof_b_budget_step.bend as BS

# The budget API (pb-cut's area; notes/bytes_proofs_drive.md, "Budget API").
#
# The assembly (proof_b_assemble.bend) needs only this: a potential `need`
# of a driver state that has not stopped, given by the machine's picture p
# and the driver's fields (pieces not given cs, eof given, next nx, output
# collected O), with an invariant `bi` of pb-cut's choice (True{} if none is
# needed), such that
#   - at the start, need fits the bound;
#   - each driver step lowers need by at least 1 + the reads it answers;
#   - a step that ends the run (Finish) leaves need >= 2 + those reads
#     (one step for it, one for the driver's last step).
# The assembly then keeps reads + need <= bound and need <= the fuel left.
# Every TODO below is pb-cut's; the statements are fixed by the assembly.

# What a step produces (projections of Norm.Step, for the statements).
def sst(s: Norm.Step) -> Norm.St:
  BN.sst(s)

def snx(s: Norm.Step) -> Pr.Next:
  BN.snx(s)

def sns(s: Norm.Step) -> List<&2, B.Note>:
  BN.sns(s)

def sout(s: Norm.Step) -> Maybe<&2, String>:
  BN.sout(s)

# The potential of a driver state (More or Ask) whose machine state is
# pictured by p: an upper bound on the driver steps plus the reads still to
# come (pb-cut's definition).
def need(+fa: List<&2, B.Contig>, +T: R.Report, +p: S.StP, +cs: List<&2, String>, +eof: Bool, +nx: Pr.Next, +O: String) -> Nat:
  BN.need(fa, T, p, cs, eof, nx, O)

# pb-cut's own invariant of such a state (True{} if none is needed).
def bi(+fa: List<&2, B.Contig>, +T: R.Report, +p: S.StP, +cs: List<&2, String>, +eof: Bool, +nx: Pr.Next, +O: String) -> Bool:
  BN.bi(fa, T, p, cs, eof, nx, O)

# The start: the program's first state (start_ok's p), nothing given yet.
def bud_start(+argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +fasta: String, +vcf: String, +cs: List<&2, String>, +p: S.StP,
  ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  hf: {Pr.Fasta.plain(fasta) == True{} : Bool},
  h: {String.concat(cs) == vcf : String},
  hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool},
  hst: {DD.start_st(Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St},
  hm: {DD.more_ok(B.Fasta.parse(fasta), p) == True{} : Bool},
  hr: {S.report(B.Fasta.parse(fasta), cs, "", Nil{}, p) == L.run(fasta, vcf, o) : R.Report}) ->
  {bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}
  & {Nat.is_le(need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}:
  BSt.bud_start_h(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst)

# A piece of the file (the driver's More with pieces left).
# Next state pictured by p2 (More or Ask{rs2}, nx2): need drops by 1 + the reads.
def bud_chunk(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +c: String,
  +cs: List<&2, String>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, c <> cs, False{}, Pr.More{}, O) == True{} : Bool},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hst: {sst(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == S.mkSt(fa, p2) : Norm.St},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == nx2 : Pr.Next},
  hout: {sout(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == Some{t} : Maybe<&2, String>},
  hw2: {S.WF(fa, p2) == True{} : Bool},
  hr2: {S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))), p2) == T : R.Report},
  hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}))), p2) == True{} : Bool}) ->
  {bi(fa, T, p2, cs, False{}, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(need(fa, T, p2, cs, False{}, nx2, String.append(O, t)), Nat.add(0n, 1n)), need(fa, T, p, c <> cs, False{}, Pr.More{}, O)) == True{} : Bool}:
  BS.bud_chunk_h(fa, T, c, cs, O, N, p, p2, nx2, t, hb, hm, hr, hg, hbi, hcb, hcn, hst, hnx, hout, hw2, hr2, hg2)

# The same input when the step ends the run (Finish).
def bud_chunk_fin(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +c: String,
  +cs: List<&2, String>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +code: Nat,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, c <> cs, False{}, Pr.More{}, O) == True{} : Bool},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})) == Pr.Finish{code} : Pr.Next}) ->
  {Nat.is_le(Nat.add(0n, 2n), need(fa, T, p, c <> cs, False{}, Pr.More{}, O)) == True{} : Bool}:
  BF.chunk_fin(fa, T, c, cs, O, p)

# The end of the file (the driver's More with no piece left).
# Next state pictured by p2 (More or Ask{rs2}, nx2): need drops by 1 + the reads.
def bud_eof(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, Nil{}, False{}, Pr.More{}, O) == True{} : Bool},
  hst: {sst(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == S.mkSt(fa, p2) : Norm.St},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == nx2 : Pr.Next},
  hout: {sout(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == Some{t} : Maybe<&2, String>},
  hw2: {S.WF(fa, p2) == True{} : Bool},
  hr2: {S.report(fa, Nil{}, String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Eof{}))), p2) == T : R.Report},
  hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Eof{}))), p2) == True{} : Bool}) ->
  {bi(fa, T, p2, Nil{}, True{}, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(need(fa, T, p2, Nil{}, True{}, nx2, String.append(O, t)), Nat.add(0n, 1n)), need(fa, T, p, Nil{}, False{}, Pr.More{}, O)) == True{} : Bool}:
  BS.bud_eof_h(fa, T, O, N, p, p2, nx2, t, hb, hm, hr, hg, hbi, hst, hnx, hout, hw2, hr2, hg2)

# The same input when the step ends the run (Finish).
def bud_eof_fin(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +code: Nat,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, Nil{}, False{}, Pr.More{}, O) == True{} : Bool},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Eof{})) == Pr.Finish{code} : Pr.Next}) ->
  {Nat.is_le(Nat.add(0n, 2n), need(fa, T, p, Nil{}, False{}, Pr.More{}, O)) == True{} : Bool}:
  BF.eof_fin(fa, T, O, p)

# The answers to an Ask (the driver adds |rs| to its reads).
# Next state pictured by p2 (More or Ask{rs2}, nx2): need drops by 1 + the reads.
def bud_ref(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +cs: List<&2, String>,
  +de: Bool,
  +rs: List<&2, Pr.Req>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +p2: S.StP, +nx2: Pr.Next, +t: String,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  hq: {E.reqs_ok(rs) == True{} : Bool},
  hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, cs, de, Pr.Ask{rs}, O) == True{} : Bool},
  hst: {sst(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == S.mkSt(fa, p2) : Norm.St},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == nx2 : Pr.Next},
  hout: {sout(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == Some{t} : Maybe<&2, String>},
  hw2: {S.WF(fa, p2) == True{} : Bool},
  hr2: {S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))), p2) == T : R.Report},
  hg2: {S.guard(String.append(O, t), List.append(&2, B.Note, N, sns(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))), p2) == True{} : Bool}) ->
  {bi(fa, T, p2, cs, de, nx2, String.append(O, t)) == True{} : Bool}
  & {Nat.is_le(Nat.add(need(fa, T, p2, cs, de, nx2, String.append(O, t)), Nat.add(List.length(&2, Pr.Req, rs), 1n)), need(fa, T, p, cs, de, Pr.Ask{rs}, O)) == True{} : Bool}:
  BS.bud_ref_h(fa, T, cs, de, rs, O, N, p, p2, nx2, t, hb, hw, hr, ha, hq, hp, hmr, hg, hbi, hst, hnx, hout, hw2, hr2, hg2)

# The same input when the step ends the run (Finish).
def bud_ref_fin(
  +fa: List<&2, B.Contig>,
  +T: R.Report,
  +cs: List<&2, String>,
  +de: Bool,
  +rs: List<&2, Pr.Req>,
  +O: String, +N: List<&2, B.Note>, +p: S.StP, +code: Nat,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  hq: {E.reqs_ok(rs) == True{} : Bool},
  hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hbi: {bi(fa, T, p, cs, de, Pr.Ask{rs}, O) == True{} : Bool},
  hnx: {snx(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})) == Pr.Finish{code} : Pr.Next}) ->
  {Nat.is_le(Nat.add(List.length(&2, Pr.Req, rs), 2n), need(fa, T, p, cs, de, Pr.Ask{rs}, O)) == True{} : Bool}:
  BF.ref_fin(fa, T, cs, de, rs, O, p)
