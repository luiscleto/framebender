import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_cachedefs.bend as PC
import ./proof_b_drivedefs.bend as DD
import ./proof_b_budget_need.bend as BN
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_lem.bend as LM
import ./proof_e_bud_start.bend as BS0

# Phase E, area E2: the budget API the assembly (proof_e_mach_asm.bend) needs
# (as proof_b_budget_api.bend for phase B): the potential BD.needW of a
# wrapper state and BD.biW, such that
#   - at the start, need fits the bound;
#   - each driver step lowers need by at least 1 + the reads it answers;
#   - a step that ends the run leaves need >= 2 + those reads.
# The statements speak of every picture x2 of the step's next state that
# E1's StepGW gives (with its InvW).

def txt(+cs: List<&2, String>) -> Bool:
  E.all_bytes(cs) && E.pieces_ok(cs)

# For every picture x2 of the step's next state (More or Ask): its InvW given
# back, biW there and the drop of need.
def KontW(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, s: W.Step, +cs2: List<&2, String>, +de2: Bool, +R: Nat, +n1: Nat, +O: String, +N: List<&2, B.Note>) -> Type:
  @x2: WD.WPic -> @nx2: Pr.Next -> @t: String -> @N2: List<&2, B.Note> -> {List.append(&2, B.Note, N, BD.snsW(s)) == N2 : List<&2, B.Note>}
    -> {BD.sstW(s) == WD.mkWSt(fa, x2) : W.St} -> {BD.snxW(s) == nx2 : Pr.Next}
    -> {BD.soutW(s) == Some{t} : Maybe<&2, String>} -> WD.InvW(dfs, fa, T, cs2, String.append(O, t), N2, x2, nx2, de2)
    -> (WD.InvW(dfs, fa, T, cs2, String.append(O, t), N2, x2, nx2, de2) & ({BD.biW(WD.mkWSt(fa, x2), cs2) == True{} : Bool}
      & {Nat.is_le(Nat.add(BD.needW(fa, T, WD.mkWSt(fa, x2), cs2, de2, nx2, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}))

# When the step ends the run.
def KFinW(s: W.Step, +R: Nat, +n1: Nat) -> Type:
  @code: Nat -> {BD.snxW(s) == Pr.Finish{code} : Pr.Next} -> {Nat.is_le(Nat.add(R, 2n), n1) == True{} : Bool}

# need always holds the last two steps and a pending Ask's step and reads.
def need_ge(+fa: List<&2, B.Contig>, +T: R.Report, +x: WD.WPic, +cs: List<&2, String>, +ef: Bool, +nx: Pr.Next, +O: String) ->
  {Nat.is_le(Nat.add(2n, BN.RD(nx)), BD.needW(fa, T, WD.mkWSt(fa, x), cs, ef, nx, O)) == True{} : Bool}:
  LM.need_ge(fa, T, x, cs, ef, nx, O)

# The start: the program's first state, nothing given yet.
def bud_startW(+dfs: B.Defs, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +fasta: String, +vcf: String, +cs: List<&2, String>,
  +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  +h: {String.concat(cs) == vcf : String},
  +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}) ->
  {BD.biW(W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs) == True{} : Bool}
  & {Nat.is_le(BD.needW(B.Fasta.parse(fasta), L.run(fasta, vcf, o), W.St{DD.start_st(dfs, Norm.start(argv)), W.BNone{}}, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}:
  (BS0.start_bi(dfs, argv, o, ref, vcfpath, cs, ha), BS0.start_need(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, ha, h, hb))
