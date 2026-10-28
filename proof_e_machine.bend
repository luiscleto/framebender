import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_e_mach_asm.bend as AS

# Phase E, area "wrap" (E2): MACHINE.bend's laws with the parallel machine
# (norm_par.bend) as the machine, stated over proof_e_mdefs.bend's copy of
# the driver. The proof is the assembly (as proof_b_assemble.bend's, with
# proof_e_wrap_defs.bend's InvW for the machine's state) and the budget (a
# potential for the parallel machine's states; notes/parallel_proofs.md,
# "Area E"). After the rename these become MACHINE.bend's laws.

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

law machine:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {M.launch(W.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  AS.machine_h(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb)

law usage:
  for +argv: List<&2, String>
  for +ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
  {W.start(argv) == W.Usage{} : W.Begin}

def usage(argv, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), None{}, ha) : {W.start.k(Norm.start.of(_)) == W.Usage{} : W.Begin}
  {==}
