import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./proof_base.bend as P
import ./proof_machine_sim.bend as PS

# Proofs: the state machine equals run (Norm.start/Norm.step, norm.bend).
# Each law below restates the law of the same name in MACHINE.bend with every
# variable reusable (+); PROOF.bend forwards M.name to it. The proof is in
# proof_machine_sim.bend (and the proof_machine_*.bend lemma files). The
# premise hf (Pr.Fasta.plain) is not needed: the driver definition answers
# from B.Fasta.parse, which already drops spaces and tabs.

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
  {M.launch(Norm.start(argv), fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h):
  +T = L.run(fasta, vcf, o)
  +n = M.bound(fasta, vcf, cs)
  +d0 = {M.DSt{Norm.St{o, R.start_st(), "", Nil{}, 0n, False{}, None{}}, Pr.More{}, cs, False{}, 0n, "", Nil{}, None{}} : M.DSt}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {M.launch(Norm.start.of(_), fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, T}} : Maybe<&2, M.Launch>}
  %Equal.sym(Maybe<&2, R.Report>, M.result(M.drive(n, B.Fasta.parse(fasta), d0), n), Some{T},
    PS.drive_good(n, fasta, T, d0, n, (PS.start_ok(o, fasta, vcf, cs, h), P.le_refl(n)))) :
    {M.launch.of(_, ref, vcfpath) == Some{M.Launch{ref, vcfpath, T}} : Maybe<&2, M.Launch>}
  {==}

law usage:
  for +argv: List<&2, String>
  for +ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
  {Norm.start(argv) == Norm.Usage{} : Norm.Begin}

def usage(argv, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), None{}, ha) : {Norm.start.of(_) == Norm.Usage{} : Norm.Begin}
  {==}
