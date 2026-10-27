import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_machine_sim.bend as PS

# Proofs: the state machine equals run (Norm.start/Norm.step, norm.bend).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it. The proof is in
# proof_machine_sim.bend (and the proof_machine_*.bend lemma files).

law machine:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  {L.launch(Norm.start(argv), fasta, vcf, cs) == Some{L.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, L.Launch>}

def machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, h):
  +T = L.run(fasta, vcf, o)
  +d0 = {L.DSt{Norm.St{o, R.start_st(), "", Nil{}, False{}, None{}}, B.More{}, cs, False{}, "", Nil{}, None{}} : L.DSt}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {L.launch(Norm.start.of(_), fasta, vcf, cs) == Some{L.Launch{ref, vcfpath, T}} : Maybe<&2, L.Launch>}
  %Equal.sym(Maybe<&2, R.Report>, L.result(L.drive(L.bound(fasta, vcf, cs), B.Fasta.parse(fasta), d0)), Some{T},
    PS.drive_good(L.bound(fasta, vcf, cs), fasta, T, d0, PS.start_ok(o, fasta, vcf, cs, h))) :
    {L.launch.of(_, ref, vcfpath) == Some{L.Launch{ref, vcfpath, T}} : Maybe<&2, L.Launch>}
  {==}
