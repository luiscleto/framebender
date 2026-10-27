import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P

# Proofs: the state machine equals run (Norm.start/Norm.step, norm.bend).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it.

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
