import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./protocol.bend as P
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./proof_b_mdefs.bend as MQ
import ./bytes_enc.bend as E
import ./proof_b_assemble.bend as AS

# The implementation laws (MACHINE.bend), restated with every variable
# reusable. usage is proven here; machine is assembled from the simulation
# (proof_b_sim.bend, proof_b_drive.bend) once its parts are proven.

# A command line B.Args.parse does not accept is a usage error.
law usage:
  for +argv: List<&2, String>
  for +ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
  {Norm.start(argv) == Norm.Usage{} : Norm.Begin}

def usage(argv, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), None{}, ha) : {Norm.start.of(_) == Norm.Usage{} : Norm.Begin}
  {==}

# The program writes what run says, within bound steps and reads
# (MACHINE.bend's law machine, restated with every variable reusable).
law machine:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {MQ.launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  AS.machine_h(B.Defs{Nil{}, Nil{}}, argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb)
