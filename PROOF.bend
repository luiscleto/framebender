import Base
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./proof_var.bend as PV
import ./proof_window.bend as PW
import ./proof_run.bend as PR
import ./proof_b_machine.bend as PM
import ./proof_e_machine.bend as EM

# Proofs of the laws: `def L.name` proves `law name` of LAWS.bend (the
# science), `def M.name` proves `law name` of MACHINE.bend (the
# implementation). Each forwards to the proof file that restates the law with
# every variable reusable.

# The normal form of one variant (proof_var.bend).

def L.same_change(seq, v, hv):
  PV.same_change(seq, v, hv)

def L.stays_valid(seq, v, hv):
  PV.stays_valid(seq, v, hv)

def L.standard_form(seq, v, hv):
  PV.standard_form(seq, v, hv)

def L.normal_unchanged(seq, v, hv, hn):
  PV.normal_unchanged(seq, v, hv, hn)

def L.twice(seq, v, hv):
  PV.twice(seq, v, hv)

def L.one_form(seq, v, w, hv, hw, hs):
  PV.one_form(seq, v, w, hv, hw, hs)

def L.shortest(seq, v, w, hv, hw, hs):
  PV.shortest(seq, v, w, hv, hw, hs)

def L.unique(seq, v, w, hv, hw, hnv, hnw, hs):
  PV.unique(seq, v, w, hv, hw, hnv, hnw, hs)

# Records the tool normalizes are valid (proof_window.bend).

def L.normalized_valid(fa, body, h):
  PW.normalized_valid(fa, body, h)

# What run guarantees (proof_run.bend).

def L.sorted(fasta, vcf, o, h):
  PR.sorted(fasta, vcf, o, h)

def L.grouped_in(fasta, vcf, o, h):
  PR.grouped_in(fasta, vcf, o, h)

def L.no_unsorted(fasta, vcf, o, hw, hg, ha, hm):
  PR.no_unsorted(fasta, vcf, o, hw, hg, ha, hm)

def L.twice_run(fasta, vcf, o, h):
  PR.twice_run(fasta, vcf, o, h)

# The program (proof_e_machine.bend, the parallel machine; it runs the
# sequential machine norm_seq.bend, whose own proof of the same law is
# proof_b_machine.bend's over proof_b_mdefs.bend).

def M.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  EM.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb)

def M.usage(argv, ha):
  EM.usage(argv, ha)
