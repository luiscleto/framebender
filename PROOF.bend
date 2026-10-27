import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var.bend as PV
import ./proof_window.bend as PW
import ./proof_run.bend as PR
import ./proof_machine.bend as PM

# Proofs of the laws in LAWS.bend: `def L.name` proves `law name`.
# Rewrites: `%e : G` with e : {new == old}; G is the goal with `_` where old
# is; what follows proves G with new there.

# A command line Args.parse rejects starts with a usage error.
def L.usage(argv, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), None{}, ha) : {Norm.start.of(_) == Norm.Usage{} : Norm.Begin}
  {==}

# Forwarded to the proof files (a law is forwarded once its proof there is
# complete; an open law cannot be called).

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

def L.window(fa, body, a, r, ht, hr):
  PW.window(fa, body, a, r, ht, hr)

def L.window_enough(fa, body, a, ht, he):
  PW.window_enough(fa, body, a, ht, he)

def L.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, h):
  PM.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, h)

def L.sorted(fasta, vcf, o, h):
  PR.sorted(fasta, vcf, o, h)

def L.grouped_in(fasta, vcf, o, h):
  PR.grouped_in(fasta, vcf, o, h)

def L.no_unsorted(fasta, vcf, o, hw, hg, ha, hm):
  PR.no_unsorted(fasta, vcf, o, hw, hg, ha, hm)
