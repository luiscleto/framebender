import Base
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./proof_var.bend as PV
import ./proof_window.bend as PW
import ./proof_run.bend as PR
import ./proof_b_machine.bend as PM
import ./proof_e_machine.bend as EM
import ./proof_f_threads.bend as FT
import ./proof_f_out.bend as FO
import ./proof_f_index.bend as FI
import ./proof_s_laws.bend as SLW
import ./proof_s_runm.bend as SRM
import ./proof_s_when.bend as SWH
import ./proof_s_site.bend as SSI
import ./proof_s_same.bend as SSA
import ./proof_s_valid.bend as SVA
import ./proof_s_norm.bend as SNO
import ./proof_s_change.bend as SCH
import ./proof_s_gtl.bend as SGT
import ./proof_s_ikeys.bend as SIK
import ./proof_s_ivals.bend as SIV
import ./proof_s_fshape.bend as SFS
import ./proof_s_fvals.bend as SFV
import ./proof_s_fkept.bend as SFK

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

# Splitting multiallelic records, -m (proof_s_*.bend).

def L.whole_without_m(defs, o, body, h):
  SLW.whole_without_m(defs, o, body, h)

def L.items_without_m(fasta, vcf, o, h):
  SRM.items_without_m_p(fasta, vcf, o, h)

def L.whole_biallelic(defs, o, body, h):
  SLW.whole_biallelic(defs, o, body, h)

def L.whole_malformed(defs, o, body, h):
  SLW.whole_malformed(defs, o, body, h)

def L.biallelic_run(fasta, vcf, o, h):
  SRM.biallelic_run_p(fasta, vcf, o, h)

def L.split_when(defs, o, body, hs, hm, hn):
  SWH.split_when_p(defs, o, body, hs, hm, hn)

def L.split_alts(defs, o, body, ps, h):
  SSI.split_alts(defs, o, body, ps, h)

def L.split_site(defs, o, body, ps, h):
  SSA.split_site(defs, o, body, ps, h)

def L.split_valid(fa, defs, o, body, ps, h, hv):
  SVA.split_valid(fa, defs, o, body, ps, h, hv)

def L.split_normalized(fa, defs, o, body, ps, h, hn):
  SNO.split_normalized_p(fa, defs, o, body, ps, h, hn)

def L.split_change(fa, defs, o, body, ps, h, hv, i, p, hp, hs):
  SCH.split_change_p(fa, defs, o, body, ps, h, hv, i, p, hp, hs)

def L.split_gt(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg):
  SGT.split_gt(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg)

def L.split_phase(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg):
  SGT.split_phase(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg)

def L.split_info_keys(defs, o, body, ps, h, i, p, hp):
  SIK.split_info_keys(defs, o, body, ps, h, i, p, hp)

def L.split_info_values(defs, o, body, ps, h, i, p, hp, e, x, hx, num, hk, ha, hv, hm):
  SIV.split_info_values(defs, o, body, ps, h, i, p, hp, e, x, hx, num, hk, ha, hv, hm)

def L.split_info_kept(defs, o, body, ps, h, i, p, hp, e, x, hx, hc):
  SIV.split_info_kept(defs, o, body, ps, h, i, p, hp, e, x, hx, hc)

def L.split_format_shape(defs, o, body, ps, h, i, p, hp, s):
  SFS.split_format_shape(defs, o, body, ps, h, i, p, hp, s)

def L.split_format_values(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, num, hn, ha, v, hv, hm):
  SFV.split_format_values(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, num, hn, ha, v, hv, hm)

def L.split_format_kept(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, v, hv, hc):
  SFK.split_format_kept(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, v, hv, hc)

# The program (proof_e_machine.bend, the parallel machine; it runs the
# sequential machine norm_seq.bend, whose own proof of the same law is
# proof_b_machine.bend's over proof_b_mdefs.bend).

def M.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  EM.machine(argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb)

def M.usage(argv, ha):
  EM.usage(argv, ha)

# --threads N changes nothing the program writes (proof_f_threads.bend, from
# law machine and law usage).

def M.threads(pre, x, n, post, fasta, vcf, cs, he, hx, hn, hf, h, hb):
  FT.threads(pre, x, n, post, fasta, vcf, cs, he, hx, hn, hf, h, hb)

# The output options (-o, -O) change nothing the program writes
# (proof_f_out.bend, from law machine and law usage).

def M.output(pre, o, post, fasta, vcf, cs, he, ho, hf, h, hb):
  FO.output(pre, o, post, fasta, vcf, cs, he, ho, hf, h, hb)

# The index option (-W) changes nothing the program writes, nor where and how
# the output is written, nor the thread count (proof_f_index.bend, from law
# machine, law usage and the parser).

def M.index(pre, x, post, fasta, vcf, cs, he, hx, hf, h, hb):
  FI.index(pre, x, post, fasta, vcf, cs, he, hx, hf, h, hb)

def M.index_sink(pre, x, post, he, hx):
  FI.index_sink(pre, x, post, he, hx)
