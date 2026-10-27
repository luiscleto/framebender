import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_sorted.bend as PS
import ./proof_run_grouped.bend as PG
import ./proof_run_nounsorted.bend as PN
import ./proof_run_twice.bend as PT

# Proofs: what run guarantees (run.bend, LAWS.run).
# Each law below restates the law of the same name in LAWS.bend with every
# variable reusable (+); PROOF.bend forwards L.name to it.

law sorted:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {R.Report.out(L.run(fasta, vcf, o)) == L.head(vcf, o) ++ L.texts(L.gsort(L.items(fasta, vcf))) : String}

def sorted(fasta, vcf, o, h):
  PS.sorted_head(B.Text.lines(vcf), B.Fasta.parse(fasta), o, 0n, "", R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, h)

law grouped_in:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.grouped(L.items(fasta, vcf)) == True{} : Bool}

def grouped_in(fasta, vcf, o, h):
  PG.grouped_head(B.Text.lines(vcf), B.Fasta.parse(fasta), o, 0n, "", R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, h)

law no_unsorted:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +hw: {Nat.is_le(1n, R.Opts.w(o)) == True{} : Bool}
  for +hg: {L.grouped(L.items(fasta, vcf)) == True{} : Bool}
  for +ha: {L.ascending(L.items(fasta, vcf)) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), L.items(fasta, vcf)) == True{} : Bool}
  {L.any_unsorted(R.Report.notes(L.run(fasta, vcf, o))) == False{} : Bool}

def no_unsorted(fasta, vcf, o, hw, hg, ha, hm):
  PN.nu_head(B.Text.lines(vcf), B.Fasta.parse(fasta), o, 0n, "", R.Cnt{0n, 0n, 0n, 0n}, "", Nil{}, {==}, hg, ha, hm)

law twice_run:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {(Nat.is_eq(R.Report.code(L.run(fasta, R.Report.out(L.run(fasta, vcf, o)), o)), 0n)
    && String.eq(L.body(R.Report.out(L.run(fasta, R.Report.out(L.run(fasta, vcf, o)), o))), L.body(R.Report.out(L.run(fasta, vcf, o))))) == True{} : Bool}

def twice_run(fasta, vcf, o, h):
  PT.twice_main(fasta, vcf, o, h)
