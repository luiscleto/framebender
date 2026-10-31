import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./LAWS.bend as L
import ./run.bend as R
import ./tan.bend as Tan
import ./protocol.bend as P
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./examples.bend as X

# The machine's concrete cases (law machine on small files). Not in the gate
# (check.sh): since the machine works on packed bytes, evaluating it inside
# the checker runs past the 4 GB cap (killed after about 5 s, even for one
# case). The law machine, proven in PROOF.bend, covers every input, and the
# binary is compared with main's on the 30 + 48 runs (notes/bytes_proofs.md).

def m_basic() -> {M.launch(Norm.start(X.argv()), X.argv(), X.fa(), X.hdr() ++ X.body1(), [X.hdr() ++ X.body1()]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), X.hdr() ++ X.body1(), X.sopts())}} : Maybe<&2, M.Launch>}:
  {==}

# The same file cut in odd places (inside a field, between CR and LF).
def m_pieces() -> {M.launch(Norm.start(X.argv()), X.argv(), X.fa(), X.hdr() ++ X.body1(), ["##fileformat=VCF", "v4.2\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\nc\t4\t.\tA", "", "A\tA\t.\t.\t.\nc\t5\t.\ta\tg\t.\t.\t.", "\n"]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), X.hdr() ++ X.body1(), X.sopts())}} : Maybe<&2, M.Launch>}:
  {==}

def m_mixed_w() -> {M.launch(Norm.start(["norm", "-c", "w", "-f", "r.fa", "in.vcf"]), ["norm", "-c", "w", "-f", "r.fa", "in.vcf"], X.fa(), X.hdr() ++ X.body2(), [X.hdr(), X.body2()]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), X.hdr() ++ X.body2(), B.Opts{False{}, 1000n, False{}, True{}, ["-c", "w", "-f", "r.fa", "in.vcf"]})}} : Maybe<&2, M.Launch>}:
  {==}

def m_mixed_e() -> {M.launch(Norm.start(X.argv()), X.argv(), X.fa(), X.hdr() ++ X.body2(), [X.hdr() ++ X.body2()]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), X.hdr() ++ X.body2(), X.sopts())}} : Maybe<&2, M.Launch>}:
  {==}

def m_unsorted() -> {M.launch(Norm.start(["norm", "-w", "1", "-f", "r.fa", "in.vcf"]), ["norm", "-w", "1", "-f", "r.fa", "in.vcf"], X.fa(), X.hdr() ++ X.body3(), [X.hdr() ++ X.body3()]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), X.hdr() ++ X.body3(), B.Opts{True{}, 1n, False{}, True{}, ["-w", "1", "-f", "r.fa", "in.vcf"]})}} : Maybe<&2, M.Launch>}:
  {==}

def m_noheader() -> {M.launch(Norm.start(X.argv()), X.argv(), X.fa(), "##x\n", ["##x\n"]) == Some{M.Launch{"r.fa", "in.vcf", L.run(X.fa(), "##x\n", X.sopts())}} : Maybe<&2, M.Launch>}:
  {==}
