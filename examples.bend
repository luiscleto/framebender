import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./LAWS.bend as L
import ./run.bend as R
import ./tan.bend as Tan
import ./protocol.bend as P
import ./MACHINE.bend as M
import ./bytes_enc.bend as E

# Concrete cases, checked by evaluation (bend examples.bend --check-only).

def gaaaat() -> List<&2, B.Base>:
  [B.G{}, B.A{}, B.A{}, B.A{}, B.A{}, B.T{}]

# Deleting one A from GAAAAT, written at the last A, moves to the G.
def del_moves() -> {Tan.normal(gaaaat(), B.Var{4n, [B.A{}, B.A{}], [[B.A{}]]}) == B.Var{1n, [B.G{}, B.A{}], [[B.G{}]]} : B.Var}:
  {==}

def del_not_normal() -> {L.normalized(gaaaat(), B.Var{4n, [B.A{}, B.A{}], [[B.A{}]]}) == False{} : Bool}:
  {==}

def del_normal() -> {L.normalized(gaaaat(), B.Var{1n, [B.G{}, B.A{}], [[B.G{}]]}) == True{} : Bool}:
  {==}

# Multiallelic: on GAAAAT, at 2, REF AA with ALTs A (delete one A) and AAA
# (insert one A) moves to the G for both.
def multi_moves() -> {Tan.normal(gaaaat(), B.Var{3n, [B.A{}, B.A{}], [[B.A{}], [B.A{}, B.A{}, B.A{}]]}) == B.Var{1n, [B.G{}, B.A{}], [[B.G{}], [B.G{}, B.A{}, B.A{}]]} : B.Var}:
  {==}

def multi_normal() -> {L.normalized(gaaaat(), B.Var{1n, [B.G{}, B.A{}], [[B.G{}], [B.G{}, B.A{}, B.A{}]]}) == True{} : Bool}:
  {==}

# Multiallelic with a SNP: AAT at 4 -> (G, AAA) on GAAAAT... a substitution
# and a deletion together: REF AT, ALTs GT and T. They share the last base T,
# which is trimmed: REF A, ALTs G and empty; empty forces a shift left.
def multi_snp() -> {Tan.normal(gaaaat(), B.Var{5n, [B.A{}, B.T{}], [[B.G{}, B.T{}], [B.T{}]]}) == B.Var{4n, [B.A{}, B.A{}], [[B.A{}, B.G{}], [B.A{}]]} : B.Var}:
  {==}

# At the start of a contig: deleting the first base takes the base after it.
def aat() -> List<&2, B.Base>:
  [B.A{}, B.A{}, B.T{}]

def start_del() -> {Tan.normal(aat(), B.Var{2n, [B.A{}, B.T{}], [[B.T{}]]}) == B.Var{1n, [B.A{}, B.A{}], [[B.A{}]]} : B.Var}:
  {==}

# (1, A, CA,GA) on A is already normal: nothing can be trimmed at position 1.
def start_multi() -> {Tan.normal([B.A{}], B.Var{1n, [B.A{}], [[B.C{}, B.A{}], [B.G{}, B.A{}]]}) == B.Var{1n, [B.A{}], [[B.C{}, B.A{}], [B.G{}, B.A{}]]} : B.Var}:
  {==}

# --- Text ------------------------------------------------------------------

def lines_lf() -> {B.Text.lines("a\nb\n") == [B.Line{"a", "\n"}, B.Line{"b", "\n"}] : List<&2, B.Line>}:
  {==}

def lines_crlf_noeol() -> {B.Text.lines("a\r\nb\r") == [B.Line{"a", "\r\n"}, B.Line{"b", "\r\n"}] : List<&2, B.Line>}:
  {==}

def lines_blank() -> {B.Text.lines("a\n\nb") == [B.Line{"a", "\n"}, B.Line{"", "\n"}, B.Line{"b", "\n"}] : List<&2, B.Line>}:
  {==}

def lines_empty() -> {B.Text.lines("") == Nil{} : List<&2, B.Line>}:
  {==}

def fasta_two() -> {B.Fasta.parse("junk\n>c1 desc\nAcR\r\nnK\n>c2\nT T\n>\nA\n>c1\nG\n") == [B.Contig{"c1", "AcRnK"}, B.Contig{"c2", "TT"}] : List<&2, B.Contig>}:
  {==}

def fasta_bases() -> {B.Bases.of_fasta("AcRnK*") == [B.A{}, B.C{}, B.A{}, B.N{}, B.G{}, B.N{}] : List<&2, B.Base>}:
  {==}

# A vertical tab is not FASTA whitespace: it reads as N.
def fasta_vt() -> {B.Fasta.parse(">c\nA\u{b}G\n") == [B.Contig{"c", "A\u{b}G"}] : List<&2, B.Contig>}:
  {==}

def args_ok() -> {B.Args.parse(["norm", "-c", "w", "-f", "r.fa", "-w", "5", "in.vcf"]) == Some{B.Cfg{B.Opts{False{}, 5n, ["-c", "w", "-f", "r.fa", "-w", "5", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_default() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 100000n, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_w0() -> {B.Args.parse(["norm", "-w", "0", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_two_vcf() -> {B.Args.parse(["norm", "-f", "r.fa", "a.vcf", "b.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_no_ref() -> {B.Args.parse(["norm", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# --threads N is read anywhere among the options and is not recorded.
def args_threads() -> {B.Args.parse(["norm", "--threads", "8", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 100000n, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads_mid() -> {B.Args.parse(["norm", "-f", "r.fa", "--threads", "008", "-c", "w", "in.vcf"]) == Some{B.Cfg{B.Opts{False{}, 100000n, ["-f", "r.fa", "-c", "w", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

# The last --threads counts.
def args_threads_last() -> {B.Args.threads(["norm", "--threads", "4", "-f", "r.fa", "--threads", "128", "in.vcf"]) == Some{128n} : Maybe<&2, Nat>}:
  {==}

def args_threads_none() -> {B.Args.threads(["norm", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

def args_threads0() -> {B.Args.parse(["norm", "--threads", "0", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads129() -> {B.Args.parse(["norm", "--threads", "129", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads_word() -> {B.Args.parse(["norm", "--threads", "four", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads_end() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "--threads"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# As the value of -f, "--threads" is a path, recorded like any other.
def args_threads_path() -> {B.Args.parse(["norm", "-f", "--threads", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 100000n, ["-f", "--threads", "in.vcf"]}, "--threads", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

# As the value of -c or -w, "--threads" is a bad value.
def args_threads_c() -> {B.Args.parse(["norm", "-f", "r.fa", "-c", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads_w() -> {B.Args.parse(["norm", "-f", "r.fa", "-w", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# A --threads without its number takes the next word as its value.
def args_threads_noval() -> {B.Args.parse(["norm", "--threads", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# Every --threads must be valid, as with -w.
def args_threads_bad_first() -> {B.Args.parse(["norm", "--threads", "0", "-f", "r.fa", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# A command line refused without --threads is refused with it.
def args_threads_no_ref() -> {B.Args.parse(["norm", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# After the VCF path, as anywhere an option may come.
def args_threads_after() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "--threads", "8"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
  {==}

# Where an option may come (law threads' B.Args.expecting).
def expecting_start() -> {B.Args.expecting([]) == True{} : Bool}:
  {==}

def expecting_after_value() -> {B.Args.expecting(["-f", "r.fa"]) == True{} : Bool}:
  {==}

def expecting_after_vcf() -> {B.Args.expecting(["-f", "r.fa", "in.vcf"]) == True{} : Bool}:
  {==}

def expecting_value() -> {B.Args.expecting(["-f"]) == False{} : Bool}:
  {==}

# After an error the parser still reads the next word as an option.
def expecting_error() -> {B.Args.expecting(["-c", "x"]) == True{} : Bool}:
  {==}

# Args.threads: Some only for an accepted command line.
def threads_lead0() -> {B.Args.threads(["norm", "-f", "r.fa", "--threads", "008", "-c", "w", "in.vcf"]) == Some{8n} : Maybe<&2, Nat>}:
  {==}

def threads_path() -> {B.Args.threads(["norm", "-f", "--threads", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

def threads_zero() -> {B.Args.threads(["norm", "--threads", "0", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

def threads_big() -> {B.Args.threads(["norm", "--threads", "999", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

def threads_cmd() -> {B.Args.threads(["x", "--threads", "8", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

def threads_trailing() -> {B.Args.threads(["norm", "--threads", "4", "-f", "r.fa", "in.vcf", "--threads"]) == None{} : Maybe<&2, Nat>}:
  {==}

def threads_refused() -> {B.Args.threads(["norm", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
  {==}

# --- Whole runs ------------------------------------------------------------

def fa() -> String:
  ">c\nGAAAAT\n>d\nACGT\n"

def hdr() -> String:
  "##fileformat=VCFv4.2\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"

def added() -> String:
  "##fileformat=VCFv4.2\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -f r.fa\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"

def strict() -> B.Opts:
  B.Opts{True{}, 100000n, ["-f", "r.fa"]}

# A deletion moves to the start; a lower-case SNP is written in upper case.
def run_basic() -> {L.run(fa(), hdr() ++ "c\t4\t.\tAA\tA\t.\t.\t.\nc\t5\t.\ta\tg\t.\t.\t.\n", strict()) == R.Report{added() ++ "c\t1\t.\tGA\tG\t.\t.\t.\nc\t5\t.\tA\tG\t.\t.\t.\n", [B.Summary{2n, 2n, 0n, 0n}], 0n} : R.Report}:
  {==}

# A REF mismatch stops the run under -c e, after the header was written.
def run_mismatch() -> {L.run(fa(), hdr() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", strict()) == R.Report{added(), [B.Stop{B.RefMismatch{}, Some{B.At{3n, "c", "2"}}, None{}}], 1n} : R.Report}:
  {==}

# Under -c w it is passed through with a warning.
def run_mismatch_w() -> {L.run(fa(), hdr() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", B.Opts{False{}, 100000n, ["-f", "r.fa"]}) == R.Report{added() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", [B.Warning{B.RefMismatch{}, B.At{3n, "c", "2"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# A record that moves before one read earlier comes out first.
def run_sorts() -> {L.run(fa(), hdr() ++ "c\t5\t.\tA\tG\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\tEND=5\n", strict()) == R.Report{added() ++ "c\t1\t.\tGA\tG\t.\t.\tEND=2\nc\t5\t.\tA\tG\t.\t.\t.\n", [B.Summary{2n, 1n, 0n, 0n}], 0n} : R.Report}:
  {==}

# With -w 1 the buffer writes early, so the same move stops the run.
def run_unsorted() -> {R.Report.code(L.run(fa(), hdr() ++ "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n", B.Opts{True{}, 1n, ["-f", "r.fa"]})) == 1n : Nat}:
  {==}

def run_unsorted_note() -> {R.Report.notes(L.run(fa(), hdr() ++ "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n", B.Opts{True{}, 1n, ["-f", "r.fa"]})) == [B.Stop{B.Unsorted{}, Some{B.At{5n, "c", "4"}}, Some{B.At{3n, "c", "2"}}}] : List<&2, B.Note>}:
  {==}

# A CHROM coming back after another one stops the run.
def run_regroup() -> {R.Report.notes(L.run(fa(), hdr() ++ "c\t2\t.\tA\tG\t.\t.\t.\nd\t1\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\n", strict())) == [B.Stop{B.Unsorted{}, Some{B.At{5n, "c", "3"}}, None{}}] : List<&2, B.Note>}:
  {==}

# Out of scope (symbolic ALT) on an unknown contig passes; a known-shape record
# on an unknown contig stops the run.
def run_unknown() -> {R.Report.notes(L.run(fa(), hdr() ++ "zz\t2\t.\tA\t<DEL>\t.\t.\t.\nzz\t3\t.\tA\tC\t.\t.\t.\n", strict())) == [B.Stop{B.UnknownChrom{}, Some{B.At{4n, "zz", "3"}}, None{}}] : List<&2, B.Note>}:
  {==}

# No #CHROM line: nothing written, NO_HEADER.
def run_noheader() -> {L.run(fa(), "##fileformat=VCFv4.2\n", strict()) == R.Report{"", [B.Stop{B.NoHeader{}, None{}, None{}}], 1n} : R.Report}:
  {==}

# A blank line is MALFORMED.
def run_blank() -> {R.Report.notes(L.run(fa(), hdr() ++ "\n", strict())) == [B.Stop{B.Malformed{}, Some{B.At{3n, "", ""}}, None{}}] : List<&2, B.Note>}:
  {==}

# A reference read returns the letters without whitespace, clipped to the
# contig.
def truth_ws() -> {M.truth(B.Fasta.parse(">c\nA C\r\nGT\n"), "c", 1n, 9n) == P.Known{4n, 1n, E.enc("CGT")} : P.Ans}:
  {==}

def truth_unknown() -> {M.truth(B.Fasta.parse(">c\nAC\n"), "d", 0n, 2n) == P.Unknown{} : P.Ans}:
  {==}

# --- The machine: cases of law machine -------------------------------------

def argv() -> List<&2, String>:
  ["norm", "-f", "r.fa", "in.vcf"]

def sopts() -> B.Opts:
  B.Opts{True{}, 100000n, ["-f", "r.fa", "in.vcf"]}

def body1() -> String:
  "c\t4\t.\tAA\tA\t.\t.\t.\nc\t5\t.\ta\tg\t.\t.\t.\n"

def body2() -> String:
  "c\t5\t.\tA\tG\t.\t.\t.\r\nc\t4\t.\tAA\tA\t.\t.\tEND=5\r\nzz\t1\t.\tA\t<DEL>\t.\t.\t.\r\nd\t2\t.\tC\tT\t.\t.\t.\r\nd\t3\t.\tGT\tG\t.\t.\t.\r\nd\t1\t.\tA\tA,G\t.\t.\t."

def body3() -> String:
  "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n"

def m_usage() -> {Norm.start(["norm", "in.vcf"]) == Norm.Usage{} : Norm.Begin}:
  {==}
