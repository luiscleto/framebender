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

def args_ok() -> {B.Args.parse(["norm", "-c", "w", "-f", "r.fa", "-w", "5", "in.vcf"]) == Some{B.Cfg{B.Opts{False{}, 5n, False{}, True{}, ["-c", "w", "-f", "r.fa", "-w", "5", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_default() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_w0() -> {B.Args.parse(["norm", "-w", "0", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_two_vcf() -> {B.Args.parse(["norm", "-f", "r.fa", "a.vcf", "b.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def args_no_ref() -> {B.Args.parse(["norm", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# --threads N is read anywhere among the options and is not recorded.
def args_threads() -> {B.Args.parse(["norm", "--threads", "8", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def args_threads_mid() -> {B.Args.parse(["norm", "-f", "r.fa", "--threads", "008", "-c", "w", "in.vcf"]) == Some{B.Cfg{B.Opts{False{}, 1000n, False{}, True{}, ["-f", "r.fa", "-c", "w", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
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
def args_threads_path() -> {B.Args.parse(["norm", "-f", "--threads", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "--threads", "in.vcf"]}, "--threads", "in.vcf"}} : Maybe<&2, B.Cfg>}:
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

# --- Output options (-o, -O; law output) -----------------------------------

# They change nothing Args.parse returns, and are not recorded in the header.
def out_header() -> {B.Args.parse(["norm", "-Oz", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def out_sep() -> {B.Args.parse(["norm", "-f", "r.fa", "-O", "z9", "in.vcf", "-o", "-"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
  {==}

# Refused: BCF (-O b, -O u, a .bcf path in any case), a level past 9, a level
# on v, a bad type, a missing value; every -O must be valid.
def out_Ob() -> {B.Args.parse(["norm", "-Ob", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_Ou() -> {B.Args.parse(["norm", "-O", "u", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_bcf() -> {B.Args.parse(["norm", "-f", "r.fa", "-o", "x.BCF", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_z10() -> {B.Args.parse(["norm", "-Oz10", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_v5() -> {B.Args.parse(["norm", "-Ov5", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_bad_first() -> {B.Args.parse(["norm", "-Ox", "-Oz", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_noval() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "-o"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# As a value, -o is that option's value; any word is a path for -o.
def out_as_ref() -> {B.Args.parse(["norm", "-f", "-o", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "-o", "in.vcf"]}, "-o", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def out_path_word() -> {B.Args.output(["norm", "-o", "--threads", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{Some{"--threads"}, False{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

# B.Args.output: the extension decides when it names a type, else -O.
def sink_default() -> {B.Args.output(["norm", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, False{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_ext() -> {B.Args.output(["norm", "-f", "r.fa", "-o", "out.vcf.gz", "in.vcf"]) == Some{B.Sink{Some{"out.vcf.gz"}, True{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_ext_case() -> {B.Args.output(["norm", "-Ov", "-f", "r.fa", "-o", "OUT.Vcf.Bgz", "in.vcf"]) == Some{B.Sink{Some{"OUT.Vcf.Bgz"}, True{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_ext_plain() -> {B.Args.output(["norm", "-Oz9", "-f", "r.fa", "-o", "out.vcf", "in.vcf"]) == Some{B.Sink{Some{"out.vcf"}, False{}, 9n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_other_ext() -> {B.Args.output(["norm", "-O", "z3", "-f", "r.fa", "-o", "out.gz", "in.vcf"]) == Some{B.Sink{Some{"out.gz"}, True{}, 3n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_stdout_z() -> {B.Args.output(["norm", "-f", "r.fa", "in.vcf", "-Oz"]) == Some{B.Sink{None{}, True{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_dash() -> {B.Args.output(["norm", "-o", "out.vcf.gz", "-o", "-", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, False{}, 6n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_last() -> {B.Args.output(["norm", "-Oz1", "-f", "r.fa", "-Oz0", "in.vcf"]) == Some{B.Sink{None{}, True{}, 0n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_refused() -> {B.Args.output(["norm", "-Oz", "in.vcf"]) == None{} : Maybe<&2, B.Sink>}:
  {==}

def out_threads() -> {B.Args.threads(["norm", "-Oz", "--threads", "8", "-o", "x.vcf.gz", "-f", "r.fa", "in.vcf"]) == Some{8n} : Maybe<&2, Nat>}:
  {==}

# The level is sticky, as in bcftools 1.24: a later -Oz or -Ov keeps it.
def sink_sticky() -> {B.Args.output(["norm", "-Oz0", "-Oz", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, True{}, 0n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_sticky_v() -> {B.Args.output(["norm", "-Oz9", "-Ov", "-o", "x.vcf.gz", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{Some{"x.vcf.gz"}, True{}, 9n}} : Maybe<&2, B.Sink>}:
  {==}

def sink_level_last() -> {B.Args.output(["norm", "-Oz1", "-O", "z9", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, True{}, 9n}} : Maybe<&2, B.Sink>}:
  {==}

# More refused lines: -O with no value, a glued -oFILE, an invalid first -o.
def out_O_noval() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "-O"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_glued_o() -> {B.Args.parse(["norm", "-ox.vcf.gz", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_bad_first_o() -> {B.Args.parse(["norm", "-o", "a.bcf", "-o", "b.vcf", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# A VCF path "-o" waits for a value (refused); written ./-o it is the VCF.
def out_vcf_dash_o() -> {B.Args.parse(["norm", "-f", "r.fa", "-o"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def out_vcf_dot_o() -> {B.Args.parse(["norm", "-f", "r.fa", "./-o"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "./-o"]}, "r.fa", "./-o"}} : Maybe<&2, B.Cfg>}:
  {==}

# The words of one output option (law output's B.Args.out_opt).
def oo_o() -> {B.Args.out_opt(["-o", "a.vcf.gz"]) == True{} : Bool}:
  {==}

def oo_glued() -> {B.Args.out_opt(["-Oz5"]) == True{} : Bool}:
  {==}

def oo_sep() -> {B.Args.out_opt(["-O", "v"]) == True{} : Bool}:
  {==}

def oo_alone() -> {B.Args.out_opt(["-O"]) == False{} : Bool}:
  {==}

def oo_bcf() -> {B.Args.out_opt(["-o", "a.bcf"]) == False{} : Bool}:
  {==}

def oo_extra() -> {B.Args.out_opt(["-Oz", "x"]) == False{} : Bool}:
  {==}

# --- The index option (-W; law index) ---------------------------------------

# It changes nothing Args.parse returns, and is not recorded in the header.
def idx_header() -> {B.Args.parse(["norm", "-W", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

def idx_long() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "--write-index=tbi"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
  {==}

# Accepted with stdout or plain output too: Args.index says BadIdx, and the
# driver refuses it ("-W needs a BGZF -o file").
def idx_stdout_parse() -> {B.Args.parse(["norm", "-W", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
  {==}

# Refused: another format (bai, a format in upper case), an abbreviated long
# form; a format in the next word is that word (here a second VCF path).
def idx_bai() -> {B.Args.parse(["norm", "-Wbai", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def idx_upper() -> {B.Args.parse(["norm", "-W=TBI", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def idx_abbrev() -> {B.Args.parse(["norm", "--write", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

def idx_next_word() -> {B.Args.parse(["norm", "-W", "tbi", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
  {==}

# B.Args.index: the -o path with .csi or .tbi; the last -W counts.
def index_none() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.NoIdx{}} : Maybe<&2, B.Idx>}:
  {==}

def index_csi() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "-W", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

def index_tbi() -> {B.Args.index(["norm", "-Wtbi", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Tbi{}, "o.vcf.gz.tbi"}} : Maybe<&2, B.Idx>}:
  {==}

def index_last() -> {B.Args.index(["norm", "-W=tbi", "-f", "r.fa", "--write-index", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

def index_other_ext() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "-o", "out.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "out.gz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

# The type is Args.output's: -Ov with a .vcf.gz path is BGZF (indexed); -Oz
# with a .vcf path is plain (BadIdx).
def index_ext_wins() -> {B.Args.index(["norm", "-W", "-Ov", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

def index_plain_ext() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "-o", "o.vcf", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
  {==}

# Stdout (no -o, or -o -), and plain output to a file, cannot be indexed.
def index_stdout() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
  {==}

def index_dash() -> {B.Args.index(["norm", "-W", "-Oz", "-o", "-", "-f", "r.fa", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
  {==}

def index_plain() -> {B.Args.index(["norm", "-W", "-f", "r.fa", "-o", "out.txt", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
  {==}

def index_refused() -> {B.Args.index(["norm", "-W", "-o", "o.vcf.gz", "in.vcf"]) == None{} : Maybe<&2, B.Idx>}:
  {==}

# -W leaves the output and the thread count as they are.
def idx_sink() -> {B.Args.output(["norm", "-Oz1", "-W", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Sink{Some{"o.vcf.gz"}, True{}, 1n}} : Maybe<&2, B.Sink>}:
  {==}

def idx_threads() -> {B.Args.threads(["norm", "-W", "--threads", "4", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{4n} : Maybe<&2, Nat>}:
  {==}

# The index option, one word (law index's B.Args.idx_opt).
def io_forms() -> {(B.Args.idx_opt("-W") && B.Args.idx_opt("-Wcsi") && B.Args.idx_opt("-Wtbi") && B.Args.idx_opt("-W=csi") && B.Args.idx_opt("-W=tbi") && B.Args.idx_opt("--write-index") && B.Args.idx_opt("--write-index=csi") && B.Args.idx_opt("--write-index=tbi")) == True{} : Bool}:
  {==}

def io_not() -> {(B.Args.idx_opt("-W=") || B.Args.idx_opt("-Wbai") || B.Args.idx_opt("--write-index=") || B.Args.idx_opt("-w")) == False{} : Bool}:
  {==}

# The other BGZF extensions, in any case: the suffix is appended to the path
# as given.
def index_bgz() -> {B.Args.index(["norm", "-W", "-f", "r.fa", "-o", "x.vcf.bgz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "x.vcf.bgz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

def index_upper_ext() -> {B.Args.index(["norm", "-Wtbi", "-f", "r.fa", "-o", "x.VCF.GZ", "in.vcf"]) == Some{B.Idx{B.Tbi{}, "x.VCF.GZ.tbi"}} : Maybe<&2, B.Idx>}:
  {==}

# --write-index tbi: the format is not read from the next word, which is the
# VCF path (here the only one).
def idx_tbi_path() -> {B.Args.parse(["norm", "-f", "r.fa", "--write-index", "tbi"]) == Some{B.Cfg{B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "tbi"]}, "r.fa", "tbi"}} : Maybe<&2, B.Cfg>}:
  {==}

def index_tbi_path() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "--write-index", "tbi"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
  {==}

# The index is built on the output's Sink (B.Args.idx.mk): BGZF to a file is
# indexed, anything else with -W is BadIdx, no -W is NoIdx.
def idx_mk_file() -> {B.Args.idx.mk(Some{B.Tbi{}}, B.Sink{Some{"o.vcf.gz"}, True{}, 6n}) == B.Idx{B.Tbi{}, "o.vcf.gz.tbi"} : B.Idx}:
  {==}

def idx_mk_plain() -> {B.Args.idx.mk(Some{B.Csi{}}, B.Sink{Some{"o.vcf"}, False{}, 6n}) == B.BadIdx{} : B.Idx}:
  {==}

def idx_mk_stdout() -> {B.Args.idx.mk(Some{B.Csi{}}, B.Sink{None{}, True{}, 6n}) == B.BadIdx{} : B.Idx}:
  {==}

def idx_mk_none() -> {B.Args.idx.mk(None{}, B.Sink{Some{"o.vcf.gz"}, True{}, 6n}) == B.NoIdx{} : B.Idx}:
  {==}

# Law index_sink on two lines: the same output and thread count with and
# without -W.
def route_w() -> {M.route(["norm", "-Wtbi", "-Oz1", "--threads", "4", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == M.Route{Some{B.Sink{Some{"o.vcf.gz"}, True{}, 1n}}, Some{4n}} : M.Route}:
  {==}

def route_same() -> {M.route(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf", "--write-index=csi"]) == M.route(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) : M.Route}:
  {==}

# --- Whole runs ------------------------------------------------------------

def fa() -> String:
  ">c\nGAAAAT\n>d\nACGT\n"

def hdr() -> String:
  "##fileformat=VCFv4.2\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"

def added() -> String:
  "##fileformat=VCFv4.2\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -f r.fa\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"

def strict() -> B.Opts:
  B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa"]}

# A deletion moves to the start; a lower-case SNP is written in upper case.
def run_basic() -> {L.run(fa(), hdr() ++ "c\t4\t.\tAA\tA\t.\t.\t.\nc\t5\t.\ta\tg\t.\t.\t.\n", strict()) == R.Report{added() ++ "c\t1\t.\tGA\tG\t.\t.\t.\nc\t5\t.\tA\tG\t.\t.\t.\n", [B.Summary{2n, 2n, 0n, 0n}], 0n} : R.Report}:
  {==}

# A REF mismatch stops the run under -c e, after the header was written.
def run_mismatch() -> {L.run(fa(), hdr() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", strict()) == R.Report{added(), [B.Stop{B.RefMismatch{}, Some{B.At{3n, "c", "2"}}, None{}}], 1n} : R.Report}:
  {==}

# Under -c w it is passed through with a warning.
def run_mismatch_w() -> {L.run(fa(), hdr() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", B.Opts{False{}, 1000n, False{}, True{}, ["-f", "r.fa"]}) == R.Report{added() ++ "c\t2\t.\tC\tT\t.\t.\t.\n", [B.Warning{B.RefMismatch{}, B.At{3n, "c", "2"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# A record that moves before one read earlier comes out first.
def run_sorts() -> {L.run(fa(), hdr() ++ "c\t5\t.\tA\tG\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\tEND=5\n", strict()) == R.Report{added() ++ "c\t1\t.\tGA\tG\t.\t.\tEND=2\nc\t5\t.\tA\tG\t.\t.\t.\n", [B.Summary{2n, 1n, 0n, 0n}], 0n} : R.Report}:
  {==}

# With -w 1 the buffer writes early, so the same move stops the run.
def run_unsorted() -> {R.Report.code(L.run(fa(), hdr() ++ "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n", B.Opts{True{}, 1n, False{}, True{}, ["-f", "r.fa"]})) == 1n : Nat}:
  {==}

def run_unsorted_note() -> {R.Report.notes(L.run(fa(), hdr() ++ "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n", B.Opts{True{}, 1n, False{}, True{}, ["-f", "r.fa"]})) == [B.Stop{B.Unsorted{}, Some{B.At{5n, "c", "4"}}, Some{B.At{3n, "c", "2"}}}] : List<&2, B.Note>}:
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
  B.Opts{True{}, 1000n, False{}, True{}, ["-f", "r.fa", "in.vcf"]}

def body1() -> String:
  "c\t4\t.\tAA\tA\t.\t.\t.\nc\t5\t.\ta\tg\t.\t.\t.\n"

def body2() -> String:
  "c\t5\t.\tA\tG\t.\t.\t.\r\nc\t4\t.\tAA\tA\t.\t.\tEND=5\r\nzz\t1\t.\tA\t<DEL>\t.\t.\t.\r\nd\t2\t.\tC\tT\t.\t.\t.\r\nd\t3\t.\tGT\tG\t.\t.\t.\r\nd\t1\t.\tA\tA,G\t.\t.\t."

def body3() -> String:
  "c\t2\t.\tA\tG\t.\t.\t.\nc\t3\t.\tA\tC\t.\t.\t.\nc\t4\t.\tAA\tA\t.\t.\t.\n"

def m_usage() -> {Norm.start(["norm", "in.vcf"]) == Norm.Usage{} : Norm.Begin}:
  {==}

# ==========================================================================
# Splitting multiallelic records (-m)
# ==========================================================================

# B.Rec.parts against bcftools 1.24 norm -m -any (cases in notes/split.md),
# and split_problem against B.Rec.parts on every case (law split_when).

def defs() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n")

def defs2() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##INFO=<ID=TA, Number=A, Type=Integer,Description=\"space after commas\">\n##INFO=<ID=TB,Number=A ,Type=Integer,Description=\"space before a comma\">\n##INFO=<ID=TC ,Number=A,Type=Integer,Description=\"space after the ID\">\n##INFO=<ID=TD,Number= A,Type=Integer,Description=\"space after =\">\n##INFO=<ID=TE,Number=A,Type=Integer,Description=\"x, y\" >\n##INFO=<ID=TG,Number=A\t,Type=Integer,Description=\"a tab\">\n##INFO=<ID=TP,Number=P,Type=String,Description=\"per copy\">\n##INFO=<ID=TF,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=NN,Type=String,Description=\"no Number\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=LAA,Number=.,Type=Integer,Description=\"local alleles\">\n##FORMAT=<ID=LAD,Number=LR,Type=Integer,Description=\"local depths\">\n")

def defs3() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n")

def m(o: Bool) -> B.Opts:
  B.Opts{True{}, 1000n, True{}, o, ["-m", "-any"]}

def ex_gt_ref() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT\t1/0\t0/0\t0/0\t1|0\t0|1\t0\t1\t0\t.\t./.\t.|.\t1/.\t./0\t.|0\t0/0\t1/1\t1/0/0\t0/0/0\t0/1\t1/0\t0/0\t0|0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT\t0/1\t0/1\t1/1\t0|1\t1|0\t1\t0\t0\t.\t./.\t.|.\t0/.\t./1\t.|1\t0/0\t0/0\t0/1/1\t0/0/0\t1/0\t0/0\t0/0\t0|0", "c1\t25\t.\tC\tA\t.\t.\t.\tGT\t0/0\t0/0\t0/0\t0|0\t0|0\t0\t0\t0\t.\t./.\t.|.\t0/.\t./0\t.|0\t0/0\t0/0\t0/0/0\t0/0/1\t0/0\t0/1\t1/1\t0|0"]} : B.Parts}:
  {==}

def when_gt_ref() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_gt_dot() -> {B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT\t1/.\t0/.\t./.\t1|.\t.|1\t.\t1\t0\t.\t./.\t.|.\t1/.\t./.\t.|.\t0/0\t1/1\t1/./.\t0/0/.\t./1\t1/.\t./.\t0|0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT\t./1\t0/1\t1/1\t.|1\t1|.\t1\t.\t0\t.\t./.\t.|.\t./.\t./1\t.|1\t0/0\t./.\t./1/1\t0/0/.\t1/.\t./.\t./.\t0|0", "c1\t25\t.\tC\tA\t.\t.\t.\tGT\t./.\t0/.\t./.\t.|.\t.|.\t.\t.\t0\t.\t./.\t.|.\t./.\t./.\t.|.\t0/0\t./.\t././.\t0/0/1\t./.\t./1\t1/1\t0|0"]} : B.Parts}:
  {==}

def when_gt_dot() -> {L.refusal(B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info0() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=1;FA=0.1;SA=x;IR=10,11;SR=r,a;IG=0,1,2;SG=g0,g1,g2;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL", "c1\t25\t.\tC\tT\t.\t.\tIA=2;FA=0.0025;SA=y;IR=10,12;SR=r,b;IG=0,3,5;SG=g0,g3,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL"]} : B.Parts}:
  {==}

def when_info0() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info1() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c") == B.Pieces{["c1\t26\trs7\tG\tA\t9\tq10\tIA=1;FA=.;SA=x;IR=.,1;SR=r,.", "c1\t26\trs7\tG\tC\t9\tq10\tIA=.;FA=0.333333;SA=.;IR=.,2;SR=r,b", "c1\t26\trs7\tG\tT\t9\tq10\tIA=3;FA=1e+10;SA=z;IR=.,3;SR=r,c"]} : B.Parts}:
  {==}

def when_info1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c")) == Some{L.split_problem(defs(), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info2() -> {B.Rec.parts(defs(), m(True{}), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28") == B.Pieces{["c1\t28\t.\tA\tC\t.\t.\tFA=0.123457;IR=1,2;IG=1,2,3;END=28", "c1\t28\t.\tA\tG\t.\t.\tFA=1;IR=1,3;IG=1,4,6;END=28"]} : B.Parts}:
  {==}

def when_info2() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28")) == Some{L.split_problem(defs(), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_fmt0() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/0:1,2:0,1,2:0.10:9:4,5\t0:4,5:7,8:.:.:.\t./.:.:.:.:.:.\t0/1:7,.:.,1,2:1:3\t0/0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t0/1:1,3:0,3,5:0.2:9:4,5\t1:4,6:7,9:1e10:.:.\t./.:.:.:.:.:.\t0/0:7,9:.,3,5:.:3\t0/0"]} : B.Parts}:
  {==}

def when_fmt0() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_fmt1() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1") == B.Pieces{["c1\t26\t.\tG\tA\t.\t.\t.\tGT:SA:SR:SG\t1/0:a:r,a:0,1,2\t0:x:r,x:h0,h1\t.:.:.:.\t0/1:p:.,1:.\t1", "c1\t26\t.\tG\tC\t.\t.\t.\tGT:SA:SR:SG\t0/0:b:r,b:0,3,5\t1:y:r,y:h0,h2\t.:.:.:.\t0/0:.:.,.:.\t0", "c1\t26\t.\tG\tT\t.\t.\t.\tGT:SA:SR:SG\t0/1:c:r,c:0,6,9\t0:z:r,z:h0,h3\t.:.:.:.\t0/0:q:.,3:.\t0"]} : B.Parts}:
  {==}

def when_fmt1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1")) == Some{L.split_problem(defs(), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_order() -> {B.Rec.parts(defs(), m(True{}), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2") == B.Pieces{["c1\t20\tx\tG\tA\t.\t.\t.\tAD:GT\t1,2:1/0", "c1\t20\tx\tG\tC\t.\t.\t.\tAD:GT\t1,3:0/1"]} : B.Parts}:
  {==}

def when_order() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2")) == Some{L.split_problem(defs(), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_lone_dot() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/0:.:.", "c1\t25\t.\tC\tT\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t0/1:.:."]} : B.Parts}:
  {==}

def when_lone_dot() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_bi() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1") == B.Whole{} : B.Parts}:
  {==}

def ex_mal() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,,T\t.\t.\t.") == B.Whole{} : B.Parts}:
  {==}

def ex_u_flag() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tXY;IA=1", "c1\t25\t.\tC\tT\t.\t.\tXY;IA=2"]} : B.Parts}:
  {==}

def when_u_flag() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_empty1() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=1;", "c1\t25\t.\tC\tT\t.\t.\tIA=2;"]} : B.Parts}:
  {==}

def when_empty1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_empty2() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4") == B.Pieces{["c1\t26\t.\tG\tA\t.\t.\t;IA=1;;I1=4", "c1\t26\t.\tG\tT\t.\t.\t;IA=2;;I1=4"]} : B.Parts}:
  {==}

def when_empty2() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4")) == Some{L.split_problem(defs(), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_nogt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tDP:PL\t3:0,1,2", "c1\t25\t.\tC\tT\t.\t.\t.\tDP:PL\t3:0,3,5"]} : B.Parts}:
  {==}

def when_pl_nogt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dotgt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:0,1,2\t1:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t.:0,3,5\t0:7,9"]} : B.Parts}:
  {==}

def when_pl_dotgt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dot_hap() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t.:7,9"]} : B.Parts}:
  {==}

def when_pl_dot_hap() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_hap_dot_over() -> {B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t1:7,9"]} : B.Parts}:
  {==}

def when_hap_dot_over() -> {L.refusal(B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_gtafter() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tPL:GT\t7,8:0", "c1\t25\t.\tC\tT\t.\t.\t.\tPL:GT\t7,9:1"]} : B.Parts}:
  {==}

def when_pl_gtafter() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_altref() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2") == B.Pieces{["c1\t12\t.\tA\tC\t.\t.\t.\tGT\t1/0", "c1\t12\t.\tA\tA\t.\t.\t.\tGT\t0/1"]} : B.Parts}:
  {==}

def when_altref() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_nogtdef() -> {B.Rec.parts(defs3(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:AD\t1/0:1,2", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:AD\t0/1:1,3"]} : B.Parts}:
  {==}

def when_nogtdef() -> {L.refusal(B.Rec.parts(defs3(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3")) == Some{L.split_problem(defs3(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_trim() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tTA=1;TB=3;TC=5;TD=7;TP=a,b;TF;TE=9\tGT:LAA\t1/0:1,2", "c1\t25\t.\tC\tT\t.\t.\tTA=2;TB=4;TC=6;TD=8;TP=a,b;TF;TE=10\tGT:LAA\t0/1:1,2"]} : B.Parts}:
  {==}

def when_trim() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_info() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2") == B.Unsplit{B.UndefinedTag{"INFO/XX"}} : B.Parts}:
  {==}

def when_u_info() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_fmt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2") == B.Unsplit{B.UndefinedTag{"FORMAT/ZZ"}} : B.Parts}:
  {==}

def when_u_fmt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_tab() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2") == B.Unsplit{B.UndefinedTag{"INFO/TG"}} : B.Parts}:
  {==}

def when_u_tab() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_nonum() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b") == B.Unsplit{B.UndefinedTag{"INFO/NN"}} : B.Parts}:
  {==}

def when_u_nonum() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_lr() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7") == B.Unsplit{B.UndefinedTag{"FORMAT/LAD"}} : B.Parts}:
  {==}

def when_u_lr() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ia() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ia() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ia3() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ia3() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_sa() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_sa() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_key() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_key() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ad() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ad() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl4() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl4() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_dip3() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_dip3() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_hap6() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_hap6() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_trip() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_trip() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_more() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_more() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_hi() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_hi() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_x() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_x() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_lead() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_lead() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_zero() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_zero() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_plus() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_plus() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup_case() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup_case() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup_sym() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup_sym() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dot_bad() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_pl_dot_bad() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_order_code() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_order_code() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

# A whole run with -m: split, each record normalized, then sorted (bcftools 1.24 writes the same records).
def ex_run() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", m(True{})) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t8\trs1\tTCA\tT\t50\tPASS\tI1=7\tGT\t1/0\nc1\t8\trs1\tT\tTCA\t50\tPASS\tI1=7\tGT\t0/1\nc1\t15\trs2;rs3\tCAG\tC\t.\tq10\t.\tGT\t1|0\nc1\t16\trs2;rs3\tA\tT\t.\tq10\t.\tGT\t0|1\nc1\t21\t.\tT\tA\t3.5\t.\tFL\tGT\t0/0\nc1\t21\t.\tT\tC\t3.5\t.\tFL\tGT\t0/0\nc1\t21\t.\tT\tG\t3.5\t.\tFL\tGT\t0/1\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", [B.Summary{8n, 3n, 0n, 0n}], 0n} : R.Report}:
  {==}

# Under -c w a line that cannot be split passes as it came, with a warning naming the tag.
def ex_run_unsplit_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", [B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# Under -c e it stops the run.
def ex_run_unsplit_e() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{True{}, 1000n, True{}, True{}, ["-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.UndefinedTag{"INFO/XX"}, Some{B.At{28n, "c1", "25"}}, None{}}], 1n} : R.Report}:
  {==}

# A line that cannot be split and whose CHROM is not in the reference stops with UNKNOWN_CHROM under -c w too, as without -m (item 7).
def ex_run_unknown_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nzz\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.UnknownChrom{}, Some{B.At{28n, "zz", "25"}}, None{}}], 1n} : R.Report}:
  {==}

# Two equal ALTs: ALT_DUP, as without -m (item 8).
def ex_run_dup_e() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2\n", B.Opts{True{}, 1000n, True{}, True{}, ["-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.AltDup{}, Some{B.At{28n, "c1", "12"}}, None{}}], 1n} : R.Report}:
  {==}

# Two equal symbolic ALTs: out of scope without -m, but -m cannot split them (decision 20): under -c w, ALT_DUP, not split.
def ex_run_dup_sym_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2\n", [B.Warning{B.DupAlts{}, B.At{28n, "c1", "12"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# A split refused for two equal ALTs says it was not split; judge's ALT_DUP (no -m) is unchanged.
def ex_render_dup() -> {B.Note.render(B.Warning{B.DupAlts{}, B.At{28n, "c1", "12"}}) == "ALT_DUP\tc1\t12\tline 28\tnot split\n" : String}:
  {==}

# Under -c w, a line that cannot be split and whose REF does not match reports only the split code (decision 22, documented).
def ex_run_unsplit_mismatch_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tA\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tA\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", [B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# The warning names the tag and the fix.
def ex_render() -> {B.Note.render(B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}) == "UNDEFINED_TAG\tc1\t25\tline 28\tINFO/XX has no usable header line (add one, e.g. with bcftools annotate -h); not split\n" : String}:
  {==}

# Messages of the other codes are as before.
def ex_render_old() -> {B.Note.render(B.Warning{B.RefMismatch{}, B.At{28n, "c1", "25"}}) == "REF_MISMATCH\tc1\t25\tline 28\n" : String}:
  {==}

# Law biallelic_run on one file.
def ex_biallelic_run() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1\nc1\t12\t.\tACA\tA\t.\t.\t.\tGT\t1/1\n", m(True{})) == L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1\nc1\t12\t.\tACA\tA\t.\t.\t.\tGT\t1/1\n", L.no_m(m(True{}))) : R.Report}:
  {==}

# Law items_without_m on one file.
def ex_items_without_m() -> {L.out_items(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", L.no_m(m(True{}))) == L.items(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n") : List<&2, R.Item>}:
  {==}

# Law split_change for ALT 1: the record written (moved to 8, TCA T) makes ALT 1's change.
def ex_split_change1() -> {L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA\t50\tPASS\tI1=7\tGT\t1/0")) == L.one_of(List.get(&2, List<&2, B.Base>, L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2"), 0n)) : List<&2, List<&2, B.Base>>}:
  {==}

# Law split_change for ALT 2 (T TCA at 8).
def ex_split_change2() -> {L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tACACA\t50\tPASS\tI1=7\tGT\t0/1")) == L.one_of(List.get(&2, List<&2, B.Base>, L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2"), 1n)) : List<&2, List<&2, B.Base>>}:
  {==}

# What written gives: the normalized record.
def ex_written_moves() -> {L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA\t50\tPASS\tI1=7\tGT\t1/0") == "c1\t8\trs1\tTCA\tT\t50\tPASS\tI1=7\tGT\t1/0" : String}:
  {==}

# A carriage return inside a line to split (BAD_CR), on a toy reference
# (contig 1 = ACGTACGTACGTACGTACGT).

def REF() -> String:
  ">1\nACGTACGTACGTACGTACGT\n"

def HDR() -> String:
  "##fileformat=VCFv4.2\n##contig=<ID=1>\n##INFO=<ID=END,Number=A,Type=Integer,Description=\"x\">\n##INFO=<ID=AF,Number=A,Type=String,Description=\"x\">\n"

def CHR() -> String:
  "#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"

def ADDED(+cmd: String) -> String:
  "##framebender_normVersion=0.1.0\n##framebender_normCommand=norm" ++ cmd ++ "\n"

# The counterexample's line (t2.vcf): a CR inside the END values.
def X1() -> String:
  "1\t05\t.\tA\tC,G\t.\t.\tEND=5\r,6"

# A CR inside the AF values; nothing else wrong with the line.
def X2() -> String:
  "1\t2\t.\tC\tA,G\t.\t.\tAF=0.1\r,0.2"

# One ALT and a CR: not a line to split.
def X3() -> String:
  "1\t2\t.\tC\tA\t.\t.\tAF=0.1\r"

def OW() -> B.Opts:
  B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}

def OE() -> B.Opts:
  B.Opts{True{}, 1000n, True{}, True{}, ["-m", "-any"]}

def DEFS() -> B.Defs:
  L.defs(HDR() ++ CHR())

# A line to split with a CR: refused, BAD_CR.
def cr_parts1() -> {B.Rec.parts(DEFS(), OW(), X1()) == B.Unsplit{B.BadCr{}} : B.Parts}:
  {==}

def cr_parts2() -> {B.Rec.parts(DEFS(), OW(), X2()) == B.Unsplit{B.BadCr{}} : B.Parts}:
  {==}

# split_problem says the same (law split_when).
def cr_problem1() -> {L.split_problem(DEFS(), X1()) == Some{B.BadCr{}} : Maybe<&2, B.Code>}:
  {==}

# A line with one ALT is not split: whole, CR or not (as today).
def cr_bi() -> {B.Rec.parts(DEFS(), OW(), X3()) == B.Whole{} : B.Parts}:
  {==}

# Under -c w the line passes as it came, with a BAD_CR warning.
def cr_run_w() -> {L.run(REF(), HDR() ++ CHR() ++ X2() ++ "\n", OW()) ==
  R.Report{HDR() ++ ADDED(" -c w -m -any") ++ CHR() ++ X2() ++ "\n", [B.Warning{B.BadCr{}, B.At{6n, "1", "2"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# Under -c e it stops the run with BAD_CR.
def cr_run_e() -> {L.run(REF(), HDR() ++ CHR() ++ X2() ++ "\n", OE()) ==
  R.Report{HDR() ++ ADDED(" -m -any") ++ CHR(), [B.Stop{B.BadCr{}, Some{B.At{6n, "1", "2"}}, None{}}], 1n} : R.Report}:
  {==}

# Decision 7's precedence: the whole line's own outcome stops first. The
# counterexample's line is BAD_END as a whole (END "5\r,6"), so under -c e it
# stops with BAD_END, as without -m.
def cr_run_e_end() -> {L.run(REF(), HDR() ++ CHR() ++ X1() ++ "\n", OE()) ==
  R.Report{HDR() ++ ADDED(" -m -any") ++ CHR(), [B.Stop{B.BadEnd{}, Some{B.At{6n, "1", "05"}}, None{}}], 1n} : R.Report}:
  {==}

# The counterexample under -c w: passed as it came (BAD_CR) ...
def cr_run_w1() -> {L.run(REF(), HDR() ++ CHR() ++ X1() ++ "\n", OW()) ==
  R.Report{HDR() ++ ADDED(" -c w -m -any") ++ CHR() ++ X1() ++ "\n", [B.Warning{B.BadCr{}, B.At{6n, "1", "05"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# ... and run again on its own output, the same body (law twice_run).
def cr_twice() -> {L.body(R.Report.out(L.run(REF(), R.Report.out(L.run(REF(), HDR() ++ CHR() ++ X1() ++ "\n", OW())), OW()))) ==
  L.body(R.Report.out(L.run(REF(), HDR() ++ CHR() ++ X1() ++ "\n", OW()))) : String}:
  {==}
