import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import lawful-bytes@0.1.1.0/defs.bend as D
import ./norm.bend as Norm

# Counterexamples to deliverables of proof_b_run.bend, run on concrete
# values (`bend proof_b_run_cex.bend`; notes/bytes_proofs_run.md explains
# them). Each ex_* is True when the machine (NR.to_spec of its run, which
# run_to_spec equates with P.specRun) agrees with run.bend; main lists them.
#   A, B: after an UNSORTED stop, buf and last differ (body-line deliverables).
#   C, F: run_head_write on a run with bytes already in ob.
#   D:    run_same before the first CHROM run with an empty CHROM.
#   E:    a body line on a stopped run (run.bend still writes it).
#   G:    run_finish with no #CHROM line after a written body line.
#   H:    (round 2, after the first fixes; True is the counterexample)
#         run_same after run_same_done with a non-byte At CHROM.

def fst(p: NR.Run & D.Bytes) -> NR.Run:
  (r, b) = p
  r

def opts(+w: Nat) -> B.Opts:
  B.Opts{False{}, w, Nil{}}

# One record through the machine (same_done, the slow path's Same).
def m_line(r: NR.Run, +w: Nat, +n: Nat, +chrom: String, +pos: Nat) -> NR.Run:
  +t = chrom ++ "\t" ++ Nat.show(pos) ++ "\n"
  fst(NR.same_done(NR.tick(r), opts(w), B.At{n, chrom, Nat.show(pos)}, pos, E.enc(t), 0, U32.from_nat(String.length(t))))

# The same record through run.bend (what run_same_done compares with).
def s_line(st: R.RunSt, +w: Nat, +n: Nat, +chrom: String, +pos: Nat) -> R.RunSt:
  +body = chrom ++ "\t" ++ Nat.show(pos)
  R.body_line(B.Res{B.Normalized{}, pos, body, False{}}, R.tick(st), opts(w), B.Line{body, "\n"}, B.At{n, chrom, Nat.show(pos)}, pos)

def keys(xs: List<&2, R.Item>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case R.Item{k, p, a, t} <> rest:
      k <> keys(rest)

def lastk(m: Maybe<&2, R.Item>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{R.Item{k, p, a, t}}:
      Some{k}

def nl_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      Nat.is_eq(x, y) && nl_eq(xs, ys)
    case _ _:
      False{}

def mn_eq(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Nat.is_eq(x, y)
    case _ _:
      False{}

# The machine's run (as a RunSt) and run.bend's agree on halt, last's key
# and the buffer's keys.
def same(a: R.RunSt, b: R.RunSt) -> Bool:
  match a b:
    case R.RunSt{n, i, h, c, e, l, bf, k, o, ns, x} R.RunSt{n2, i2, h2, c2, e2, l2, bf2, k2, o2, ns2, x2}:
      Bool.not(Bool.xor(x, x2)) && (mn_eq(lastk(l), lastk(l2)) && nl_eq(keys(bf), keys(bf2)))

# halt (1/0), last's key (0: None), then the buffer's keys.
def pic(st: R.RunSt) -> List<&2, Nat>:
  match st:
    case R.RunSt{n, i, h, c, e, l, bf, k, o, ns, x}:
      Bool.pick(Nat, x, 1n, 0n) <> (Maybe.default(&2, Nat, lastk(l), 0n) <> keys(bf))

# A: chr1:100, chr2:100, chr1:200 with w = 1000 (nothing ready): the third
# line starts chr1's run again (UNSORTED). run.bend keeps buf = [chr2:100]
# and last = None; the machine has written chr2:100 (buf [], last 100).
def ex_a() -> Bool:
  m = m_line(m_line(m_line(NR.start(), 1000n, 1n, "chr1", 100n), 1000n, 2n, "chr2", 100n), 1000n, 3n, "chr1", 200n)
  s = s_line(s_line(s_line(R.start_st(), 1000n, 1n, "chr1", 100n), 1000n, 2n, "chr2", 100n), 1000n, 3n, "chr1", 200n)
  same(NR.to_spec(m), s)

# B: one CHROM, w = 10: 100, 200, 50, 300. At 300 the buffer is front [50,
# 200] + back [300] and 50 is below the last written key (100): UNSORTED.
# run.bend's buf is []; the machine keeps back = [300].
def ex_b() -> Bool:
  m = m_line(m_line(m_line(m_line(NR.start(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n), 10n, 4n, "c", 300n)
  s = s_line(s_line(s_line(s_line(R.start_st(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n), 10n, 4n, "c", 300n)
  same(NR.to_spec(m), s)

# B after three lines (before the stop): the two agree.
def ex_b3() -> Bool:
  m = m_line(m_line(m_line(NR.start(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n)
  s = s_line(s_line(s_line(R.start_st(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n)
  same(NR.to_spec(m), s)

def pics_a() -> List<&2, List<&2, Nat>>:
  m = m_line(m_line(m_line(NR.start(), 1000n, 1n, "chr1", 100n), 1000n, 2n, "chr2", 100n), 1000n, 3n, "chr1", 200n)
  s = s_line(s_line(s_line(R.start_st(), 1000n, 1n, "chr1", 100n), 1000n, 2n, "chr2", 100n), 1000n, 3n, "chr1", 200n)
  [pic(NR.to_spec(m)), pic(s)]

def pics_b() -> List<&2, List<&2, Nat>>:
  m = m_line(m_line(m_line(m_line(NR.start(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n), 10n, 4n, "c", 300n)
  s = s_line(s_line(s_line(s_line(R.start_st(), 10n, 1n, "c", 100n), 10n, 2n, "c", 200n), 10n, 3n, "c", 50n), 10n, 4n, "c", 300n)
  [pic(NR.to_spec(m)), pic(s)]

def outs(st: R.RunSt) -> String:
  match st:
    case R.RunSt{n, i, h, c, e, l, bf, k, o, ns, x}:
      o

def both(+a: R.RunSt, +b: R.RunSt) -> Bool:
  same(a, b) && String.eq(outs(a), outs(b))

def m_head(r: NR.Run) -> NR.Run:
  NR.head_line(True{}, NR.tick(r), opts(1000n), B.Line{"#CHROM", "\n"})

def s_head(st: R.RunSt) -> R.RunSt:
  R.head_line(True{}, R.tick(st), opts(1000n), B.Line{"#CHROM", "\n"})

# C: two #CHROM lines through run_head_write: run.bend's out is the second
# header only; the machine's is both.
def ex_c() -> Bool:
  String.eq(outs(NR.to_spec(m_head(m_head(NR.start())))), outs(s_head(s_head(R.start_st()))))

# D: run_same before the first CHROM run (cur None, cb empty) with an empty
# CHROM (s = e0): q is True, so the claim reads Some{""} == None.
def q_of(p: NR.Run & (D.Bytes & Bool)) -> Bool:
  (r, q) = p
  (b, ok) = q
  ok

def ex_d() -> Bool:
  Bool.not(q_of(Norm.Run.same(NR.start(), E.enc("x"), 0, 0)))

# E: w = 0: c:100, c:50 (UNSORTED: both agree here), then c:200 on the
# stopped run: run.bend writes it (out grows), the machine does not.
def ex_e2() -> Bool:
  m = m_line(m_line(NR.start(), 0n, 1n, "c", 100n), 0n, 2n, "c", 50n)
  s = s_line(s_line(R.start_st(), 0n, 1n, "c", 100n), 0n, 2n, "c", 50n)
  same(NR.to_spec(m), s)

def ex_e() -> Bool:
  m = m_line(m_line(m_line(NR.start(), 0n, 1n, "c", 100n), 0n, 2n, "c", 50n), 0n, 3n, "c", 200n)
  s = s_line(s_line(s_line(R.start_st(), 0n, 1n, "c", 100n), 0n, 2n, "c", 50n), 0n, 3n, "c", 200n)
  both(NR.to_spec(m), s)

# F: a body line before the #CHROM line (inbody False; w = 1000, so it waits
# in the buffer), then the #CHROM line: run.bend's out is the header, the
# machine's is the record's text then the header.
def ex_f() -> Bool:
  String.eq(outs(NR.to_spec(m_head(m_line(NR.start(), 1000n, 1n, "c", 100n)))), outs(s_head(s_line(R.start_st(), 1000n, 1n, "c", 100n))))

def fin_run(p: NR.Run & Nat) -> NR.Run:
  (r, c) = p
  r

# G: w = 0, a body line before any #CHROM line (written at once), then the
# end: run.bend's report has out "" (NO_HEADER), the machine's out is the
# record.
def ex_g() -> Bool:
  m = fin_run(NR.finish(m_line(NR.start(), 0n, 1n, "c", 100n), 0n))
  s = s_line(R.start_st(), 0n, 1n, "c", 100n)
  String.eq(outs(NR.to_spec(m)), R.Report.out(R.finish(s)))

# H: run_same_done with a line whose At has CHROM "\u0100" (a Char above
# 255; the statement ties only the line's text to bytes, not at): new_run
# stores of_str(chrom) as cb, which cannot hold that Char. run_same then
# passes on a buffer holding cb's bytes, but its text is not the CHROM.
def cb_text(r: NR.Run) -> String:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      NR.chars(D.view(cb))

def h_run() -> NR.Run:
  +t = {"x\t1\n" : String}
  +chrom = {SCon{Chr{256}, ""} : String}
  fst(NR.same_done(NR.tick(m_head(NR.start())), opts(1000n), B.At{2n, chrom, "1"}, 1n, E.enc(t), 0, U32.from_nat(String.length(t))))

# True: run_same's q is True (a pass) though btext is not the CHROM.
def ex_h() -> Bool:
  +ct = cb_text(h_run())
  q_of(Norm.Run.same(h_run(), E.enc(ct), 0, U32.from_nat(String.length(ct)))) && Bool.not(String.eq(ct, SCon{Chr{256}, ""}))

# Expected [False, True, False, False, False, True, False, False, False, True]:
# every False is a counterexample; ex_b3 and ex_e2 agree (the states before).
def main() -> List<&2, Bool>:
  [ex_a(), ex_b3(), ex_b(), ex_c(), ex_d(), ex_e2(), ex_e(), ex_f(), ex_g(), ex_h()]
