import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-halves@0.1.0.0/defs.bend as HD
import lawful-halves@0.1.0.0/halves.bend as HH

# framebender: the parallel machine (code; not yet proven, see
# notes/parallel.md). It runs norm.bend's machine (Q) unchanged and, once Q
# is in the body with nothing left to do, handles the VCF in batches:
#
# 1. Collect: up to kmax() pieces of at least minp() bytes are taken without
#    being read (each Chunk answers More); the end of the file or a shorter
#    piece (taken as the last) closes a batch early. The driver sizes the
#    batches: it sends an empty piece after every --threads N pieces.
# 2. Plan: for each piece of at least minp() bytes, the CHROM and POS of its
#    first and last complete lines (after its first LF); one Ask with two
#    reads per such piece (none if there is no such piece).
# 3. Run: one task per piece (lawful-halves' H.all, in parallel). A task runs
#    Q's pump on the piece's lines after its first LF, from a fresh run whose
#    CHROM is the first line's and whose last written key is l (a phantom,
#    above any key the task can write first: the task stops, UNSORTED, at
#    its first write, and runs once more from the key it stopped at, which
#    the merge checks against the true run's). It is clean when every complete line is handled on bytes,
#    with no stop and no read its windows do not answer (its warnings, -c w,
#    are kept, numbered from its first line).
# 4. Combine, in order: the line across the boundary is handled by Q on the
#    true state; then a clean task whose run fits the true one (merge.ok) is
#    spliced in, the true run's output and messages handed out in this step
#    (the task's messages, renumbered, stay in the spliced run); any other
#    piece is handled by Q itself, asking for reads as Q does. One piece per
#    step: each P.Ask{[]} gets the next one.

# ---------------------------------------------------------------------------
# The state
# ---------------------------------------------------------------------------

# A clean task: its run, the end of its last line not complete, its last
# window, the piece's first LF, the first line's CHROM and the phantom key.
type Tc is Type:
  Tc{run: NR.Run, pend: Q.Pd, win: Q.Win, k: U32, c0: String, l: Nat}

# A task's result: dirty, clean, or (from its first run only) stopped as
# UNSORTED against the phantom, by an item of key l: the task runs again
# from l, with the window w and the spare ones ws (task.again).
type TRes is Type:
  TDirty{}
  TClean{c: Tc}
  TAgain{l: Nat, w: Q.Win, ws: List<&1, Q.Win>}

# A task's result, with its piece (handed back by the task when it ran on it).
type TOut is Type:
  TOut{b: D.Bytes, r: TRes}

# A planned piece: its bytes, its two reads (one window each), whether it has a
# complete line after its first LF (with a tab), that LF, the line's CHROM
# and POS.
type Pl is Type:
  Pl{b: D.Bytes, rs: List<&2, P.Req>, ok: Bool, k: U32, c0: String, l: Nat}

# The batch: none; collecting (pieces newest first, how many); waiting for
# its answers; combining (seq: Q is in the middle of a piece).
type Bat is Type:
  BNone{}
  BCol{ps: List<&1, D.Bytes>, k: Nat}
  BAsk{pls: List<&1, Pl>, eofp: Bool}
  BComb{pcs: List<&1, TOut>, eofp: Bool, seq: Bool}

type St is Type:
  St{q: Q.St, bat: Bat}

type Begin is Type:
  Begin{st: St, ref: String, vcf: String}
  Usage{}

type Step is Type:
  Step{st: St, out: D.Bytes, notes: List<&2, B.Note>, next: P.Next}

# A backward search: the buffer, where it is, whether to go on, whether the
# byte at i is an LF.
type Rl is Type:
  Rl{b: D.Bytes, i: U32, more: Bool, hit: Bool}

# A number read forward: the buffer, the next index, the value so far,
# whether to go on.
type Nm is Type:
  Nm{b: D.Bytes, j: U32, acc: U32, more: Bool}

# A line's CHROM and POS, if it has a tab.
type Cp is Type:
  Cp{b: D.Bytes, ok: Bool, c: String, p: Nat}

# Where a task's piece is: still Q's input, from some point on (PIn), or
# held by the task once Q's input is a copy of the piece's last partial line
# (PHeld).
type Ph is Type:
  PIn{}
  PHeld{b: D.Bytes}

# A task's loop: go on from st (spare: the windows not tried yet), or done
# (with the piece).
type Tk is Type:
  TGo{st: Q.St, spare: List<&1, Q.Win>, ph: Ph}
  TEnd{r: TOut}

# Q after an advance on the boundary line: at the piece from k+1 (ok: with
# nothing else waiting), or not yet.
type Ew is Type:
  EHere{q: Q.St, c: Tc, ok: Bool}
  EMore{q: Q.St, c: Tc}
  EWant{st: Q.St, reqs: List<&2, P.Req>, c: Tc}
  EOther{a: Q.Adv}

type Mg is Type:
  MOk{out: D.Bytes, notes: List<&2, B.Note>, run: NR.Run}
  MNo{run: NR.Run}

# ---------------------------------------------------------------------------
# Start
# ---------------------------------------------------------------------------

# The most pieces a batch takes: B.Args.max_threads(), so the driver's empty
# pieces (after every N of them) close each batch.
def kmax() -> Nat:
  128n

# The smallest piece a batch takes (bytes). Each batched piece costs a few
# driver steps and reads more than Q would spend on it; a piece this long
# always has room for them in MACHINE.bend's bound. A shorter piece ends the
# batch (as its last piece, left to Q) or is left to Q.
def minp() -> U32:
  256

def start.k(b: Q.Begin) -> Begin:
  match b:
    case Q.Begin{st, r, v}:
      Begin{St{st, BNone{}}, r, v}
    case Q.Usage{}:
      Usage{}

# The command line after the program's name.
def start(argv: List<&2, String>) -> Begin:
  start.k(Q.start(argv))

def wrap(s: Q.Step, bat: Bat) -> Step:
  match s:
    case Q.Step{st, o, ns, nx}:
      Step{St{st, bat}, o, ns, nx}

# ---------------------------------------------------------------------------
# Q's state, looked at
# ---------------------------------------------------------------------------

def is_nil.src(src: List<&1, Q.Src>) -> List<&1, Q.Src> & Bool:
  match src:
    case Nil{}:
      (Nil{}, True{})
    case h <> t:
      (h <> t, False{})

def is_pb(p: Q.Pd) -> Q.Pd & Bool:
  match p:
    case Q.PB{b}:
      (Q.PB{b}, True{})
    case Q.PS{s}:
      (Q.PS{s}, False{})

def is_none(m: Maybe<&2, List<&2, P.Req>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def run.ok(r: NR.Run) -> NR.Run & Bool:
  match r:
    case NR.Run{n, +i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, +x}:
      (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, i && Bool.not(x))

def md.ok.k(p: NR.Run & Bool) -> Q.Md & Bool:
  (r, +ok) = p
  (Q.MB{r}, ok)

def md.ok(md: Q.Md) -> Q.Md & Bool:
  match md:
    case Q.MB{r}:
      md.ok.k(run.ok(r))
    case Q.MS{s, qs, ql, c}:
      (Q.MS{s, qs, ql, c}, False{})

def quiet.k(+o: B.Opts, m: Q.Md & Bool, s: List<&1, Q.Src> & Bool, p: Q.Pd & Bool, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Bool:
  (md, +b1) = m
  (src, +b2) = s
  (pend, +b3) = p
  (Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, b1 && b2 && b3 && Bool.not(eof) && Bool.not(fneed) && is_none(asked))

# Q is in the body, on bytes, not stopped, with no input left and no read
# asked: a batch can start.
def quiet(q: Q.St) -> Q.St & Bool:
  match q:
    case Q.St{+o, md, src, pend, +eof, +back, win, +asked, +fneed, dfs}:
      quiet.k(o, md.ok(md), is_nil.src(src), is_pb(pend), eof, back, win, asked, fneed, dfs)

def opts(q: Q.St) -> Q.St & B.Opts:
  match q:
    case Q.St{+o, md, src, pend, eof, back, win, asked, fneed, dfs}:
      (Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, o)

def rev_b(xs: List<&1, D.Bytes>, acc: List<&1, D.Bytes>) -> List<&1, D.Bytes>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_b(t, x <> acc)

# ---------------------------------------------------------------------------
# Plan: each piece's first and last complete lines, and its reads
# ---------------------------------------------------------------------------

def rlf.byte(r: D.Bytes & U32, +i: U32) -> Rl:
  (b, +x) = r
  Rl{b, i, Bool.not(U32.is_eq(x, 10)), U32.is_eq(x, 10)}

def rlf.step.if(done: Bool, b: D.Bytes, +i: U32) -> Rl:
  match done:
    case True{}:
      Rl{b, i, False{}, False{}}
    case False{}:
      rlf.byte(BY.at(b, (i - 1 : U32)), (i - 1 : U32))

def rlf.step(b: D.Bytes, +i: U32, +lo: U32) -> Rl:
  rlf.step.if(U32.is_le(i, lo), b, i)

def rlf.go(fuel: Nat, r: Rl, +lo: U32) -> D.Bytes & (U32 & Bool):
  match fuel r:
    case 0n Rl{b, i, m, h}:
      (b, (0, False{}))
    case 1n+f Rl{b, +i, False{}, +h}:
      (b, (i, h))
    case 1n+f Rl{b, +i, True{}, h}:
      rlf.go(f, rlf.step(b, i, lo), lo)

# The largest i with lo <= i < j where byte i is an LF, if any.
def rlf(b: D.Bytes, +j: U32, +lo: U32) -> D.Bytes & (U32 & Bool):
  rlf.go(Nat.add(U32.to_nat((j - lo : U32)), 2n), rlf.step(b, j, lo), lo)

def num.byte(r: D.Bytes & U32, +j: U32, +acc: U32) -> Nm:
  (b, +x) = r
  +dig = U32.is_le(48, x) && U32.is_le(x, 57)
  Nm{b, (j + 1 : U32), Bool.pick(U32, dig, ((acc * 10 : U32) + (x - 48 : U32) : U32), acc), dig}

def num.step.if(more: Bool, b: D.Bytes, +j: U32, +acc: U32) -> Nm:
  match more:
    case True{}:
      num.byte(BY.at(b, j), j, acc)
    case False{}:
      Nm{b, j, acc, False{}}

def num.step(b: D.Bytes, +j: U32, +e: U32, +acc: U32) -> Nm:
  num.step.if(U32.is_lt(j, e), b, j, acc)

def num.go(fuel: Nat, r: Nm, +e: U32) -> D.Bytes & U32:
  match fuel r:
    case 0n Nm{b, j, +acc, m}:
      (b, acc)
    case 1n+f Nm{b, j, +acc, False{}}:
      (b, acc)
    case 1n+f Nm{b, +j, +acc, True{}}:
      num.go(f, num.step(b, j, e, acc), e)

# The digits from j up to e (a POS), as a number (0 if none; a planning
# guess only: any value is correct, see merge.ok).
def num(b: D.Bytes, +j: U32, +e: U32) -> D.Bytes & U32:
  num.go(10n, num.step(b, j, e, 0), e)

def cp.num(+c: String, r: D.Bytes & U32) -> Cp:
  (b, +p) = r
  Cp{b, True{}, c, U32.to_nat(p)}

def cp.text(+t: U32, +e: U32, r: D.Bytes & String) -> Cp:
  (b, +c) = r
  cp.num(c, num(b, (t + 1 : U32), e))

def cp.tab.if(found: Bool, +s: U32, +t: U32, +e: U32, b: D.Bytes) -> Cp:
  match found:
    case True{}:
      cp.text(t, e, Q.text(b, s, (t - s : U32)))
    case False{}:
      Cp{b, False{}, "", 0n}

def cp.tab(+s: U32, +e: U32, r: D.Bytes & U32) -> Cp:
  (b, +t) = r
  cp.tab.if(U32.is_lt(t, e), s, t, e, b)

# The CHROM (the bytes before the first tab) and POS of the line s .. e-1
# (e: its LF); not ok without a tab.
def cp(b: D.Bytes, +s: U32, +e: U32) -> Cp:
  cp.tab(s, e, F.find(b, s, e, 9))

# The reads for a piece whose first complete line is at c1:p1 and last at
# c2:p2 (POS 1-based): one window from margin() letters before the smaller
# POS to margin() past the larger, when both are on one CHROM and it is at
# most ahead() + margin() letters (and an empty one); else two (plan.two),
# each empty if it is more than 2^31 letters. A piece with a complete line
# after its first LF has these two reads; any other piece none.
def plan.win.if(one: Bool, +c: String, +a: Nat, +e: Nat) -> P.Req:
  match one:
    case True{}:
      P.Req{c, a, e}
    case False{}:
      P.Req{c, e, e}

# The read of letters a .. e of contig c if it is at most 2^31 letters, else
# an empty one.
def plan.win(+c: String, +a: Nat, +e: Nat) -> P.Req:
  plan.win.if(Q.le31(Nat.sub(e, a)), c, a, e)

# Two windows: a window ahead() letters on from the first line and one
# ahead() letters back from the last, each in a 4 MiB block (notes/memory.md);
# but when the lines are on one CHROM more than 2 ahead() letters apart (so
# those two leave a gap: a sparse piece, or one with short lines) and the
# span a .. e is at most 4 ahead() letters, its two halves, each with
# margin() letters more where they meet (at most 2 ahead() + margin() + 1
# letters, an 8 MiB block).
def plan.two(halves: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat, +a: Nat, +e: Nat) -> List<&2, P.Req>:
  match halves:
    case True{}:
      +m = Nat.add(a, Nat.div(Nat.sub(e, a), 2n))
      [plan.win(c1, a, Nat.add(m, Q.margin())), plan.win(c1, Nat.sub(m, Q.margin()), e)]
    case False{}:
      [plan.win(c1, Nat.sub(Nat.sub(p1, 1n), Q.margin()), Nat.add(p1, Q.ahead())),
       plan.win(c2, Nat.sub(Nat.sub(p2, 1n), Q.ahead()), Nat.add(p2, Q.margin()))]

def plan.reqs.if(one: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat, +a: Nat, +e: Nat) -> List<&2, P.Req>:
  match one:
    case True{}:
      [P.Req{c1, a, e}, P.Req{c1, e, e}]
    case False{}:
      plan.two(String.eq(c1, c2) && Bool.not(Nat.is_le(Nat.sub(Nat.sub(p2, p1), Q.ahead()), Q.ahead())) && Nat.is_le(Nat.sub(Nat.sub(Nat.sub(Nat.sub(e, a), Q.ahead()), Q.ahead()), Q.ahead()), Q.ahead()), c1, p1, c2, p2, a, e)

def plan.reqs(+c1: String, +p1: Nat, +c2: String, +p2: Nat) -> List<&2, P.Req>:
  +a = Nat.sub(Nat.sub(Nat.min(p1, p2), 1n), Q.margin())
  +e = Nat.add(Nat.max(p1, p2), Q.margin())
  plan.reqs.if(String.eq(c1, c2) && Q.le31(Nat.sub(e, a)) && Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead()), c1, p1, c2, p2, a, e)

def plan.last.cp(+k: U32, +c1: String, +p1: Nat, +l: Nat, c: Cp) -> Pl:
  match c:
    case Cp{b, True{}, +c2, +p2}:
      Pl{b, plan.reqs(c1, p1, c2, p2), True{}, k, c1, l}
    case Cp{b, False{}, c2, p2}:
      Pl{b, plan.reqs(c1, p1, c1, p1), True{}, k, c1, l}

def plan.last.at2(+k: U32, +c1: String, +p1: Nat, +l: Nat, +el: U32, +s1: U32, b: D.Bytes, q: U32 & Bool) -> Pl:
  (+e0, f0) = q
  plan.last.cp(k, c1, p1, l, cp(b, Bool.pick(U32, f0, (e0 + 1 : U32), s1), el))

def plan.last.at(+k: U32, +c1: String, +p1: Nat, +l: Nat, +el: U32, +s1: U32, r: D.Bytes & (U32 & Bool)) -> Pl:
  (b, q) = r
  plan.last.at2(k, c1, p1, l, el, s1, b, q)

def plan.last.k2(+k: U32, +c1: String, +p1: Nat, +l: Nat, +s1: U32, b: D.Bytes, q: U32 & Bool) -> Pl:
  (+el, len) = q
  plan.last.at(k, c1, p1, l, el, s1, rlf(b, el, s1))

def plan.last.k(+k: U32, +c1: String, +p1: Nat, +l: Nat, +s1: U32, r: D.Bytes & (U32 & Bool)) -> Pl:
  (b, q) = r
  plan.last.k2(k, c1, p1, l, s1, b, q)

# The phantom key is the first line's POS plus the piece's length: above any
# key the task can write first (an item's key is at most its line's POS plus
# its REF's length), so the task's first run stops at its first write and
# runs again from that key, the highest phantom (merge.ok asks S's keys to be
# at most the phantom). The first run reads only the lines up to that write.
def plan.first(+len: U32, +k: U32, +s1: U32, c: Cp) -> Pl:
  match c:
    case Cp{b, True{}, +c1, +p1}:
      plan.last.k(k, c1, p1, Nat.add(p1, U32.to_nat(len)), s1, rlf(b, len, s1))
    case Cp{b, False{}, c1, p1}:
      Pl{b, Nil{}, False{}, k, "", 0n}

def plan.e1.if(line: Bool, +len: U32, +k: U32, +e1: U32, b: D.Bytes) -> Pl:
  match line:
    case True{}:
      plan.first(len, k, (k + 1 : U32), cp(b, (k + 1 : U32), e1))
    case False{}:
      Pl{b, Nil{}, False{}, k, "", 0n}

def plan.e1(+len: U32, +k: U32, r: D.Bytes & U32) -> Pl:
  (b, +e1) = r
  plan.e1.if(U32.is_lt(e1, len), len, k, e1, b)

def plan.k.if(more: Bool, +len: U32, +k: U32, b: D.Bytes) -> Pl:
  match more:
    case True{}:
      plan.e1(len, k, F.find(b, (k + 1 : U32), len, 10))
    case False{}:
      Pl{b, Nil{}, False{}, k, "", 0n}

def plan.k(+len: U32, r: D.Bytes & U32) -> Pl:
  (b, +k) = r
  plan.k.if(U32.is_le(minp(), len) && U32.is_lt(k, len) && U32.is_lt((k + 1 : U32), len), len, k, b)

def plan.len(r: D.Bytes & U32) -> Pl:
  (b, +len) = r
  plan.k(len, F.find(b, 0, len, 10))

# A piece: its first LF k; the first complete line after it (k+1 up to its
# LF) and the last one.
def plan.piece(b: D.Bytes) -> Pl:
  plan.len(BY.len(b))

def plan.all(ps: List<&1, D.Bytes>) -> List<&1, Pl>:
  match ps:
    case Nil{}:
      Nil{}
    case b <> t:
      plan.piece(b) <> plan.all(t)

def plan.reqs_cons(p: Pl, +rs: List<&2, P.Req>, r: List<&1, Pl> & List<&2, P.Req>) -> List<&1, Pl> & List<&2, P.Req>:
  (t, +rt) = r
  (p <> t, List.append(&2, P.Req, rs, rt))

def plan.reqs_all(pls: List<&1, Pl>) -> List<&1, Pl> & List<&2, P.Req>:
  match pls:
    case Nil{}:
      (Nil{}, Nil{})
    case Pl{b, +rs, ok, +k, +c0, +l} <> t:
      plan.reqs_cons(Pl{b, rs, ok, k, c0, l}, rs, plan.reqs_all(t))

# ---------------------------------------------------------------------------
# Run: one task per piece
# ---------------------------------------------------------------------------

def swap_win(st: Q.St, w: Q.Win) -> Q.St:
  match st:
    case Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}:
      Q.St{o, md, src, pend, eof, back, w, None{}, fneed, dfs}

def task.done(st: Q.St, +k: U32, +c0: String, +l: Nat) -> TRes:
  match st:
    case Q.St{o, Q.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}:
      TClean{Tc{run, pend, win, k, c0, l}}
    case Q.St{o, Q.MS{s, qs, ql, c}, src, pend, eof, back, win, asked, fneed, dfs}:
      TDirty{}

# The buffer of Q's input (the piece, while the task has not taken it back).
def src_b(src: List<&1, Q.Src>) -> D.Bytes:
  match src:
    case Nil{}:
      BY.empty(0n)
    case Q.SB{b, at} <> t:
      b
    case Q.SL{p} <> t:
      BY.empty(0n)
    case Q.SP{r, at} <> t:
      src_b(t)
    case Q.SR{l} <> t:
      src_b(t)

def st_b(st: Q.St) -> D.Bytes:
  match st:
    case Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}:
      src_b(src)

# The piece: held by the task, or Q's input.
def task.back(st: Q.St, ph: Ph) -> D.Bytes:
  match ph:
    case PHeld{b}:
      b
    case PIn{}:
      st_b(st)

def task.dirty(st: Q.St, ph: Ph) -> Tk:
  TEnd{TOut{task.back(st, ph), TDirty{}}}

# Q's input made a copy of the piece's bytes from at (its last partial line),
# the piece held by the task.
def swap.put(+o: B.Opts, md: Q.Md, p: D.Bytes & D.Bytes, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  (tail, b) = p
  (Q.St{o, md, [Q.SB{tail, 0}], pend, eof, back, win, asked, fneed, dfs}, PHeld{b})

def swap.len(+o: B.Opts, md: Q.Md, r: D.Bytes & U32, +at: U32, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  (b, +len) = r
  swap.put(o, md, NR.put_bytes(BY.empty(NR.depth((len - at + 8 : U32))), b, at, (len - at : U32)), pend, eof, back, win, asked, fneed, dfs)

def swap.if(go: Bool, +o: B.Opts, md: Q.Md, b: D.Bytes, +at: U32, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  match go:
    case True{}:
      swap.len(o, md, BY.len(b), at, pend, eof, back, win, asked, fneed, dfs)
    case False{}:
      (Q.St{o, md, [Q.SB{b, at}], pend, eof, back, win, asked, fneed, dfs}, PIn{})

# The piece stays Q's input while its byte el is an LF at or after at.
def swap.at(r: D.Bytes & U32, +at: U32, +el: U32, +o: B.Opts, md: Q.Md, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  (b, +x) = r
  swap.if(Bool.not(U32.is_le(at, el) && U32.is_eq(x, 10)), o, md, b, at, pend, eof, back, win, asked, fneed, dfs)

def swap.lt(lt: Bool, b: D.Bytes, +at: U32, +el: U32, +o: B.Opts, md: Q.Md, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  match lt:
    case True{}:
      swap.at(BY.at(b, el), at, el, o, md, pend, eof, back, win, asked, fneed, dfs)
    case False{}:
      swap.if(True{}, o, md, b, at, pend, eof, back, win, asked, fneed, dfs)

def swap.src(src: List<&1, Q.Src>, +el: U32, +len: U32, +o: B.Opts, md: Q.Md, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  match src:
    case Nil{}:
      (Q.St{o, md, Nil{}, pend, eof, back, win, asked, fneed, dfs}, PIn{})
    case Q.SB{b, +at} <> t:
      match t:
        case Nil{}:
          swap.lt(U32.is_lt(el, len), b, at, el, o, md, pend, eof, back, win, asked, fneed, dfs)
        case h <> t2:
          (Q.St{o, md, Q.SB{b, at} <> (h <> t2), pend, eof, back, win, asked, fneed, dfs}, PIn{})
    case Q.SL{p} <> t:
      (Q.St{o, md, Q.SL{p} <> t, pend, eof, back, win, asked, fneed, dfs}, PIn{})
    case Q.SP{r, at} <> t:
      (Q.St{o, md, Q.SP{r, at} <> t, pend, eof, back, win, asked, fneed, dfs}, PIn{})
    case Q.SR{l} <> t:
      (Q.St{o, md, Q.SR{l} <> t, pend, eof, back, win, asked, fneed, dfs}, PIn{})

# Before Q reaches the piece's last partial line (no LF from at), where it
# would drop its input, its input becomes a copy of that line and the task
# holds the piece. el is where the piece's last LF should be (len: the
# piece's length): while its byte is an LF at or after at, Q keeps the piece.
def swap.ph(ph: Ph, +el: U32, +len: U32, +o: B.Opts, md: Q.Md, src: List<&1, Q.Src>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Ph:
  match ph:
    case PHeld{b}:
      (Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, PHeld{b})
    case PIn{}:
      swap.src(src, el, len, o, md, pend, eof, back, win, asked, fneed, dfs)

def swap(st: Q.St, ph: Ph, +el: U32, +len: U32) -> Q.St & Ph:
  match st:
    case Q.St{+o, md, src, pend, +eof, +back, win, +asked, +fneed, dfs}:
      swap.ph(ph, el, len, o, md, src, pend, eof, back, win, asked, fneed, dfs)

def task.tgo(p: Q.St & Ph, spare: List<&1, Q.Win>) -> Tk:
  (st, ph) = p
  TGo{st, spare, ph}

# The loop goes on from st, after the swap test; Q in the String mode makes
# the task dirty (Q's input is then no longer kept for the piece).
def task.next(st: Q.St, ph: Ph, spare: List<&1, Q.Win>, +el: U32, +len: U32) -> Tk:
  match st:
    case Q.St{o, Q.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}:
      task.tgo(swap(Q.St{o, Q.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, ph, el, len), spare)
    case Q.St{o, Q.MS{s, qs, ql, c}, src, pend, eof, back, win, asked, fneed, dfs}:
      task.dirty(Q.St{o, Q.MS{s, qs, ql, c}, src, pend, eof, back, win, asked, fneed, dfs}, ph)

def task.idle(st: Q.St, ph: Ph, +k: U32, +c0: String, +l: Nat) -> Tk:
  match ph:
    case PHeld{b}:
      TEnd{TOut{b, task.done(st, k, c0, l)}}
    case PIn{}:
      task.dirty(st, PIn{})

# Whether the run stopped as UNSORTED against the phantom (the line before
# the item out of order is line 0).
def again.ph(ns: List<&2, B.Note>) -> Bool:
  match ns:
    case B.Stop{B.Unsorted{}, Some{a}, Some{B.At{+ln, c, p}}} <> t:
      Nat.is_eq(ln, 0n)
    case _:
      False{}

def again.key(+ok: Bool, c: Cp) -> D.Bytes & Maybe<&2, Nat>:
  match c:
    case Cp{b, +f, c1, +p}:
      (b, Bool.pick(Maybe<&2, Nat>, ok && f, Some{p}, None{}))

def again.len(+ok: Bool, +ow: U32, r: D.Bytes & U32) -> D.Bytes & Maybe<&2, Nat>:
  (b, +n) = r
  again.key(ok, cp(b, ow, n))

def again.run.k(p: D.Bytes & Maybe<&2, Nat>, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, cb: D.Bytes, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +ow: U32, +ns: List<&2, B.Note>, +x: Bool) -> NR.Run & Maybe<&2, Nat>:
  (ob, +m) = p
  (NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, m)

# The key of the item a stop against the phantom refused: the POS of its
# text, the first after the bytes written (any value is correct: it only
# chooses the phantom of the task's second run).
def again.run(r: NR.Run) -> NR.Run & Maybe<&2, Nat>:
  match r:
    case NR.Run{+n, +i, +h, +c, cb, +e, +l, +f, +b, +bn, +tl, +k, ob, +ow, +ns, +x}:
      again.run.k(again.len(again.ph(ns), ow, BY.len(ob)), n, i, h, c, cb, e, l, f, b, bn, tl, k, ow, ns, x)

# The task stopped against the phantom l at an item of key l2 below it: it
# hands back its piece and its windows, to run again from l2.
def task.again.if(go: Bool, +l2: Nat, +o: B.Opts, run: NR.Run, src: List<&1, Q.Src>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs, spare: List<&1, Q.Win>, ph: Ph) -> Tk:
  match go:
    case True{}:
      TEnd{TOut{task.back(Q.St{o, Q.MB{run}, src, pend, eof, back, Q.WNone{}, asked, fneed, dfs}, ph), TAgain{l2, win, spare}}}
    case False{}:
      task.dirty(Q.St{o, Q.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, ph)

def task.again(p: NR.Run & Maybe<&2, Nat>, +l: Nat, +o: B.Opts, src: List<&1, Q.Src>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs, spare: List<&1, Q.Win>, ph: Ph) -> Tk:
  (run, m) = p
  match m:
    case Some{+l2}:
      task.again.if(Nat.is_lt(l2, l), l2, o, run, src, pend, eof, back, win, asked, fneed, dfs, spare, ph)
    case None{}:
      task.dirty(Q.St{o, Q.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, ph)

# The task's run stopped: dirty, unless it stopped against the phantom.
def task.ended(st: Q.St, spare: List<&1, Q.Win>, ph: Ph, +l: Nat) -> Tk:
  match st:
    case Q.St{+o, Q.MB{run}, src, pend, +eof, +back, win, +asked, +fneed, +dfs}:
      task.again(again.run(run), l, o, src, pend, eof, back, win, asked, fneed, dfs, spare, ph)
    case Q.St{o, Q.MS{s, qs, ql, c}, src, pend, eof, back, win, asked, fneed, dfs}:
      task.dirty(Q.St{o, Q.MS{s, qs, ql, c}, src, pend, eof, back, win, asked, fneed, dfs}, ph)

def task.want(st: Q.St, spare: List<&1, Q.Win>, ph: Ph, +el: U32, +len: U32) -> Tk:
  match spare:
    case Nil{}:
      task.dirty(st, ph)
    case w <> ws:
      task.next(swap_win(st, w), ph, ws, el, len)

def task.adv(a: Q.Adv, spare: List<&1, Q.Win>, ph: Ph, +el: U32, +len: U32, +k: U32, +c0: String, +l: Nat) -> Tk:
  match a:
    case Q.Went{st}:
      task.next(st, ph, spare, el, len)
    case Q.Want{st, r}:
      task.want(st, spare, ph, el, len)
    case Q.Idle{st}:
      task.idle(st, ph, k, c0, l)
    case Q.Ended{st}:
      task.ended(st, spare, ph, l)
    case Q.Yield{st}:
      task.dirty(st, ph)

# Q's pump on the task's lines: a read its window does not answer tries the
# next window, then makes the task dirty. The piece comes back with the
# result.
def task.loop(fuel: Nat, t: Tk, +el: U32, +len: U32, +k: U32, +c0: String, +l: Nat) -> TOut:
  match fuel t:
    case 0n TGo{st, sp, ph}:
      TOut{task.back(st, ph), TDirty{}}
    case 1n+f TGo{st, sp, ph}:
      task.loop(f, task.adv(Q.advance(st), sp, ph, el, len, k, c0, l), el, len, k, c0, l)
    case _ TEnd{r}:
      r

def task.wins(ws: List<&1, Q.Win>) -> Q.Win & List<&1, Q.Win>:
  match ws:
    case Nil{}:
      (Q.WNone{}, Nil{})
    case w <> t:
      (w, t)

# The task's run: in the body, the current CHROM c0, the phantom as the last
# item written (key and input POS l, line 0, length 0), room for len bytes of
# output (task.res).
def task.run0(+c0: String, +l: Nat, +len: U32) -> NR.Run:
  NR.reserve(NR.Run{0n, True{}, "", Some{c0}, NR.of_str(c0), Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, R.Cnt{0n, 0n, 0n, 0n}, BY.empty(0n), 0, Nil{}, False{}}, len)

# Room for a task's output: its piece's length, twice that with -m (a split
# line's records hold more bytes than the line; notes/split.md, memory).
def task.res(+o: B.Opts, +len: U32) -> U32:
  Bool.pick(U32, R.Opts.split(o), (len + len : U32), len)

# One run of the task's loop on its piece, from the phantom l, with room for
# res bytes of output.
def task.run1(+o: B.Opts, b: D.Bytes, +len: U32, +k: U32, w: Q.Win, spare: List<&1, Q.Win>, +el: U32, +c0: String, +l: Nat, +res: U32, +dfs: B.Defs) -> TOut:
  task.loop(Nat.add(U32.to_nat(len), 8n), task.next(Q.St{o, Q.MB{task.run0(c0, l, res)}, [Q.SB{b, (k + 1 : U32)}], Q.PB{BY.empty(0n)}, False{}, 0n, w, None{}, False{}, dfs}, PIn{}, spare, el, len), el, len, k, c0, l)

# The second run's result: a second stop against the phantom is dirty.
def task.final(r: TOut) -> TOut:
  match r:
    case TOut{b, TAgain{l2, w, ws}}:
      TOut{b, TDirty{}}
    case TOut{b, TDirty{}}:
      TOut{b, TDirty{}}
    case TOut{b, TClean{c}}:
      TOut{b, TClean{c}}

# The first run's result: when it stopped against the phantom (at its first
# write, plan.first), the task runs once more from the key it stopped at,
# with room for its output (task.res); the merge checks that key against the
# true run's.
def task.retry(+o: B.Opts, +len: U32, +k: U32, +el: U32, +c0: String, +dfs: B.Defs, r: TOut) -> TOut:
  match r:
    case TOut{b, TAgain{+l2, w, ws}}:
      task.final(task.run1(o, b, len, k, w, ws, el, c0, l2, task.res(o, len), dfs))
    case TOut{b, TDirty{}}:
      TOut{b, TDirty{}}
    case TOut{b, TClean{c}}:
      TOut{b, TClean{c}}

# The first run stops at its first write (plan.first): it gets a small
# output buffer (it grows if the run goes on).
def task.start(+o: B.Opts, b: D.Bytes, +len: U32, +k: U32, p: Q.Win & List<&1, Q.Win>, +el: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> TOut:
  (w, spare) = p
  task.retry(o, len, k, el, c0, dfs, task.run1(o, b, len, k, w, spare, el, c0, l, 65536, dfs))

def task.last.k(+o: B.Opts, +len: U32, ws: List<&1, Q.Win>, +k: U32, +c0: String, +l: Nat, b: D.Bytes, q: U32 & Bool, +dfs: B.Defs) -> TOut:
  (+el, fl) = q
  task.start(o, b, len, k, task.wins(ws), el, c0, l, dfs)

def task.last(+o: B.Opts, +len: U32, ws: List<&1, Q.Win>, +k: U32, +c0: String, +l: Nat, r: D.Bytes & (U32 & Bool), +dfs: B.Defs) -> TOut:
  (b, q) = r
  task.last.k(o, len, ws, k, c0, l, b, q, dfs)

def task.len.if(small: Bool, +o: B.Opts, b: D.Bytes, +len: U32, ws: List<&1, Q.Win>, +k: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> TOut:
  match small:
    case True{}:
      task.last(o, len, ws, k, c0, l, rlf(b, len, (k + 1 : U32)), dfs)
    case False{}:
      TOut{b, TDirty{}}

# The piece is run, if it has less than 2^30 bytes (the driver's have
# 3.5 MB); a larger one is left to Q. The task runs on the piece itself and
# hands it back (for the combine), with no copy: its last LF el tells
# when to take it back from Q.
def task.len(+o: B.Opts, r: D.Bytes & U32, ws: List<&1, Q.Win>, +k: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> TOut:
  (b, +len) = r
  task.len.if(U32.is_lt(len, 1073741824), o, b, len, ws, k, c0, l, dfs)

def task.win.if(short: Bool, +r: P.Req, a: P.Ans) -> Q.Win:
  match short:
    case True{}:
      Q.win_of([r], [a])
    case False{}:
      Q.WNone{}

# The window of one read and its answer (none for a contig name of more than
# 2^28 bytes, which no byte-mode line has).
def task.win(+r: P.Req, a: P.Ans) -> Q.Win:
  match r:
    case P.Req{+c, x, y}:
      task.win.if(Q.len_le(c, 268435456), r, a)

# The windows of a piece's reads (the answers a1 and a2).
def task.wins2(rs: List<&2, P.Req>, a1: P.Ans, a2: P.Ans) -> List<&1, Q.Win>:
  match rs:
    case Nil{}:
      Nil{}
    case +r1 <> t:
      match t:
        case Nil{}:
          [task.win(r1, a1)]
        case +r2 <> t2:
          [task.win(r1, a1), task.win(r2, a2)]

def task.go(run: Bool, +o: B.Opts, b: D.Bytes, rs: List<&2, P.Req>, a1: P.Ans, a2: P.Ans, +k: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> TOut:
  match run:
    case True{}:
      task.len(o, BY.len(b), task.wins2(rs, a1, a2), k, c0, l, dfs)
    case False{}:
      TOut{b, TDirty{}}

# A piece's task: the task runs on the piece and hands it back (for the
# combine); a piece with no complete line after its first LF, or whose first
# CHROM has more than 2^28 bytes (no byte-mode line has), is left to Q.
def task(+o: B.Opts, b: D.Bytes, ok: Bool, rs: List<&2, P.Req>, a1: P.Ans, a2: P.Ans, +k: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> TOut:
  task.go(ok && Q.len_le(c0, 268435456), o, b, rs, a1, a2, k, c0, l, dfs)

def task.mk(+o: B.Opts, b: D.Bytes, ok: Bool, rs: List<&2, P.Req>, a1: P.Ans, a2: P.Ans, +k: U32, +c0: String, +l: Nat, +dfs: B.Defs) -> HD.Task<&1, TOut>:
  HD.Task{u => task(o, b, ok, rs, a1, a2, k, c0, l, dfs)}

# The answers, two at a time (each piece with reads has two).
def pairs(as: List<&1, P.Ans>) -> List<&1, P.Ans & P.Ans>:
  match as:
    case Nil{}:
      Nil{}
    case a1 <> t:
      match t:
        case Nil{}:
          Nil{}
        case a2 <> r:
          (a1, a2) <> pairs(r)

def task.of.k(+o: B.Opts, b: D.Bytes, ok: Bool, rs: List<&2, P.Req>, +k: U32, +c0: String, +l: Nat, x: P.Ans & P.Ans, +dfs: B.Defs) -> HD.Task<&1, TOut>:
  (a1, a2) = x
  task.mk(o, b, ok, rs, a1, a2, k, c0, l, dfs)

def task.of(+o: B.Opts, p: Pl, x: P.Ans & P.Ans, +dfs: B.Defs) -> HD.Task<&1, TOut>:
  match p:
    case Pl{b, rs, ok, +k, +c0, +l}:
      task.of.k(o, b, ok, rs, k, c0, l, x, dfs)

# One task per piece, with its answers (the next two, for a piece with reads).
def tasks(+o: B.Opts, pls: List<&1, Pl>, ps: List<&1, P.Ans & P.Ans>, +dfs: B.Defs) -> List<&1, HD.Task<&1, TOut>>:
  match pls ps:
    case Nil{} x:
      Nil{}
    case Pl{b, rs, True{}, +k, +c0, +l} <> t x <> pt:
      task.of(o, Pl{b, rs, True{}, k, c0, l}, x, dfs) <> tasks(o, t, pt, dfs)
    case Pl{b, rs, True{}, +k, +c0, +l} <> t Nil{}:
      task.of(o, Pl{b, rs, True{}, k, c0, l}, (P.Unknown{}, P.Unknown{}), dfs) <> tasks(o, t, Nil{}, dfs)
    case Pl{b, rs, False{}, +k, +c0, +l} <> t x:
      task.of(o, Pl{b, rs, False{}, k, c0, l}, (P.Unknown{}, P.Unknown{}), dfs) <> tasks(o, t, x, dfs)

# ---------------------------------------------------------------------------
# Merge: a clean task's run spliced after the true run
# ---------------------------------------------------------------------------

def ck_shift(+d: Nat, c: NR.Ck) -> NR.Ck:
  match c:
    case NR.Ck{k, ip, ln, p, n}:
      NR.Ck{k, ip, Nat.add(ln, d), p, n}

def cks_shift(+d: Nat, xs: List<&2, NR.Ck>) -> List<&2, NR.Ck>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      ck_shift(d, x) <> cks_shift(d, t)

def ck_inpos(c: NR.Ck) -> Nat:
  match c:
    case NR.Ck{k, ip, ln, p, n}:
      ip

# The phantom (line 0; every real item has the line number of its line,
# from 1).
def ck_phantom(c: NR.Ck) -> Bool:
  match c:
    case NR.Ck{k, ip, ln, p, n}:
      Nat.is_eq(ln, 0n)

# T's last is the phantom.
def last_ph(m: Maybe<&2, NR.Ck>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      ck_phantom(c)

def max_inpos(xs: List<&2, NR.Ck>, +m: Nat) -> Nat:
  match xs:
    case Nil{}:
      m
    case +x <> t:
      max_inpos(t, Nat.max(m, ck_inpos(x)))

def real_inpos.k(ph: Bool, +c: NR.Ck) -> Nat:
  match ph:
    case True{}:
      0n
    case False{}:
      ck_inpos(c)

# The input POS of T's last written item (0 for none or the phantom).
def real_inpos(m: Maybe<&2, NR.Ck>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{+c}:
      real_inpos.k(ck_phantom(c), c)

def at_shift(+d: Nat, m: Maybe<&2, B.At>) -> Maybe<&2, B.At>:
  match m:
    case None{}:
      None{}
    case Some{B.At{ln, c, p}}:
      Some{B.At{Nat.add(ln, d), c, p}}

# A message with its line number moved on by d (a task's, as the true run's).
def note_shift(+d: Nat, n: B.Note) -> B.Note:
  match n:
    case B.Warning{c, B.At{ln, ch, p}}:
      B.Warning{c, B.At{Nat.add(ln, d), ch, p}}
    case B.Stop{c, a, p}:
      B.Stop{c, at_shift(d, a), at_shift(d, p)}
    case B.Summary{a, b, c, e}:
      B.Summary{a, b, c, e}

def notes_shift(+d: Nat, xs: List<&2, B.Note>) -> List<&2, B.Note>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      note_shift(d, x) <> notes_shift(d, t)

def cnt_add(a: R.Cnt, b: R.Cnt) -> R.Cnt:
  match a b:
    case R.Cnt{a1, a2, a3, a4} R.Cnt{b1, b2, b3, b4}:
      R.Cnt{Nat.add(a1, b1), Nat.add(a2, b2), Nat.add(a3, b3), Nat.add(a4, b4)}

def last_ck(xs: List<&2, NR.Ck>) -> Maybe<&2, NR.Ck>:
  match xs:
    case Nil{}:
      None{}
    case +x <> t:
      Maybe.or(&2, NR.Ck, last_ck(t), Some{x})

def first_ck(xs: List<&2, NR.Ck>) -> Maybe<&2, NR.Ck>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      Some{x}

# A buffer front ++ reverse(back): its first item, and its last.
def buf_first(+f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>) -> Maybe<&2, NR.Ck>:
  Maybe.or(&2, NR.Ck, first_ck(f), last_ck(b))

def buf_last(+f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>) -> Maybe<&2, NR.Ck>:
  Maybe.or(&2, NR.Ck, first_ck(b), last_ck(f))

def key_or(m: Maybe<&2, NR.Ck>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{c}:
      NR.Ck.key(c)

# Every key is at least l.
def keys_ge(xs: List<&2, NR.Ck>, +l: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case c <> t:
      Nat.is_le(l, NR.Ck.key(c)) && keys_ge(t, l)

def sorted.go(xs: List<&2, NR.Ck>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +c <> t:
      Nat.is_le(k, NR.Ck.key(c)) && sorted.go(t, NR.Ck.key(c))

# The keys never go down.
def sorted(xs: List<&2, NR.Ck>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +c <> t:
      sorted.go(t, NR.Ck.key(c))

# T's CHROMs other than c0 are neither among the CHROMs the true run has
# ended nor its current one.
def chroms_ok(xs: List<&2, String>, +c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      (String.eq(x, c0) || (Bool.not(R.has(x, se)) && Bool.not(R.is_cur(sc, x)))) && chroms_ok(t, c0, se, sc)

def cur_list(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{c}:
      [c]

def last_of.k(ph: Bool, +c: NR.Ck, +same: Bool, +sl: Maybe<&2, NR.Ck>, +elast: Maybe<&2, NR.Ck>, +sn: Nat) -> Maybe<&2, NR.Ck>:
  match ph same:
    case False{} _:
      Some{ck_shift(sn, c)}
    case True{} True{}:
      Maybe.or(&2, NR.Ck, elast, sl)
    case True{} False{}:
      None{}

# T's last, as the true run's: the phantom (nothing written in T's first
# CHROM run) stands for what the true run wrote last before T's lines: the
# last of S's buffer (all of it written) or S's last, in the same CHROM run;
# nothing after a new CHROM run.
def last_of(+tl: Maybe<&2, NR.Ck>, +same: Bool, +sl: Maybe<&2, NR.Ck>, +elast: Maybe<&2, NR.Ck>, +sn: Nat) -> Maybe<&2, NR.Ck>:
  match tl:
    case None{}:
      None{}
    case Some{+c}:
      last_of.k(ck_phantom(c), c, same, sl, elast, sn)

# Whether the true run S, given T's lines, does what T did from its phantom
# state, with S's buffered items E all written first (notes/parallel.md,
# "merge"):
# - both in the body and not stopped; T read lines (its messages, warnings,
#   are the true run's, their line numbers moved on);
# - c0 has not ended in S; T's other CHROMs neither ended in S nor are S's;
#   T's last is the phantom only while T's CHROM is c0;
# - E is sorted and starts no lower than S's last;
# - if S's CHROM is c0 (else T's first line writes E and starts a new run):
#   E's keys and S's last are at most l; and unless T left c0 (which writes
#   E), every key in T's buffer is l or above and a line of T had an input POS
#   at least max(E) + w (so E was written).
def merge.ok(+l: Nat, +w: Nat, +c0: String, +sc: Maybe<&2, String>, +se: List<&2, String>, +sl: Maybe<&2, NR.Ck>, +sf: List<&2, NR.Ck>, +sb: List<&2, NR.Ck>, +sbn: Nat, +stl: Nat, +si: Bool, +sx: Bool, +tn: Nat, +tc: Maybe<&2, String>, +te: List<&2, String>, +tl: Maybe<&2, NR.Ck>, +tf: List<&2, NR.Ck>, +tb: List<&2, NR.Ck>, +ti: Bool, +tx: Bool) -> Bool:
  +same = R.is_cur(sc, c0)
  +eempty = Nat.is_eq(sbn, 0n)
  +maxe = Nat.max(Bool.pick(Nat, eempty, 0n, stl), key_or(sl, 0n))
  +changed = Bool.not(List.is_empty(&2, String, te))
  +mlow = max_inpos(tf, max_inpos(tb, Bool.pick(Nat, changed, 0n, real_inpos(tl))))
  si && ti && Bool.not(sx) && Bool.not(tx) && Nat.is_lt(0n, tn) && Bool.not(R.has(c0, se)) && (Bool.not(last_ph(tl)) || R.is_cur(tc, c0)) && chroms_ok(List.append(&2, String, cur_list(tc), te), c0, se, sc) && sorted(NR.append_ck(sf, NR.rev_ck(sb, Nil{}))) && (eempty || NR.last_le(sl, key_or(buf_first(sf, sb), 0n))) && (Bool.not(same) || (Nat.is_le(maxe, l) && (changed || (keys_ge(tf, l) && keys_ge(tb, l))) && (changed || eempty || Nat.is_le(Nat.add(maxe, w), mlow))))

# The run after S and T: S's output (its written bytes, then E) and messages
# handed out now; T's state, its line numbers (and its messages') shifted by
# S's, the counts added, ended T's then S's (S's current pushed when T's
# first line started a new run).
def merge.if(ok: Bool, s: NR.Run, t: NR.Run, +same: Bool) -> Mg:
  match ok s t:
    case True{} NR.Run{+sn, si, +sh, +sc, scb, +se, +sl, +sf, +sb, sbn, stl, +sk, sob, sow, +sns, sx} NR.Run{+tn, ti, th, +tc, tcb, +te, +tl, +tf, +tb, +tbn, +ttl, +tk, tob, +tow, +tns, tx}:
      MOk{sob, List.reverse(&2, B.Note, sns), NR.Run{Nat.add(sn, tn), True{}, sh, tc, tcb, List.append(&2, String, te, Bool.pick(List<&2, String>, same, se, NR.push_cur(sc, se))), last_of(tl, same, sl, buf_last(sf, sb), sn), cks_shift(sn, tf), cks_shift(sn, tb), tbn, ttl, cnt_add(sk, tk), tob, tow, notes_shift(sn, tns), False{}}}
    case False{} r t2:
      MNo{r}

def merge(s: NR.Run, t: NR.Run, +l: Nat, +w: Nat, +c0: String) -> Mg:
  match s t:
    case NR.Run{sn, +si, sh, +sc, scb, +se, +sl, +sf, +sb, +sbn, +stl, sk, sob, sow, sns, +sx} NR.Run{+tn, +ti, th, +tc, tcb, +te, +tl, +tf, +tb, tbn, ttl, tk, tob, tow, tns, +tx}:
      merge.if(merge.ok(l, w, c0, sc, se, sl, sf, sb, sbn, stl, si, sx, tn, tc, te, tl, tf, tb, ti, tx), NR.Run{sn, si, sh, sc, scb, se, sl, sf, sb, sbn, stl, sk, sob, sow, sns, sx}, NR.Run{tn, ti, th, tc, tcb, te, tl, tf, tb, tbn, ttl, tk, tob, tow, tns, tx}, R.is_cur(sc, c0))

# ---------------------------------------------------------------------------
# Combine, in order
# ---------------------------------------------------------------------------

def list_nil(xs: List<&1, TOut>) -> List<&1, TOut> & Bool:
  match xs:
    case Nil{}:
      (Nil{}, True{})
    case h <> t:
      (h <> t, False{})

def seq.more(p: List<&1, TOut> & Bool, +eofp: Bool, st: Q.St, o: D.Bytes, +ns: List<&2, B.Note>) -> Step:
  (rest, +none) = p
  match none eofp:
    case True{} False{}:
      Step{St{st, BNone{}}, o, ns, P.More{}}
    case _ _:
      Step{St{st, BComb{rest, eofp, False{}}}, o, ns, P.Ask{Nil{}}}

def seq.k(nx: P.Next, st: Q.St, o: D.Bytes, +ns: List<&2, B.Note>, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  match nx:
    case P.More{}:
      seq.more(list_nil(rest), eofp, st, o, ns)
    case P.Ask{+r}:
      Step{St{st, BComb{rest, eofp, True{}}}, o, ns, P.Ask{r}}
    case P.Finish{+c}:
      Step{St{st, BNone{}}, o, ns, P.Finish{c}}

# A step of Q while combining: when Q wants more input, the batch goes on
# with its next piece (in the next step).
def seq_out(s: Q.Step, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  match s:
    case Q.Step{st, o, +ns, +nx}:
      seq.k(nx, st, o, ns, rest, eofp)

def comb.mg(m: Mg, +o: B.Opts, tp: Q.Pd, tw: Q.Win, src: List<&1, Q.Src>, pend: Q.Pd, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, rest: List<&1, TOut>, +eofp: Bool, +dfs: B.Defs) -> Step:
  match m:
    case MOk{out, +ns, run}:
      Step{St{Q.St{o, Q.MB{run}, Nil{}, tp, False{}, 0n, tw, None{}, False{}, dfs}, BComb{rest, eofp, False{}}}, out, ns, P.Ask{Nil{}}}
    case MNo{run}:
      seq_out(Q.go(Q.St{o, Q.MB{run}, src, pend, False{}, back, win, asked, fneed, dfs}), rest, eofp)

def comb.splice(q2: Q.St, c: Tc, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  match q2 c:
    case Q.St{+o, Q.MB{s}, src, pend, eof, +back, win, +asked, +fneed, dfs} Tc{t, tp, tw, k, +c0, +l}:
      comb.mg(merge(s, t, l, R.Opts.w(o), c0), o, tp, tw, src, pend, back, win, asked, fneed, rest, eofp, dfs)
    case Q.St{o, Q.MS{s, qs, ql, cd}, src, pend, eof, back, win, asked, fneed, dfs} _:
      seq_out(Q.go(Q.St{o, Q.MS{s, qs, ql, cd}, src, pend, eof, back, win, asked, fneed, dfs}), rest, eofp)

# The input left: one buffer (and where in it), or more.
def one_src(src: List<&1, Q.Src>) -> List<&1, Q.Src> & (U32 & Bool):
  match src:
    case Nil{}:
      (Nil{}, (0, False{}))
    case Q.SB{b, +at} <> Nil{}:
      ([Q.SB{b, at}], (at, True{}))
    case Q.SB{b, at} <> (h <> t):
      (Q.SB{b, at} <> (h <> t), (0, False{}))
    case Q.SL{p} <> t:
      (Q.SL{p} <> t, (0, False{}))
    case Q.SP{r, at} <> t:
      (Q.SP{r, at} <> t, (0, False{}))
    case Q.SR{l} <> t:
      (Q.SR{l} <> t, (0, False{}))

def tc.k(c: Tc) -> Tc & U32:
  match c:
    case Tc{t, tp, tw, +k, c0, l}:
      (Tc{t, tp, tw, k, c0, l}, k)

def edge.where.if(here: Bool, +ok: Bool, q: Q.St, c: Tc) -> Ew:
  match here:
    case True{}:
      EHere{q, c, ok}
    case False{}:
      EMore{q, c}

def md.n.k(p: NR.Run & Nat) -> Q.Md & Nat:
  (r, +n) = p
  (Q.MB{r}, n)

# The byte run's line count (0 in the String mode).
def md.n(md: Q.Md) -> Q.Md & Nat:
  match md:
    case Q.MB{r}:
      md.n.k(NR.Run.n(r))
    case Q.MS{s, qs, ql, c}:
      (Q.MS{s, qs, ql, c}, 0n)

def q.n.k(+o: B.Opts, m: Q.Md & Nat, src: List<&1, Q.Src>, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, +dfs: B.Defs) -> Q.St & Nat:
  (md, +n) = m
  (Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, n)

def q.n(q: Q.St) -> Q.St & Nat:
  match q:
    case Q.St{+o, md, src, pend, +eof, +back, win, +asked, +fneed, dfs}:
      q.n.k(o, md.n(md), src, pend, eof, back, win, asked, fneed, dfs)

def edge.where.q(+o: B.Opts, m: Q.Md & Nat, src: List<&1, Q.Src>, q: U32 & Bool, pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, c: Tc, +k: U32, +n0: Nat, +dfs: B.Defs) -> Ew:
  (md, +n) = m
  (+at, one) = q
  edge.where.if(one && U32.is_eq(at, (k + 1 : U32)) && Nat.is_eq(n, 1n+n0), Bool.not(eof) && is_none(asked) && Bool.not(fneed), Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, c)

def edge.where.k(+o: B.Opts, md: Q.Md, r: List<&1, Q.Src> & (U32 & Bool), pend: Q.Pd, +eof: Bool, +back: Nat, win: Q.Win, +asked: Maybe<&2, List<&2, P.Req>>, +fneed: Bool, p: Tc & U32, +n0: Nat, +dfs: B.Defs) -> Ew:
  (src, q) = r
  (c, +k) = p
  edge.where.q(o, md.n(md), src, q, pend, eof, back, win, asked, fneed, c, k, n0, dfs)

# Where Q is: past exactly one line since the piece came (n0: Q's line count
# then), at the piece from k+1 on (the line across the boundary handled),
# and whether nothing else waits; or not yet.
def edge.where(q2: Q.St, c: Tc, +n0: Nat) -> Ew:
  match q2:
    case Q.St{+o, md, src, pend, +eof, +back, win, +asked, +fneed, dfs}:
      edge.where.k(o, md, one_src(src), pend, eof, back, win, asked, fneed, tc.k(c), n0, dfs)

def edge.of(a: Q.Adv, c: Tc, +n0: Nat) -> Ew:
  match a:
    case Q.Went{q2}:
      edge.where(q2, c, n0)
    case Q.Want{st, r}:
      EWant{st, r, c}
    case a2:
      EOther{a2}

# The line across the boundary (and the end of a joined buffer) handled by
# Q, with fuel for its advances. Then the task is spliced in, or the piece is
# left to Q (also when the line needs reads: Q asks for them).
def edge(fuel: Nat, +n0: Nat, e: Ew, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  match fuel e:
    case _ EHere{q3, c2, True{}}:
      comb.splice(q3, c2, rest, eofp)
    case _ EHere{q3, c2, False{}}:
      seq_out(Q.go(q3), rest, eofp)
    case 0n EMore{q3, c2}:
      seq_out(Q.go(q3), rest, eofp)
    case 1n+g EMore{q3, c2}:
      edge(g, n0, edge.of(Q.advance(q3), c2, n0), rest, eofp)
    case _ EWant{st, +r, c2}:
      seq_out(Q.pump(0n, Q.Want{st, r}), rest, eofp)
    case _ EOther{a}:
      seq_out(Q.pump(0n, a), rest, eofp)

# Q.feed without room for the whole piece (Q handles only its first line).
def feed_line(q: Q.St, b: D.Bytes) -> Q.St:
  match q:
    case Q.St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      Q.feed.k(o, md, src, b, Q.Pd.len(pend), eof, back, win, asked, fneed, dfs)

def comb.clean(p: Q.St & Nat, b: D.Bytes, c: Tc, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  (q, +n0) = p
  edge(4096n, n0, edge.of(Q.advance(feed_line(q, b)), c, n0), rest, eofp)

def comb.piece(r: TRes, q: Q.St, b: D.Bytes, rest: List<&1, TOut>, +eofp: Bool) -> Step:
  match r:
    case TDirty{}:
      seq_out(Q.step(q, P.Chunk{b}), rest, eofp)
    case TClean{c}:
      comb.clean(q.n(q), b, c, rest, eofp)
    case TAgain{l, w, ws}:
      seq_out(Q.step(q, P.Chunk{b}), rest, eofp)

def comb.end(eofp: Bool, q: Q.St) -> Step:
  match eofp:
    case True{}:
      wrap(Q.step(q, P.Eof{}), BNone{})
    case False{}:
      wrap(Q.out(q, P.More{}), BNone{})

def comb.next(pcs: List<&1, TOut>, q: Q.St, +eofp: Bool) -> Step:
  match pcs:
    case Nil{}:
      comb.end(eofp, q)
    case TOut{b, r} <> rest:
      comb.piece(r, q, b, rest, eofp)

# ---------------------------------------------------------------------------
# One step
# ---------------------------------------------------------------------------

def none.chunk(p: Q.St & Bool, b: D.Bytes) -> Step:
  (q, +ok) = p
  match ok:
    case True{}:
      wrap(Q.out(q, P.More{}), BCol{[b], 1n})
    case False{}:
      wrap(Q.step(q, P.Chunk{b}), BNone{})

def none.len.k(q: Q.St, +ok: Bool, r: D.Bytes & U32) -> Step:
  (b, +n) = r
  none.chunk((q, ok && U32.is_le(minp(), n)), b)

# A piece starts a batch when Q is quiet and the piece has minp() bytes.
def none.len(p: Q.St & Bool, r: D.Bytes & U32) -> Step:
  (q, +ok) = p
  none.len.k(q, ok, r)

def none.step(i: P.In, q: Q.St) -> Step:
  match i:
    case P.Chunk{b}:
      none.len(quiet(q), BY.len(b))
    case P.Eof{}:
      wrap(Q.step(q, P.Eof{}), BNone{})
    case P.Ref{as}:
      wrap(Q.step(q, P.Ref{as}), BNone{})

def ask.run(p: Q.St & B.Opts, pls: List<&1, Pl>, as: List<&1, P.Ans>, +eofp: Bool, +dfs: B.Defs) -> Step:
  (q, +o) = p
  comb.next(HH.all(&1, TOut, tasks(o, pls, pairs(as), dfs)), q, eofp)

def plan.go(none: Bool, q: Q.St, pls: List<&1, Pl>, +reqs: List<&2, P.Req>, +eofp: Bool, +dfs: B.Defs) -> Step:
  match none:
    case True{}:
      ask.run(opts(q), pls, Nil{}, eofp, dfs)
    case False{}:
      wrap(Q.out(q, P.Ask{reqs}), BAsk{pls, eofp})

def plan.ask(q: Q.St, r: List<&1, Pl> & List<&2, P.Req>, +eofp: Bool, +dfs: B.Defs) -> Step:
  (pls, +reqs) = r
  plan.go(List.is_empty(&2, P.Req, reqs), q, pls, reqs, eofp, dfs)

# A batch is complete (ps in order): its reads are asked, all at once (with
# none, its tasks run in this step).
def plan(q: Q.St, ps: List<&1, D.Bytes>, +eofp: Bool, +dfs: B.Defs) -> Step:
  plan.ask(q, plan.reqs_all(plan.all(ps)), eofp, dfs)

def col.add(full: Bool, q: Q.St, ps: List<&1, D.Bytes>, +k: Nat, +dfs: B.Defs) -> Step:
  match full:
    case True{}:
      plan(q, rev_b(ps, Nil{}), False{}, dfs)
    case False{}:
      wrap(Q.out(q, P.More{}), BCol{ps, k})

def col.len(r: D.Bytes & U32, q: Q.St, ps: List<&1, D.Bytes>, +k: Nat, +dfs: B.Defs) -> Step:
  (b, +n) = r
  col.add(Nat.is_le(kmax(), 1n+k) || U32.is_lt(n, minp()), q, b <> ps, 1n+k, dfs)

def col.step(i: P.In, q: Q.St, ps: List<&1, D.Bytes>, +k: Nat, +dfs: B.Defs) -> Step:
  match i:
    case P.Chunk{b}:
      col.len(BY.len(b), q, ps, k, dfs)
    case P.Eof{}:
      plan(q, rev_b(ps, Nil{}), True{}, dfs)
    case P.Ref{as}:
      wrap(Q.out(q, P.More{}), BCol{ps, k})

def ask.step(i: P.In, q: Q.St, pls: List<&1, Pl>, +eofp: Bool, +dfs: B.Defs) -> Step:
  match i:
    case P.Ref{as}:
      ask.run(opts(q), pls, as, eofp, dfs)
    case P.Chunk{b}:
      wrap(Q.out(q, P.Ask{Nil{}}), BAsk{pls, eofp})
    case P.Eof{}:
      wrap(Q.out(q, P.Ask{Nil{}}), BAsk{pls, eofp})

def comb.step(i: P.In, seq: Bool, q: Q.St, pcs: List<&1, TOut>, +eofp: Bool) -> Step:
  match seq:
    case True{}:
      seq_out(Q.step(q, i), pcs, eofp)
    case False{}:
      comb.next(pcs, q, eofp)

def step.bat(b: Bat, q: Q.St, i: P.In, +dfs: B.Defs) -> Step:
  match b:
    case BNone{}:
      none.step(i, q)
    case BCol{ps, +k}:
      col.step(i, q, ps, k, dfs)
    case BAsk{pls, +e}:
      ask.step(i, q, pls, e, dfs)
    case BComb{pcs, +e, +s}:
      comb.step(i, s, q, pcs, e)

# Q's header definitions (-m), for the tasks.
def dfs_of(q: Q.St) -> Q.St & B.Defs:
  match q:
    case Q.St{o, md, src, pend, eof, back, win, asked, fneed, +dfs}:
      (Q.St{o, md, src, pend, eof, back, win, asked, fneed, dfs}, dfs)

def step.q(b: Bat, p: Q.St & B.Defs, i: P.In) -> Step:
  (q, +dfs) = p
  step.bat(b, q, i, dfs)

# One step of the program.
def step(st: St, i: P.In) -> Step:
  match st:
    case St{q, b}:
      step.q(b, dfs_of(q), i)
