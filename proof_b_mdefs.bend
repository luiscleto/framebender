import Base
import ./types.bend as B
import ./protocol.bend as P
import ./run.bend as R
import ./norm_seq.bend as W
import ./bytes_enc.bend as E
import ./MACHINE.bend as M

# MACHINE.bend's driver (drive, dstep, absorb, result, launch), copied with
# the sequential machine (norm_seq.bend) as the machine, for phase B's proof
# that this machine meets the law too (proof_b_machine.bend). Edit only to
# follow MACHINE.bend.

type DSt is Type:
  DSt{st: W.St, next: P.Next, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, out: String, notes: List<&2, B.Note>, done: Maybe<&2, Nat>}

def absorb.out(m: Maybe<&2, String>, +out: String) -> String & Bool:
  match m:
    case Some{t}:
      (out ++ t, True{})
    case None{}:
      (out, False{})

def absorb.k(st: W.St, nx: P.Next, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, r: String & Bool, +notes: List<&2, B.Note>, ns: List<&2, B.Note>) -> DSt:
  (out, ok) = r
  DSt{st, nx, cs, eof, reads, good && ok, out, List.append(&2, B.Note, notes, ns), None{}}

# A step's output is added as the text it holds (E.out); an output buffer that
# is not well formed clears good, and the run then has no result.
def absorb(s: W.Step, cs: List<&2, String>, eof: Bool, reads: Nat, good: Bool, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match s:
    case W.Step{st, o, ns, nx}:
      absorb.k(st, nx, cs, eof, reads, good, absorb.out(E.out(o), out), notes, ns)

def dstep.more(cs: List<&2, String>, eof: Bool, st: W.St, reads: Nat, good: Bool, +out: String, +notes: List<&2, B.Note>) -> DSt:
  match cs eof:
    case Nil{} True{}:
      DSt{st, P.More{}, Nil{}, True{}, reads, good, out, notes, None{}}
    case Nil{} False{}:
      absorb(W.step(st, P.Eof{}), Nil{}, True{}, reads, good, out, notes)
    case c <> t _:
      absorb(W.step(st, P.Chunk{E.enc(c)}), t, eof, reads, good, out, notes)

# One step of the driver. Asking for more after the end of the file gets
# nothing (so such a machine never stops). reads counts the reference reads.
def dstep(+fa: List<&2, B.Contig>, d: DSt) -> DSt:
  match d:
    case DSt{st, nx, cs, e, k, g, out, notes, Some{c}}:
      DSt{st, nx, cs, e, k, g, out, notes, Some{c}}
    case DSt{st, P.Finish{+c}, cs, e, k, g, out, notes, None{}}:
      DSt{st, P.Finish{c}, cs, e, k, g, out, notes, Some{c}}
    case DSt{st, P.Ask{+rs}, cs, e, k, g, out, notes, None{}}:
      absorb(W.step(st, P.Ref{M.truths(fa, rs)}), cs, e, Nat.add(k, List.length(&2, P.Req, rs)), g && E.reqs_ok(rs), out, notes)
    case DSt{st, P.More{}, cs, e, k, g, out, notes, None{}}:
      dstep.more(cs, e, st, k, g, out, notes)

def drive(fuel: Nat, +fa: List<&2, B.Contig>, d: DSt) -> DSt:
  match fuel:
    case 0n:
      d
    case 1n+f:
      drive(f, fa, dstep(fa, d))

def result.if(ok: Bool, r: R.Report) -> Maybe<&2, R.Report>:
  match ok:
    case True{}:
      Some{r}
    case False{}:
      None{}

# The report, if the machine stopped within the steps, made at most limit
# reference reads, wrote only well-formed buffers and asked for no window of
# more than 2^31 letters (good).
def result(d: DSt, +limit: Nat) -> Maybe<&2, R.Report>:
  match d:
    case DSt{st, nx, cs, e, k, g, out, notes, Some{c}}:
      result.if(g && Nat.is_le(k, limit), R.Report{out, notes, c})
    case DSt{st, nx, cs, e, k, g, out, notes, None{}}:
      None{}

def launch.of(m: Maybe<&2, R.Report>, r: String, v: String) -> Maybe<&2, M.Launch>:
  match m:
    case None{}:
      None{}
    case Some{rep}:
      Some{M.Launch{r, v, rep}}

def launch(b: W.Begin, argv: List<&2, String>, +fasta: String, +vcf: String, +cs: List<&2, String>) -> Maybe<&2, M.Launch>:
  match b:
    case W.Usage{}:
      None{}
    case W.Begin{st, r, v}:
      +n = M.bound(argv, fasta, vcf, cs)
      launch.of(result(drive(n, B.Fasta.parse(fasta), DSt{st, P.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}}), n), r, v)
