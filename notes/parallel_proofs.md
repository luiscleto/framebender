# The parallel machine's proofs (phase E, step 3): design and areas

Goal: `MACHINE.bend`'s laws `machine` and `usage` hold with `norm_par.bend` (W) as the machine.
Then the rename: `norm.bend` becomes `norm_seq.bend` (Q), `norm_par.bend` becomes `norm.bend`,
and every proof file's `import ./norm.bend as Norm` that means Q becomes
`import ./norm_seq.bend as Norm`. No contract file changes. Brief: `notes/briefs/PARALLEL.md`;
the code and why it is correct: `notes/parallel.md`.

W runs Q unchanged, so every phase-B lemma about Q is reused as is. What is new:

| area | file(s) | what |
|---|---|---|
| A, adv-moved | `proof_b_simdefs.bend` (AdvG), the adv files, `proof_b_drive_pump.bend`, `proof_b_budget_*` | AdvG's Went, Want and Idle also give `S.Moved` (the state-level fact the line paths already prove) |
| B, seg | `proof_e_seg.bend` (+ helpers `proof_e_seg_*.bend`) | the segment lemma on run.bend's states |
| C, merge | `proof_e_merge.bend` (+ `proof_e_merge_*.bend`) | `W.merge` on pictured runs: MOk/MNo, RunInv, segok, the state it stands for |
| D, task | `proof_e_task.bend` (+ `proof_e_task_*.bend`) | the plan of a batch, and its tasks run with truthful answers |
| F, qif | `proof_e_qif.bend` (+ `proof_e_qif_*.bend`) | Q-level lemmas the wrapper needs that phase B does not state: a piece given as any good buffer (the copy), `W.feed_line` (feed without `reserve`), `set_win` |
| E, wrap | `proof_e_wrap*.bend`, later `proof_e_assemble.bend`, `proof_e_budget*.bend` | the wrapper's picture and invariant, each wrapper step, the budget, the law `machine` |

Shared definitions (fixed; ask the coordinator to change one): `proof_e_defs.bend` (the spec side
of the segment lemma), the picture types at the top of `proof_e_task.bend` and
`proof_e_merge.bend`, `S.Moved` (below). A deliverable's statement is fixed; helpers are free.

## Area A: AdvG gives the state-level step

In `proof_b_simdefs.bend`, after `guard`, define (exactly):

    # What advance did in the byte mode (byte mode before and after): the
    # lines it handled, taken from the front of the text still to come, moved
    # into the run. In any other case nothing is claimed.
    def Moved(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: StP, +p2: StP) -> Type:
      match StP.md(p) StP.md(p2):
        case MBP{+rp} MBP{+rp2}:
          &ls: List<&2, B.Line> -> ({B.Text.lines(intext(p, cs)) == List.append(&2, B.Line, ls, B.Text.lines(intext(p2, cs))) : List<&2, B.Line>}
            & {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls, fa, StP.o(p), P.specRun(rp))) : R.RunSt})
        case _ _:
          Unit

and add `{...} & Moved(fa, cs, p, p2)` as the last component of AdvG's Went, Want and Idle
tuples; also add `{StP.o(p2) == StP.o(p) : B.Opts}` (the options never change) to all five
cases, just before Moved in Went, Want and Idle and as the last component in Ended and Yield (so Went ends `... & ({guard(O, N, p2) == True{} : Bool} & ({StP.o(p2) == StP.o(p) : B.Opts} & Moved(fa, cs, p, p2)))`). Every producer
supplies it: a line path has `hrun` (`went_line`: `ls = [line]`, `hlc` gives the lines); the end of
a buffer (`part.len`), a Want and Idle keep the run (`ls = []`); the header paths have
`hold_step`; any producer whose p2 is in the String mode gives `Unit{}`. Consumers
(`proof_b_drive_pump.bend`, `proof_b_budget_step.bend`, `proof_b_budget_fast.bend`) take one more
component. Done when `PROOF.bend` passes `--check-only` and `--verdict` again.

## Area B: the segment lemma

`proof_e_seg.bend`'s `seg`: for any spec state S, lines ls whose first CHROM is c0, and
T = `L.run.go(ls, fa, o, SD.rs0(c0, l))`, if `SD.segok(w, c0, l, S, T)` then
`settle(run.go(ls, S)) == settle(SD.shiftS(c0, S, T))`. The argument (notes/parallel.md, "Why
merge.ok is enough"), as an induction over ls with an invariant relating the two runs:
- every item T writes or holds in its first CHROM run has key at least l. This is a *backward*
  fact: an item below l either stays in T's buffer to the end (where segok checks `keys_ge`) or is
  written or flushed (where the phantom, or a later written item at least l, makes T stop, and T
  does not stop). Prove "an item below l in the buffer, with last at least l, leads to a stop or
  stays to the end" by induction on the remaining lines, then use it in the forward induction;
- same CHROM (S's is c0): true buffer = (E not yet written) ++ (T's buffer); E's ready items are a
  prefix (sorted); T's ready items are empty while E is not all ready (their keys are at least l,
  at least E's); out = S's ++ E's written ++ T's; at the end E is all written (T left c0, or some
  line had inpos at least max(E) + w: T's buffered items and its last real item carry such
  inpos values);
- new CHROM: T's first line writes all of E (sorted, from S's last), then the runs differ in
  ended (T's on top of S's with S's CHROM pushed) and in the phantom, which only makes T stricter;
- T's later CHROMs are not in S's ended list nor S's CHROM (`chroms_ok`);
- line numbers: T's items are at line i, the true run's at S.n + i.

## Area C: merge on pictured runs

`proof_e_merge.bend`: `merge_yes`, `merge_no` (computation), `merge_inv` (the merged run is
good: T's buffers and counts, S's header), `merge_segok` (merge.ok on byte runs implies
SD.segok on the states they stand for: E's keys are at most `tl` by RunInv's `keys_le`, so
merge.ok's max(E) bound is at least segok's; `NR.spec.items` keeps keys, inpos and line numbers;
the phantom is line 0 in both), `merge_spec` (the merged run with S's whole output buffer before it
stands for SD.shiftS: S's buffer text is its output then its items' texts, by RunInv's length
equation).

## Area D: plan and tasks

`proof_e_task.bend`:
- `plan_all`: the plan hands every piece's buffer back (`F.find`, `BY.at`, `Q.text` return their
  buffer), gives two reads per piece with a line after its first LF (each within 2^31 letters by
  `plan.win`'s and `plan.reqs`'s le31 tests; their contigs are bytes) and none otherwise; and c0 is
  the CHROM of the first line after k.
- `batch`: with the truthful answers, `HH.all` = `HD.force` (lawful-halves' `all_force`), and each
  task gives its piece's buffer (the copy: `NR.put_bytes` into an empty block, same view) and a
  clean result only with TcOK: run the task's Q states through `adv_ok` (with area A's Moved) from
  the start picture (task.run0 is good: RunInv; its window is `win_truths` of `[r] = parts(r)` or
  WNone; `task.win`'s length test gives mb_win), compose the Moved facts along the loop (a Want
  swaps the window: same run, `ls = []`), and stop at Idle (no source: the text left is the line
  end's).

## Area F: Q interfaces

`proof_e_qif.bend` (statements to come with E's file; F starts from these needs):
- a piece given as any good buffer C.BT(len, t) of depth d with view `E.codes(c)` (the task's
  copy): `step_chunk`'s and `StepG2`'s guarantee, from `proof_b_drive_chunk.bend`'s core with
  BTc(c) replaced by the buffer;
- `W.feed_line` (Q.feed without `md.reserve`): the same as `feed_ok`, with the run unchanged and
  `S.intext(p1, cs) == S.intext(p, c <> cs)`;
- `Q.set_win` with the truthful answers to what was asked: the picture step_ref uses.

## Area E: the wrapper

Picture: Q's picture `p: S.StP` and the batch's (pieces as texts, a planned batch as `Pc`s,
results as `TOutP`s). What a wrapper state stands for: `S.report(fa, held ++ cs, O, N, p)`, the
held pieces' texts going before the driver's. Each wrapper step is shown by Q's lemmas
(step_chunk, step_eof, step_ref, pump_ok, out_ok), areas D and F, and for a clean piece: feed_line,
up to three advances (adv_ok with Moved), the edge check (Q's line count went up by exactly one, so
the Moved facts give the lines still to come as the piece's after k), then C and B. The budget
(`need`) counts Q's need over held ++ cs plus each batched piece's extra (at most the batch Ask,
two reads, one `Ask{[]}`): a batched piece has at least `W.minp()` = 256 bytes, whose allowance
leaves room for it (notes/bytes_proofs_budget.md: a line's Wants cost about 8 of its
(|fasta| + 3) * |line|).

### E's files and split

- E1 (`proof_e_wrap.bend`, helpers `proof_e_wrap_*.bend`): `wstep_chunk`, `wstep_eof`,
  `wstep_ref`, `wstart` over `proof_e_wrap_defs.bend` (WPic, InvW, StepGW: fixed).
- E2 (`proof_e_machine.bend`, helpers `proof_e_mach_*.bend`, `proof_e_bud_*.bend`): the laws
  `machine` and `usage` for W over `proof_e_mdefs.bend` (MACHINE.bend's driver copied with W as
  the machine). The assembly follows `proof_b_assemble.bend` with InvW in place of GoodN's
  machine facts and E1's lemmas in place of the sg_* ones; the budget is E2's design.

### The budget (E2): where the extra steps and reads are paid

Phase B's potential (`proof_b_budget_need.bend`): need = |cs| + [not eof] + 2 + HO + RD(nx) +
WA, WA the sum over the lines still to come of LA = 2 RW + 2 ZW (RW = 1 + max(1, |REF|),
ZW = 2 + FM; 0 for a malformed line). The bound gives (|fasta| + 3) per VCF byte, so a
Want-able line (at least 8 fields) leaves about |line| - 6 spare and a malformed one all of
its share: the start inequality has room of at least about |vcf| / 5 (less HO's share).

What W adds, per batched piece (each at least `W.minp()` = 256 bytes; smaller pieces are never
batched, except as the last piece of a batch, which costs Q's own steps only):
- its Chunk step into the batch (Q's |cs| count does not drop: the piece stays in held ++ cs);
- its share of the batch's closing step and of the Ask's answer step (one each per batch,
  none if no piece has reads);
- its two reads (pieces with a line after the first LF);
- one `Ask{[]}` step in the combine (after a merge: paid by Q's |cs| count of the piece, which
  drops as it leaves held without a Chunk to Q, and by its lines' LA, which the task handled; after
  a dirty piece that is not the batch's last: Q's step used that count, so one more).
So about 6 per batched piece, pre-paid in the potential from the start, e.g.
need_W = BN.need over (held ++ cs) + 6 * |pieces of cs of at least minp() bytes| + (what is left of
the held pieces' 6), each step consuming its part. The start bound then needs
6 * |vcf| / 256 more room than phase B's: a strengthened `bud_start` (WA <= (|fasta| + 3) * |vcf|
- |vcf| / 8 or similar). If the room is not there, tell the coordinator: a code change (fewer reads,
or a larger minp) is fine; a change of `M.bound` is a contract change and stops the phase.

## Code changes made for the proofs (outputs unchanged; checks rerun)

- Batches take only pieces of at least `minp()` = 256 bytes; a shorter piece ends the batch as its
  last (left to Q). Only a piece with a line after its first LF has reads (two); a batch with no
  reads runs its tasks in the same step (no Ask).
- Every planned read is at most 2^31 letters (`plan.win`'s test, else an empty read).
- `merge.ok` also checks that the true run's buffer is sorted and that every key in the task's
  buffer is at least l (both were facts of reachable runs that no invariant states).
- The phantom is recognised by line 0 only.
- A task gives no window for a contig name of more than 2^28 bytes (`mb_win`).
- The edge splices only if Q's line count went up by exactly one during it (the line across the
  boundary), which lets the proof name the lines still to come without tracking which buffer is
  Q's last source.
- No BEdge state: a boundary line that needs reads leaves its piece to Q (never seen on the whole
  genome: 772 of 772 batched pieces merged).
- `merge.ok`: T's last is the phantom only while T's CHROM is c0 (area C's counterexample).
- A task runs only if its first CHROM has at most 2^28 bytes (area D: the start run's RunInv).
- A task runs only on a piece of less than 2^30 bytes (area D: the copy's buffer lemma needs
  len + 8 < 2^31).

After these: `test/par.sh` 312/312 and `test/same.sh` 128/128 on all four builds, whole genome
`-c w`, `-c e` identical (plain and `.vcf.gz`), 1.87-1.88 s to /dev/null pinned.

## Rules for every area

- Every check through `timeout 1800 test/bcheck.sh <file> [--check-only|--verdict]` (4 GB, two at
  once across all agents; the lock waits). Never close a goal about a big Nat (2^28, 2^31, ...)
  by computation: keep bounds abstract or go through U32 lemmas.
- No commits, pushes or branch switches. `ls` before creating a file. Edit only your area's files
  (area A: the adv, pump and budget files named above, and simdefs for `Moved`).
- Notes in `notes/parallel_proofs_<area>.md`: status first, then what was hard.
- A statement that cannot be proven as stated (a counterexample, a missing hypothesis): stop and
  write it in your notes, then tell the coordinator; do not weaken it yourself.
