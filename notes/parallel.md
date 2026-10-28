# The parallel machine (phase E)

Brief: `notes/briefs/PARALLEL.md`. Design: `notes/speed_plan.md`, section D. Branch `parallel`.

## Step 1: `lawful-halves`, laws drafted (2026-10-28)

`../lawful-halves` (`git init`, nothing committed): `defs.bend`, `halves.bend`, `LAWS.bend` (7
laws, open), `docs/LAWS.md`, `README.md`, `NOTES.md`, `check.sh`, `test/spot.bend`, MIT `LICENSE`.
The name is free on BendHub (13 characters: registered directly, no auction).

The difference from the plan: the plan had `pmap(f, t) == map(f, t)`. Bend 2.0.39 cannot state
that for every `f`, since closures are affine and template arguments must be closed. So the
package runs a list of tasks (closures `Unit -> B`, each holding its own input), and
`D.force(ts)` (call each once, in order) is the spec. For framebender this means one closure per
(piece, window) pair, built in the machine before the batch runs. The laws:
- `all_force`: `H.all(ts) == D.force(ts)`;
- `all_tree`: `H.all` runs the balanced tree of `ts`;
- `run_leaves`: running any tree gives the results of its leaves, in order;
- `tree_leaves`, `tree_balanced`: the tree of a list holds its values in order, and is balanced
  (halves of `n / 2` and `n - n / 2` at every node);
- `force_append`, `force_length`.

Checked: the laws type-check (`test/bcheck.sh`, 7 TODOs). `test/spot.bend` gives 18 of 18 True.
The compiled `H.run` forks (two task nodes and a join).

Next: the lead's three-model law review, then step 2 (the proofs).

## Step 1, round 1 of the law review (2026-10-28)

Reviews in `../lawful-halves/reviews/` (Claude, GPT, Grok), the lead's verdicts in
`responses-1.md`: 8 items, all accepted. Revised (laws, definitions, docs, tests; no proofs):
1. `check.sh` pins the parallel structure. The proof of `all_tree` must be exactly `{==}`;
   `halves.bend` must keep `x y = run(b, B, l) run(b, B, r)`; and the compiled C must have `run`
   make two tasks and a join. Tried on a copy: a sequential `run` is refused even with the
   parallel let kept elsewhere.
2. `run_leaves`, proven by Grok's route (one walk that hands its values back, with facts about
   them), checks in bend2. **But `--verdict` refuses any proof that passes a bare closure: bend's
   elaborator eta-expands it, and the BendTT kernel reports a mismatch with bend's checker.** So
   tasks became a datatype, `D.Task{fn: Unit -> B}`, run by `D.call`. This changes every law's
   types, which goes to the lead. With it, `run_leaves` passes `--check-only` and `--verdict`
   against the package's own files (`data/tmp/halves/spike2r.bend`).
3. to 5. New laws `run_shape`, `count_leaves`, `all_append`, `all_length` (11 in all).
6. `test/caller.bend`: tasks that each capture an `Array`, and
   `H.all(map(mk, ps)) == map(judge, ps)`. It checks, except for the call to the still-open
   `all_force`. Its task-making walk passes `--verdict` alone.
7. `test/spot.bend`: 22 of 22 True. It adds spines, internal `Tip`s, whole arrays, and direct
   comparisons for every law.
8. The work on one core (O(k log k) before the first fork and after the last join) is documented
   in `halves.bend` and `docs/LAWS.md`.

For framebender this means a batch's tasks are `D.Task{u => pump(S0, piece, window)}`, made by one
walk over the pieces (the `test/caller.bend` pattern).

## Step 1, round 2, and step 2: lawful-halves proven (2026-10-28)

Round 2 (`../lawful-halves/reviews/responses-2.md`, 7 items, all accepted) is applied:
- the new law `all_force_back` (the hand-back form);
- the wording fixes;
- `Task`'s field renamed `fn`;
- `check.sh` notes (the bend version its C check reads, a clear message without `PROOF.bend`,
  "`run` forks at every Node").

`build` now uses its own structural `half` and `hi` (code only).

All 12 laws are proven (`PROOF.bend` and `proof_*.bend`, about 1,070 lines). Each check ran
through `test/bcheck.sh`:
- `PROOF.bend --check-only` and `--verdict`: ALL PROOFS CHECK.
- `test/caller.bend`, which now imports `PROOF.bend`: ALL PROOFS CHECK, both.
- `check.sh`'s structure steps: pass (2 forks in `run`).
- `test/spot.bend`: 22 of 22 True.

Every proof walks a once-only list or tree a single time and hands it out with the facts it needs
(a `Sigma`). See `../lawful-halves/NOTES.md`.

## Step 3: paused before any code was kept (2026-10-28)

Lead's change of plan: stop after step 2; no step 3, no benchmarks. A first draft of the parallel
machine was started and then set aside, unchecked. It is in `data/tmp/parallel/norm_par.bend`
(ignored); nothing in the tree uses it, and `main.bend` is unchanged. To resume:
- **Layout.** A new module `norm_par.bend` wraps `norm.bend` (`Q`) unchanged: its own `St`
  (`Q.St` plus the batch: none, collecting, waiting for answers, combining), `Step`, `Begin`,
  `start` and `step`. `main.bend` switches to it for the code phase. `MACHINE.bend` names only
  `Norm.St`, `Norm.Step`, `Norm.Begin`, `Norm.start` and `Norm.step`, so after the proofs the
  wrapper takes those names (and today's machine moves to `norm_seq.bend`).
- **Tasks.** Each piece's lines after its first LF run Q's pump from a fresh run whose current
  CHROM is the piece's first (`c0`, parsed in the plan pass) and whose `last` is a phantom item
  (key `l`, the first line's POS, length 0). Starting with no current CHROM would not work: the
  first record's `new_run` resets `last`, which erases the phantom. A clean task has therefore
  written no key below `l`. A Want tries the task's next window, then makes it dirty. The task
  copies its piece (`NR.put_bytes`) for the combine.
- **Merge (`merge.ok`).** The checks between the true run S (after the line across the boundary)
  and the task's run T:
  - both in the body, neither stopped, no notes in T, T read lines;
  - `c0` not in S's ended list, and T's other CHROMs neither ended in S nor S's current one;
  - S's buffered items E start no lower than S's last;
  - if S's CHROM is `c0`: E's largest key and S's last are at most `l`; when T kept one CHROM, its
    buffer's first key is at least `l`, and E is all written within T (`max(E) + w` is at most
    an input POS T saw).

  Then the output this step is all of S's buffer (E is written), and the run becomes T's, with
  T's line numbers shifted by S's `n`, the counts added, and ended = T's ++ S's (with S's current
  CHROM pushed when it differs). T's buffer stays in place, so the splice needs no copy.
- **Where the draft stopped.** In its first check, `plan.two` could not infer the type of a
  nested pattern `(b, (+c2, +p2))`: split it into two destructuring helpers. Bend also refuses
  mutual recursion and a def calling one below it. The draft's helpers were sorted with
  `toposort.py` (scratchpad); loops with an early exit use a step record with a `more` flag, as
  `NR.flush.go` does.
- **Still to write after it checks:** the boundary test cases in the brief (CHROM change at a
  piece boundary, a record moving left across one, unsorted input, `-c e` mid-batch, warnings
  under `-c w`, files shorter than a batch); then `same.sh`, `compare.sh`, the gz suites and the
  tiny-piece builds; then timings.

## Step 3: the code, resumed (2026-10-28)

`norm_par.bend` (new, about 900 lines) wraps `norm.bend` (`Q`) unchanged; `main.bend` imports
it as `Norm` for the code phase (one line; `MACHINE.bend` still names `norm.bend`). It passes
`test/bcheck.sh norm_par.bend --check-only`. Changes from the paused draft:
- **The line across a boundary** may need two of Q's advances: with a non-empty `pend`, Q first
  handles the joined line, then drops the joined buffer (`[SB{joined, end}, SB{piece, k+1}]`, then
  `[SB{piece, k+1}]`). `edge` advances up to 3 times until Q's input is exactly the piece from
  `k+1`. If the line needs reads, they are asked (`BEdge`) and the splice is still tried after the
  answer; the draft dropped the task then (every piece after a window miss went sequential).
- **After a merge, Q's window is the task's last window**, not the true run's (which is the one
  before the batch); the next boundary line is then usually answered from it.
- **`c0` comes from the first complete line only** (the bytes before the first tab before its LF);
  a piece without such a line is left to Q. The draft's search ran past the LF.
- **Exactly two reads per piece**: one window (`margin()` before the smaller of the first and last
  POS to `margin()` past the larger, when both are on one CHROM and it fits one read) and an empty
  read; else `ahead()` letters on from the first line and `ahead()` back from the last. So each
  piece's answers are the next two (`pairs`), with no splitting walk (Bend refuses mutual
  recursion and a computed scrutinee, and its termination check wants a structural argument).
  At most 2 reads per piece, each at most 2^31 letters: the read bound is not at risk.
- The task builds its windows itself (in parallel). The phantom is recognised by line 0 and
  length 0.

Why `merge.ok` is enough (to become the segment lemma; S: the true run after the boundary line,
E: its buffer, T: the task's run from the phantom state on the piece's lines L):
- Any `l` is correct; it only has to make T strict. Every item T writes or keeps in its first
  CHROM run has key at least `l`: a written one passed the check against the phantom or a later
  one, and the buffer left at the end is checked (`ck_ge`).
- Same CHROM (S's is `c0`), with max(E) and S's last at most `l`: in the true run the buffer is
  always (E not yet written) ++ (T's buffer). An item is inserted after every E item (its key is at
  least `l`). At each line the ready prefix is E's ready prefix, then T's ready items only if all of
  E is ready: an E item that is not ready has a key at most every T item's. So the output is S's,
  then E's written items, then T's; the UNSORTED checks pass whenever T's do (E starts at or
  above S's last, and T's first written key is at least `l`, which is at least E's keys and S's last).
  All of E is written when T leaves `c0` (a new run writes the whole buffer) or when a line of T has
  an input POS of at least max(E) + w; T's buffered items and its last real item carry such POS
  values (`mlow`).
- New CHROM (S's is not `c0`): T's first line writes all of E (it starts at or above S's last),
  `c0` must not have ended in S, and from then on the two runs differ only in `ended` (S's current
  pushed onto S's list, under T's) and in the phantom, which only makes T stricter.
- T's later CHROMs are checked against S's ended list and S's current one (`chroms_ok`). Notes,
  stops, String mode, reads the windows cannot answer: the piece goes to Q.

Checks so far (each against `data/tmp/parallel/fb_seq`, main's machine built from this tree):
- `test/same.sh`: ALL IDENTICAL (128 runs) for the normal build and the builds with `piece()` of
  1,000, 70,001 and 300 bytes.
- New `test/gen_par.py` and `test/par.sh` (the brief's batch-boundary cases; 39 files on a 4-contig
  FASTA): CHROM changes exactly at, straddling and just after piece boundaries of 300, 1,000 and
  70,001 bytes; indels in long repeats right after boundaries that normalize far left; POS back
  within and beyond the window; swaps; a CHROM revisited; a REF mismatch, a malformed line and an
  unknown CHROM in the middle of a batch; many warnings; header only, one record, fewer than a
  batch of pieces, exactly 31/32/33/64 pieces of 1,000 bytes and a few bytes more, a long header,
  no final LF, CRLF; and SNP-only variants (no left moves, so `-w 1` runs to the end). Under `-c e`
  and `-c w`, `-w` 1, 50, 10,000 and the default: ALL IDENTICAL (312 runs) for each of the four
  builds.
- An instrumented build (tags on stderr; scratch) shows the paths are exercised: chr22 at the normal
  size merges 9 of 9 pieces; at 1,000-byte pieces `snp_sorted -w 1` merges 1,063 of 1,063, and the
  suite hits every fallback (dirty for a stop, a window miss, no complete line; no merge for notes
  or an unflushed buffer; a boundary line asking for reads, then merging).
- Limitation seen: a piece merges only if the true run's buffer is written within it, so pieces
  spanning fewer than `w` bases (tiny test pieces, or very dense regions) go to Q. At 3.5 MB a piece
  spans megabases.

Whole genome and the rest of the brief's checks (normal build unless said):
- Whole genome, `-c w` and `-c e`, plain and the GIAB `.vcf.gz` (same relative path): stdout
  (2,836,801,740 bytes), stderr and exit code identical to `fb_seq` on the plain file. The
  instrumented build merges 772 of the 772 batched pieces (the first piece runs in Q), with no
  fallback.
- `test/compare.sh` (bcftools 1.24): chr22 0, scr 0, `test/edge/sorted.vcf` 1 (the `<DEL>`
  record, as before), whole genome 0, whole genome from the `.vcf.gz` 0.
- `data/tmp/speed/gztest.sh` on the four builds (normal, 70,001, 1,000, 300): ALL IDENTICAL (1,008
  comparisons).
- `data/tmp/speed/eoftest.sh` (BGZF files without their end block): as expected for the normal,
  70,001 and 1,000 builds. The 300 build fails 6 checks (`edge_in`, `edge_in2`, `-c e`): it stops
  with REF_MISMATCH at line 10 before the driver reads the last piece, so the missing end block is
  never reported. Main's machine built with 300-byte pieces (`fb_seq_300`) does the same and fails
  4 more (`-c w`, UNSORTED at line 21); the parallel build collects ahead and meets the driver's
  error sooner. Damaged BGZF is outside the law; both stop with a prefix of the output. Not a
  regression; the suite was only ever run at 70,001 and 1,000.
- The gate, each through `test/bcheck.sh`: `examples.bend` 15 TODOs, `main.bend` 62 defs rely on
  unsafe or foreign code, `PROOF.bend --check-only` and `--verdict` ALL PROOFS CHECK, `MACHINE.bend`
  15 TODOs. All as before.

Timings (whole genome, `-c w`, 4,048,342 records; `data/tmp/parallel/bench.sh`, bench4's protocol:
`nice -n 19`, interleaved, inputs in the page cache, nothing else running; 3 rounds each; seq:
main's machine, par: this one):

| input, output | pinned 0-15: seq / par / bcftools | unpinned: seq / par / bcftools |
|---|---|---|
| plain, /dev/null | 4.26-4.45 / **1.80-1.81** / 5.67-5.76 s | 4.86-6.52 / 2.22-2.54 / 5.55-5.81 s |
| plain, file | 4.83-4.92 / **2.37-2.42** / 7.77-7.88 s | 6.02-6.45 / 3.00-3.19 / 7.81-7.85 s |
| `.vcf.gz`, /dev/null | 4.37-4.43 / **2.13-2.19** / 5.78-6.07 s | 5.04-6.15 / 2.73-2.88 / 5.72-6.08 s |
| `.vcf.gz`, file | 4.80-4.96 / **2.79-2.81** / 7.90-8.00 s | 5.53-7.21 / 3.72-3.86 / 7.96-8.20 s |

To a file, pinned: 3.3x bcftools on the plain file (2.0x main's machine), 2.8x on the `.vcf.gz`.
chr22 (pinned, /dev/null, 5 rounds): seq 0.077-0.087, par 0.058-0.063, bcftools 0.075-0.077 s.
Peak memory, whole genome: 782 MB (main's machine 141 MB; the plan said about 400 MB).

Where the time goes now (driver effects timed in the generated C, `patch.py`; pinned, /dev/null,
1.82-1.89 s wall): FASTA windows `Io.fa_read` 0.67-0.73 s (794 reads, one after another), VCF
pieces `Io.read_block` 0.35-0.37 s (waiting: the read-ahead thread reads one piece ahead, but a
batch takes 32 at once), the machine 0.76-0.78 s. So the driver is now more than half the time:
step 4 (the batch's reads answered in parallel, reading several pieces ahead) is the next lever,
toward the plan's 1.0-1.3 s to /dev/null.

Open points for the lead:
1. Memory 782 MB at K = 32 (the lead accepted about 400 MB). The big items per piece: the window
   block (a whole piece's span, about 8 M letters, in a power-of-two block), the task's output
   buffer, the piece and its copy. K = 16, or dropping the copy, would roughly halve it.
2. The copy of each piece (made in the task, in parallel) is kept so a piece that does not merge
   can go to Q. Q drops the piece at its end, so the task cannot hand it back without stopping
   just before the last partial line; that saves the copy but adds a proof obligation (the piece
   is still in Q's input at every dirty exit). Left as is for now.
3. A piece merges only if the true run's buffer is written within it (or a CHROM change writes
   it). Fine at 3.5 MB; with pieces spanning fewer than `w` bases, every piece goes to Q.

Next (after the lead's look): the proofs (segment lemma, `merge.ok`, the machine), then step 4.
Scratch: `data/tmp/parallel` (builds `fb_seq`, `fb_par`, `fb_par_{300,1000,70001}`, `fb_seq_300`,
the instrumented `norm_pdbg.bend` and `fb_dbg_*`, the timed `fb_par_t`, `bench.sh`, `wg/`).

## Step 3, lead's decisions (2026-10-28)

The lead reproduced the checks and committed the code (eadf3dc). Decisions: keep the per-piece
copy (fewer proof obligations); the merge limitation is accepted; measure K = 16 against K = 32.

K (whole genome, plain, `-c w`, to a file, pinned 0-15, interleaved, 5 rounds): K = 32 2.35-2.41 s,
782 MB peak; K = 16 2.41-2.46 s (2-3% slower), 608 MB. Within 5%: **K = 16** (`kmax()`). With it:
`test/par.sh` 312/312, `test/same.sh` 128/128, whole genome `-c w` and `-c e` identical to main's
machine.

## Step 3, the proofs: started (2026-10-28)

Design and areas: `notes/parallel_proofs.md`; brief for the area agents:
`notes/briefs/PARALLEL_PROOFS.md`. Statement files (deliverables `?TODO`): `proof_e_seg.bend` (B),
`proof_e_merge.bend` (C), `proof_e_task.bend` (D), `proof_e_qif.bend` (F), `proof_e_wrap.bend`
(E1), `proof_e_machine.bend` (E2); shared definitions `proof_e_defs.bend`,
`proof_e_wrap_defs.bend`, `proof_e_mdefs.bend`; area A edits `S.AdvG` in place.

Herdr workspaces (one Claude agent each; close when done): fbe-a w1P (A, adv Moved), fbe-b w1Q
(B, seg), fbe-c w1R (C, merge), fbe-d w1S (D, task), fbe-f w1T (F, Q interfaces), fbe-e1 w1V (E1,
wrapper steps), fbe-e2 w1W (E2, budget and assembly).

Code changes for the proofs so far (outputs unchanged; listed in `notes/parallel_proofs.md`):
minimum piece size 256 for batching, reads only for pieces with a line, le31 tests on reads,
sortedness and key tests in merge.ok, phantom by line 0, task windows only for contig names of at
most 2^28 bytes, the one-line edge check, no BEdge, the phantom-CHROM test in merge.ok (area C's
counterexample), the CHROM-length guard on tasks (area D).

## Step 3: proven, renamed, gate passed (2026-10-28)

All areas proven (each area's notes: `notes/parallel_proofs_<area>.md`; design:
`notes/parallel_proofs.md`): A (AdvG's Moved and options clauses), B (the segment lemma: the true
run over a piece's lines equals shiftS exactly), C (merge on pictured runs), D (the plan and the
batch's tasks), F (Q interfaces: a piece as any good buffer, feed_line, set_win), E1 (each wrapper
step), E2 (the budget: phase B's potential plus 12 per piece of at least 256 bytes, the start
bound with that room; the assembly; `machine` and `usage`). New proofs: 64 files `proof_e_*.bend`,
about 19,400 lines; phase-B files touched for AdvG and the rename: 72 (+215, -146). Every Herdr
workspace of the phase is closed.

**The rename** (a one-off script, dry-run on a scratch copy first): `norm.bend` is now the
parallel machine (it imports the sequential one as `./norm_seq.bend as Q`); `norm_seq.bend` is the
former `norm.bend`; proof files import `./norm_seq.bend` where they mean the sequential machine.
`MACHINE.bend` and the rest of the contract are unchanged. `PROOF.bend`'s `M.machine` and
`M.usage` forward to `proof_e_machine.bend`. Phase B's own proof that the sequential machine meets
the same law still checks (`proof_b_machine.bend`, over `proof_b_mdefs.bend`, MACHINE.bend's driver
copied with `norm_seq.bend` as the machine). The driver copy over the parallel machine
(`proof_e_mdefs.bend`) is gone: its users now use MACHINE.bend's own driver.

**`test/bcheck.sh`**: a 64 MB stack (`ulimit -s 65536`), and the 4 GB cap for every check through the
cgroup (`MemoryMax=4G`, as `--verdict` had). The largest harnesses overflowed bend's machine stack
at random with the default 16 MB, and an address-space cap leaves no room for 64 MB thread stacks.

**The gate**, through `test/bcheck.sh`: `PROOF.bend --check-only` ALL PROOFS CHECK, `--verdict` ALL
PROOFS CHECK (39 s); `examples.bend` 15 TODOs and `MACHINE.bend` 15 TODOs (the imported laws, as
before); `main.bend` 62 defs rely on unsafe or foreign code (as before).

**The final build** (`./build.sh` from the renamed tree): `test/par.sh` 312/312 and `test/same.sh`
128/128 on the normal, 70,001, 1,000 and 300-byte builds; whole genome `-c w` and `-c e`, plain and
`.vcf.gz`, identical to main's machine; `test/compare.sh` 0 differing records on chr22, the whole
genome and the whole genome from `.vcf.gz`.

Timings (whole genome, `-c w`, `data/tmp/parallel/bench.sh`, interleaved; seq: main's machine):

| input, output | pinned 0-15: seq / par / bcftools | unpinned (2 rounds) |
|---|---|---|
| plain, file | 4.86-4.94 / **2.39-2.49** / 7.87-8.01 s | 5.18-5.82 / 3.21-3.56 / 7.86-7.90 s |
| `.vcf.gz`, file | 4.88-4.93 / **2.72-2.74** / 8.03-8.09 s | 5.23-5.86 / 3.90-4.07 / 8.09-8.17 s |
| plain, /dev/null | 4.34-4.47 / **1.84** / 5.40-5.57 s | |
| `.vcf.gz`, /dev/null | 4.35-4.43 / **2.16** / 5.58-5.79 s | |

Next (the lead's call): step 4, the driver (the batch's reads answered in parallel, reading
several pieces ahead), which is now most of the time.
