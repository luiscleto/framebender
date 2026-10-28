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
