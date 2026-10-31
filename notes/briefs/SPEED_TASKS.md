# Brief: pieces redone on the main thread (fb-tasks)

Read `notes/briefs/SPEED_COMMON.md` first. framebender normalizes pieces of the file in parallel
tasks; the main thread (Q) merges their results and redoes any piece whose task result it cannot
splice. Two causes make Q redo work and become the bottleneck:

1. **False UNSORTED.** A task starts as if the last record written had its first line's POS. When
   that first line normalizes to the left (an insertion moved one base left), the task sees its
   own first record as unsorted, stops, and Q redoes the piece. `notes/split.md`, "Pieces redone
   on the main thread", has the cohort's cases and the lead: start the task from a lower stand-in
   key and leave the UNSORTED check to the merge, which already makes it.
2. **Tasks with notes.** `merge.ok` (`norm.bend`) splices a task only if it wrote no notes
   (warnings), because their line numbers count from the task's start. Any warning under `-c w`
   (a REF mismatch, a bad END) makes Q redo the piece. Fix 3 of `notes/briefs/END.md`: let the
   merge renumber and append a task's notes.

Both are phase-E machine changes (`norm.bend`'s tasks and merge, `proof_e_task_*`,
`proof_e_merge_*`, the threads machine's invariant and budget `proof_e_bud_*`). Do (1) first, then
(2). fb-end works on the bytes fast path at the same time; stay out of `norm_fast.bend`,
`norm_fix.bend` and their proofs.

**Measure** the cohort with `-m -any` (`data/tmp/split/gen/cohort.vcf`, `data/chr22.fa`), how many
pieces Q redoes before and after (a scratch counter, not committed), and a file with warnings
spread through it (e.g. HG002 chr22 with `-c w` and a reference where 2% of REFs mismatch, or
fb-end's 2% bad END file); plus HG002 whole genome, which must not get slower.
