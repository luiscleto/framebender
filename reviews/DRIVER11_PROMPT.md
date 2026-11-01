Review of framebender's branch `speed`, in `/home/luisc/Work/bend-projects/framebender-speed`
(read-only: do not modify, create or delete files in the repository, and do not switch branches;
compare with `git diff main speed`).

framebender is a VCF normalizer in Bend 2. Its program is proven: `PROOF.bend` proves every law
of `LAWS.bend` and `MACHINE.bend`, checked by bend2 and by the Lean BendTT kernel (`check.sh`).
What the proof does not cover is the trusted part: the driver (`main.bend`, `io64.c`, `io64.js`),
the build, htslib and Bend's runtime, plus everything the laws do not state: speed, memory, the
docs and the tests.

The branch is the speed phase: five changes to the proven part, none to the laws, the driver or
the tests. Each has a brief in `notes/briefs/SPEED_*.md` (rules in `SPEED_COMMON.md`) and a section
in `notes/speed.md` with the design, the timings and what was not done:
1. **fb-end:** a record with a valid INFO/END, and an out-of-scope record (gVCF's `<NON_REF>`,
   `*`, `<DEL>`, breakends), handled on bytes instead of decoded Strings (`norm_fast.bend`,
   `norm_seq.bend`, `norm_run.bend`).
2. **fb-tasks:** a task stopped as UNSORTED against its stand-in start key runs again from the key
   it stopped at, and a task's warnings are kept in the merge instead of its piece being redone
   (`norm.bend`, the `proof_e_*` files).
3. **fb-refuse:** a line `-m` cannot split is refused on bytes, with the code `split_problem`
   gives, instead of through the String path (`norm_split.bend`, `norm_seq.bend`).
4. **fb-rewrite:** the stand-in start key and the windows of a sparse piece, so pieces are not
   redone; buffers created at their size (`norm.bend`, `norm_fix.bend`, `norm_run.bend`).
5. **fb-memory:** buffers grow to twice their size below 64 MiB and to exactly their size above
   (`NR.want` in `norm_run.bend`, `norm_split.bend`).

The lead ran `check.sh`'s steps on the merged branch (`PROOF.bend` checks with `--check-only` and
`--verdict`) and the output suites (`test/same.sh`, `par.sh`, `threads.sh`, `out.sh`, `index.sh`,
`split.sh`) against main's build.

Review:
1. **The laws are unchanged.** No change to `LAWS.bend`, `MACHINE.bend`, `types.bend`, `run.bend`,
   `tan.bend` or `docs/LAWS.md`, and nothing in the proof that weakens what they say: no TODO, no
   `unsafe`, no new assumption, no statement about the spec changed to fit the code.
2. **Same output.** The proof says the output is the spec's; check that by running main's build
   and this one on inputs of your own that exercise the five changes (END values at their limits,
   gVCF shapes, refused `-m` lines, scrambled indels, records that move across piece boundaries,
   `--threads 1` and many, `-w` small and large). Any byte of difference in stdout, stderr or the
   exit code is a blocker.
3. **Speed and memory.** Regressions on plain files (HG002, a cohort) at `--threads 1` and the
   default; whether the figures in `notes/speed.md` and `docs/USAGE.md` hold; buffer sizes near
   the 2^31-byte limits (`NR.want` doubling, the 8 MiB windows, a 64 KiB first-run buffer that
   has to grow).
4. **Docs:** `docs/USAGE.md`'s "Speed and memory" note and the README's results clause: anything
   stated that is false or out of date after these changes, or a slow case left unsaid (the
   notes list what is still slow: END on a rewritten record, BAD_END lines, `-m` with many
   records waiting in the window).

You may build and run it on small inputs (`./build.sh /tmp/<dir>/fb`; main's build in
`/home/luisc/Work/bend-projects/framebender` the same way; `bgzip`, `tabix`, `bcftools` and
`samtools` are installed), run `bend` checks on single files, and write test files under `/tmp`
only. Time things with `nice -n 19` and `timeout`, one at a time. Do not run anything on the
whole-genome files in `data/`, and do not run the whole `PROOF.bend` (the lead runs it; it takes
a long time).

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
