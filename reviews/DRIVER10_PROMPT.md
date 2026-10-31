Review of framebender's branch `split`, in `/home/luisc/Work/bend-projects/framebender-split`
(read-only: do not modify, create or delete files in the repository, and do not switch branches;
compare with `git diff $(git merge-base main split) split`).

framebender is a VCF normalizer in Bend 2. Its program is proven: `PROOF.bend` proves every law
of `LAWS.bend` and `MACHINE.bend`, checked by bend2 and by the Lean BendTT kernel (`check.sh`).
What the proof does not cover is the trusted part: the driver (`main.bend`, `io64.c`, `io64.js`),
the build, htslib and Bend's runtime, plus everything the laws do not state: speed, memory, the
docs and the tests. The comment above `law machine` in `MACHINE.bend` lists what the driver must
do.

The branch groups three changes:
1. **Splitting multiallelic records** (`-m -any`, as `bcftools norm -m -any`). Its laws passed
   three review rounds and two later changes (a stray CR is refused; the step bound grows by
   (VCF length + 1)^2 with `-m` only): `reviews/*-split-*.md`, decisions 1-36 in
   `reviews/responses-split-law.md`. The design, checks and timings are in `notes/split.md`.
   The program changes are in the proven part (`norm.bend`, `norm_seq.bend`, `norm_run.bend`,
   `norm_split.bend`); the driver is unchanged.
2. **A faster splitter** (`notes/split.md`, "Splitter speed"): `norm_split.bend` rewritten for
   speed, proven equal to the spec (`split_t` in `proof_s_drv.bend`, statement unchanged).
3. **A warning about old indexes** (`notes/briefs/STALE_INDEX.md`): a run without `-W` that
   writes a BGZF `-o` file warns once per old index htslib would read for it, before anything
   is read; nothing is removed. Driver only: `main.bend`, `io64.c`, `io64.js`.

Review:
1. **The approved laws are the ones on the branch.** Compare `LAWS.bend`, `MACHINE.bend`,
   `types.bend`, `run.bend` and `docs/LAWS.md` with the decisions: anything changed that no
   decision approved, any approved law weakened, any law without `-m` changed?
2. **The proof is complete.** `PROOF.bend` imports every law and every law is proven (no TODO,
   no `unsafe` outside `main.bend`'s report, no assumption that is false). The step bound's use
   in `law machine` matches decisions 29-36.
3. **The old-index warning** (`main.bend`, `io64.c`): the names checked against htslib 1.24's
   search order (`hts_idx_check_local`, both formats), when it is printed, symlinks, directories,
   the `-o` path itself, names with odd bytes, that nothing is opened or changed, and that output
   bytes and exit codes never change.
4. **What the laws do not state, under `-m`:** memory (the output reserve in `norm.bend`, a line
   with thousands of ALTs or samples, `--threads 1` and 128), the 2^31-byte limits on a piece and
   on one write, speed regressions without `-m`, and the driver's assumptions in the comment on
   `law machine` (do they still hold when one input line becomes many records?).
5. **Docs and tests:** `README.md` (the `-m` row), `docs/USAGE.md` (`-m`, `--multi-overlaps`,
   the old-index warning, the differences from bcftools), `docs/LAWS.md`; `test/split.sh`,
   `test/gen_split.py`, the `-m` and warning cases in `test/index.sh`. Is anything stated that is
   false, or missing that a user of `bcftools norm -m -any` would need?

You may build and run it on small inputs (`./build.sh /tmp/<dir>/fb`; `bgzip`, `tabix`,
`bcftools` and `samtools` are installed), run `bend` checks on single files, and write test files
under `/tmp` only. Do not run anything on the whole-genome files in `data/`, and do not run the
whole `PROOF.bend` (the lead runs it; it takes a long time).

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
