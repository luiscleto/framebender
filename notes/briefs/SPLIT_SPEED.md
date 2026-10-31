# Brief: a faster splitter (fb-splitspeed)

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws and proven
(`docs/LAWS.md`, `notes/split.md`). Phase I (`-m -any`, splitting multiallelic records) is on
branch `split`, where another agent (fb-split) is finishing the machine proofs. Your branch,
`split-speed`, starts from `split` at d365d9e; you own only the splitter: `norm_split.bend` and
the `proof_s_*.bend` files.

**Goal.** With `-m -any` on the 1000 Genomes cohort (about 2,500 samples per line) framebender
takes 1.8 s against bcftools' 1.3-1.5 s. Single-threaded the splitter costs about 5.2-5.7 s of a
5.5-6.2 s run (`notes/split.md`, "Stage 2"; `data/tmp/split/proof_progress.md`, "Milestone (2)
started"). Make it about 1.5x faster or more. Known leads:
- A gprof profile shows no single hot spot: runtime alloc/free about 25%, `cut` (range lists)
  14%, values 18%, `pick` 11%, writer 15%, GT 6%.
- Decision 19 in `reviews/responses-split-law.md`: look up each FORMAT key's Number once per line
  and split each column once, not once per record.
- Fewer allocations: reuse buffers, avoid building lists that are only walked once.
Measure before and after each change; keep only what pays.

**What must not change.**
- No law, plain statement or spec file: `LAWS.bend`, `MACHINE.bend`, `types.bend`, `run.bend`,
  `tan.bend`, `docs/`.
- `split_t` (`proof_s_drv.bend`: the byte splitter equals `B.Rec.parts`) keeps its statement and
  must check with `--check-only` and `--verdict` (through `test/bcheck.sh`).
- Every name from `norm_split.bend` or `proof_s_*.bend` used by a file outside them (the machine,
  `norm_seq.bend`, `proof_b_*`, `proof_c_*`, `proof_e_*`, `proof_run_*`: find them with grep)
  keeps its name, type and statement, so fb-split's work merges without changes. If a speed-up
  needs one of them changed, stop and report instead.
- Output byte for byte the same: `data/tmp/split/cmp_m.sh` against bcftools on the cohort,
  joined and HG002 files, `test/split.sh` (the fuzz), and the old build's output (`fb_m3`) on the
  same files, at `--threads 1` and the default.

**How to work.**
- Build with `./build.sh` into your own path. `BEND_NO_TELEMETRY=1`.
- Proof checks only through `test/bcheck.sh` (it limits memory and allows two at a time
  machine-wide; fb-split uses it too).
- Timings: `flock data/tmp/bench.lock nice -n 19 timeout ... taskset -c 0-15 ...`, interleaved
  with the base build, at least three rounds, `--threads 1` and the default. Nothing else should
  be timing at once; the lock does that.
- Scratch in `data/tmp/splitspeed/` (gitignored). `rm` only with literal paths.
- Commit on `split-speed` as you go. Don't push, don't merge, don't touch `split`.
- Write your results, what paid and what didn't, in a section "Splitter speed" at the end of
  `notes/split.md`.

**Report** (final message): the timings (before/after, `--threads 1` and default, cohort,
joined, HG002 chr22), the proof status of `split_t` (both modes), the identity results, the
commits, and anything you stopped on.
