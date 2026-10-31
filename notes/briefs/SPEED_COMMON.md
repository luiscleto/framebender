# Rules for the speed-phase agents (2026-10-31)

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws and proven
(`docs/LAWS.md`, `check.sh`). The speed phase makes it faster without changing what it does.
Several agents work at once, each on its own branch and worktree from main 03c3ed4.

- **No law changes.** `LAWS.bend`, `MACHINE.bend` (definitions and law statements; its comments
  only if the driver's promise changes), `types.bend`, `run.bend`, `tan.bend` and `docs/LAWS.md`
  stay as they are. Program files (`norm*.bend`) and proofs may change. If a speed-up needs a law
  or spec change, stop and report instead.
- **The gate.** At the end `check.sh`'s four steps pass (run them through `test/bcheck.sh`: two
  checks at a time machine-wide, 4 GB each, shared with the other agents), and the output is byte
  for byte the same as main's build on the test suites (`test/same.sh`, `test/par.sh`,
  `test/threads.sh`, `test/out.sh`, `test/index.sh`, `test/split.sh`) and on the files your change
  is about.
- **Timing.** `flock data/tmp/bench.lock nice -n 19 timeout ... taskset -c 0-15 ...`, interleaved
  with main's build, at least three rounds; say if the machine was busy. Only one timing runs at a
  time machine-wide (the lock does that). No whole-genome runs outside the lock.
- **Files.** Scratch under `data/tmp/<your name>/` (gitignored; `data` is the main checkout's
  data directory). `rm` only with literal paths. Commit on your branch as you go; don't push or
  merge, and don't touch other branches.
- **Notes.** Write what you did, what paid and what didn't, in `notes/speed.md` under a section
  with your name (create the file if it doesn't exist; other agents add their own sections, so
  keep to yours to ease merging).
- **Report** (final message): the timings before and after, the gate's result, the files changed,
  the commits, anything you stopped on.
