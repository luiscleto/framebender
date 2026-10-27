# Driver fixes after review: brief

You are on framebender's git branch `bytes`. Do not switch branches, and do not commit: the lead
commits.

Another agent (`fb-bytes`) is proving the program (`norm*.bend`, `proof_*.bend`) on this branch.
Do not edit those files.

Yours: the trusted driver, `main.bend` and `io64.c` (and `io64.js` stubs). Make the seven changes
in `reviews/responses-driver3.md`. The reviewers' full reports are `reviews/*-driver3.md`. Keep the
trust-boundary comment in `MACHINE.bend` accurate: list a new error, such as "out of memory", there
and in `main.bend`'s header. `MACHINE.bend` is otherwise frozen. Ask the lead before changing
anything but that comment's error list.

After the changes:
- `bend main.bend --check-only` gives only the expected unsafe/foreign report.
- `test/compare.sh` gives 0, 0 and 1 (chr22, scr, `test/edge/sorted.vcf`).
- stdout, stderr and the exit code are byte-identical to the current binary on every
  `test/edge/*.vcf`, under `-c e` and `-c w`.
- Each fix is tested where it can be: an injected EINTR, a path containing LF, a `.fai` with a
  line length of 2^32 or more.

Use `nice -n 19` and a `timeout` for every build and run. Set `BEND_NO_TELEMETRY=1`. Report what
you changed and how you tested it.
