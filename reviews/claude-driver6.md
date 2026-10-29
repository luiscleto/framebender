# Driver review 6 (`--threads N`), branch `threads`: report

## Context
Read-only review of `git diff main -- main.bend io64.c io64.js` against the comment on law machine.
Plan mode was on, so nothing was built or run. I read the code and the generated C of the branch
(`data/tmp/threads/bin/fb.c`: its `main` and `corpus_setup`).

## Verdict: ACCEPT (three minor items, none of which changes the output)

What was checked and found right:
- **Grammar** (`io64_threads_of` against `Args.word/step/thr/done`, `Pos.read`): a lone `-` and `""`
  are paths on both sides (`x[0]=='-' && x[1]!=0` is the same test as `starts_with "-" && length > 1`).
  `-f --threads` takes `--threads` as the path. A missing value leaves an option pending, and both
  give none. Leading zeros are accepted by both (`0128` gives 128). `0`, `129` and huge values are
  refused (the cap of 1000 cannot overflow). With repeated `--threads`, every one must be valid and
  the last counts. A second `-f` or a second path is refused. `-c`/`-w` values match. `w[0]` must be
  `norm`. Nothing found where the C gives a count and `B.Args.threads` gives `None`, or a different
  count.
- **Runtime split:** it matches `main` in the generated C exactly. `--RTS` is tested first, also
  inside `+RTS`. A stray `-RTS` is dropped. Word 0 is skipped on both sides.
- **`BENDRTS`:** the new value is prepended, so the user's own `--threads`, and `+RTS --threads`
  (argv comes after env in `rts[]`), still win. The `--threads N` pair is consumed as a pair, so how
  the user's tokens parse does not change, and a malformed user `BENDRTS` fails exactly as before.
  The size is correct (`32 + strlen`). `setenv` runs in a constructor, before `main`'s `getenv`.
  The runtime caps workers at `CUBE_T`, so 128 is safe.
- **`loop.piece`:** no piece is lost, duplicated or reordered. The read happens only in the False
  branch. `c` survives an `Ask` (`loop.ref`) and resets only on the empty piece. A short last piece
  or the end of the file just adds an empty `Chunk` before `Eof`, which law machine allows. Errors
  go through `read_fail` as before. For N = 1, every piece is followed by an empty one. For N = 128,
  the batches may be misaligned with `kmax()` at first, which costs speed only.
- **Ring:** `io64_ahead_n` is set by `Io.threads` in `main.t` before any `Io.read_block` (the `.fai`
  read included). It is called once, and every ring use happens after `io64_ahead_start` resets the
  counters. The helper reads the value only after `pthread_create`. The index stays below
  `IO64_AHEAD_MAX`.
- **Reference reads:** g ≤ 128 = `IO64_FA_MAX`, and each group waits for all its tickets before the
  next group starts, so a slot is always free. The first failing wait stops the program, in order,
  as before.
- **Messages and exit codes:** unchanged. `io64.js` has a no-op `Io.threads`. `build.sh` and the
  one-step `bend -o` pick up the constructor by default.

Minor:
1. **minor:** `io64.c`, `io64_rts_threads`. A command line of 1 MiB or more (allowed when `ARG_MAX`
   is above 1 MiB, e.g. a 2 MiB `ARG_MAX` with an 8 MiB stack) makes the constructor give up
   silently. The input is `norm -f r.fa --threads 2 <a path of about 1.1 MB>`, which runs with one
   worker per CPU. It fails safe. The fix: say "a command line of 1 MiB or more" in the comment's
   list of unexpected cases, or grow the buffer.
2. **minor:** `io64.c`, `io64_ahead_n`. It is a plain static, written by one effect and read by
   later effects and by the helper. It relies on the runtime ordering IO effects in sequence
   (happens-before). It is correct as used. The fix: a one-line comment, or make it `_Atomic`.
3. **minor (cosmetic):** two comment lines overflow the wrap width: `main.bend`'s header ("...also
   sets Bend's worker threads from it. Every error of its own prints one") and `io64.c`'s
   `Io.fa_start` comment ("in order (32, or --threads N: main.bend's answers). The read's block
   ..."). The fix: rewrap them.
