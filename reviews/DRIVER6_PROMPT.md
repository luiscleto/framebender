Review of framebender's trusted driver on the git branch `threads` (read-only: do not modify, create
or delete files in the repository, and do not switch branches).

framebender's program is proven: `PROOF.bend` proves every law of `LAWS.bend` and `MACHINE.bend`.
What the proof does not cover is the trusted driver, `main.bend` (Bend: the loop, `.fai` parsing,
answering reference reads) and `io64.c` (C effects). The comment above `law machine` in
`MACHINE.bend` lists exactly what the driver must do; in short:
- read the files' bytes, one character per byte (BGZF: the decompressed bytes, checked);
- hand each VCF piece to the program as exactly `E.enc` of its text, pieces of at most 2^31
  bytes (law machine holds for every way the VCF is cut into pieces, empty pieces included);
- answer each reference read of an `Ask`, in order, with exactly
  `truth(B.Fasta.parse(fasta), chrom, a, b)`, packed by `E.enc`;
- write exactly the bytes of each output buffer and every message, then exit with the code;
- report its own errors, each as one line on stderr with exit code 2.

The previous driver was reviewed and accepted (`reviews/*-driver5.md`). This change adds an option
`--threads N` (N from 1 to 128). The parser change and a new `law threads` (in `MACHINE.bend`:
`--threads N` where an option is expected changes nothing the program writes) were reviewed
separately and are proven; `B.Args.threads(argv)` is `Some{n}` only for a line `B.Args.parse`
accepts, with 1 <= n <= 128 (`proof_f_args.bend`, `threads_ok`). This review is about the driver
only: `git diff main -- main.bend io64.c io64.js` shows all of it, and `notes/threads.md` (section
"Step 2", from "Where the batch size lives" to "Open, for the driver review") explains it. In short:
1. The driver reads N once (`B.Args.threads`; none: 0) and sizes its work by it: the VCF
   read-ahead depth (`Io.threads`, 16 by default, at most 128), the reference reads started at
   once (32 by default, else N), and the batches: after every k pieces (16 by default, else N) it
   gives the machine an empty piece, which closes the machine's batch. The machine's own cap
   `kmax()` rises from 16 to 128.
2. A C constructor (`io64_rts_threads`, compiled out with `-DFB_NO_RTS_THREADS`) reads the
   program's words before `main` (`/proc/self/cmdline` on Linux, `_NSGetArgv` on macOS), applies
   its own copy of the parser's grammar (`io64_threads_of`), and when the line has a `--threads N`
   that `B.Args.parse` would accept, puts `--threads N` before `BENDRTS` so Bend's runtime runs at
   most N workers. It must fail safe: anything unexpected leaves `BENDRTS` as it is.

Check the new driver against the comment on law machine. Look for, among others:
- the constructor's grammar: any command line where `io64_threads_of` returns a count but
  `B.Args.threads` (types.bend) gives `None`, or a different count (a lone `-`, an empty word,
  `-f` taking `--threads` as its path, a missing value, leading zeros, huge numbers, repeated
  options, words after the VCF path, `+RTS ... -RTS` and `--RTS` split as Bend's runtime splits
  them: check the generated C's `main`); the effect of a wrong count (output must still be the
  same; only speed and memory may change); buffer and `malloc` handling, a `/proc/self/cmdline`
  of 1 MiB or more, `setenv` before the runtime reads `BENDRTS`, a user's own `BENDRTS`;
- the empty pieces (`loop.piece`): a piece lost, duplicated or reordered; the counter `c` across
  `Ask`s, the end of the file, a short last piece, an error; any interaction with the machine's
  `kmax()` (N = 128, N = 1);
- the read-ahead ring with a variable depth (`io64_ahead_n`): indexing modulo a depth that is set
  after the ring was used, or before it was initialised; `Io.threads` called more than once;
- reference reads grouped by g up to 128 (`IO64_FA_MAX` 128): slots, tickets, threads and
  descriptors; the first error in order still being the one reported;
- a message lost, or a wrong exit code; the one-step build (`bend main.bend -o`) and `build.sh`.

You may build and run it on small inputs (`./build.sh /tmp/fb_review`, then
`/tmp/fb_review norm -f test/edge/ref.fa --threads 3 test/edge/sorted.vcf`; `test/threads.sh`
shows how the branch was tested), and you may write test files under `/tmp` only. Do not run
anything on the whole-genome files in `data/`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
