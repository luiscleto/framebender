## Driver review 8, round 2: ACCEPT, with four minor items still open

The trusted output path has no blocker or should-fix left. The code is unchanged since my last run: a fresh `./build.sh` gives a binary byte-identical to the one I tested then.

**Your list vs. what I reported.** `reviews/claude-driver8.md` holds my plan draft, not my final report. So decisions 1, 5, 6 and 7 answer the draft. The four minor findings of my final report were never seen, and they are still open (items 1–4 below).

**The seven decisions (yours and the other reviewers'), checked in the code and re-run:**
1. **Pipe or FIFO input named by `-o`:** fixed. `cat sorted.vcf | fb -o /dev/stdin /dev/stdin` and one FIFO given as both VCF and `-o` are now refused ("output is an input", exit 2) with no hang.
2. **SIGXFSZ:** fixed. Under `prlimit --fsize`, with no trap, both BGZF and plain output end with exit 2, "cannot write <path>", the file stopped at the limit, and no end-of-file block. The 300,000-byte BGZF run fits under its limit and exits 0, which is correct.
3. **Failed `close` after the end-of-file block:** fixed. With `EIO` injected into `close` through `LD_PRELOAD`, the run exits 2 with "cannot write <path>", and the file is bgzip's bytes without the end-of-file block.
4. **`test/out.sh` exit status:** fixed, it ends with `exit "$bad"`.
5. **The final carried bytes:** fixed. `wend` is set for every full window, and at the end `ps == wend` is exactly the case where bgzip's next read returns nothing.
6. **The prefix comment:** fixed, in law machine's comment and in `io64.c`.
7. **Tests:** added, but the EAGAIN test can't catch what it targets (item 3 below).

**Re-run, all passing:**
- `-Oz0` to `-Oz9` on `sorted.vcf` and on a header-only file match `bgzip -l L` byte for byte.
- Every `gen_out.py` case, `tailwin` included, matches at levels 0, 6 and 9 with `--threads` 1 and 128.
- `tailwin`'s output is exactly 65,280 bytes and identical to bgzip's.

The fixes add no new problem beyond items 1 and 2.

**Open items:**
1. **minor:** `io64.c`, `io64_out_open` compares the output with stderr when stderr is a FIFO, so `fb norm -f ref.fa -o /dev/stdout in.vcf 2>&1 | tail` is refused ("output is an input /dev/stdout"). With the same redirection, `-o -` and plain stdout both work; I re-ran all three. Output and messages sharing one pipe loses no data and doesn't hang, and it is what the user asked for. Fix: compare with stderr only when stderr is a regular file, where emptying the file would wipe the messages. Drop the `-o /dev/stderr` FIFO test, or keep it as an accepted case.
2. **minor:** `io64.c`, `io_out_close_run`, the take-back after a failed `close` reopens `io64_out.path` by name. If the path was renamed, replaced or re-pointed as a symlink during the run, `ftruncate` cuts a different file. Fix: keep the output's device and inode from the first open, `fstat` the reopened descriptor, and truncate only if they match.
3. **minor (test):** the EAGAIN test in `test/out.sh` §2 can't tell a writer that keeps going after its first error from one that stops. The reader waits 2 s, so every later write also hits the full pipe, and the run exits before anything is read. Fix: add an `LD_PRELOAD` `write()` shim, like the close shim, that fails the k-th write to the output once with `EIO` and lets later ones through. Then check that the file is a prefix of bgzip's bytes with no end-of-file block; a writer that went on would leave a gap.
4. **minor (test):** `tailwin` passes with or without the `wend` fix. The machine always ends its text with an LF (checked again on `nolf.vcf`'s output), and with a final LF the old cut gives the same single block. The fix is correct but can't be reached from real output. Either say so in `gen_out.py`'s comment, or test `io64_cut`/`io64_out_tail` directly in C on a text with no final LF.

The scripts I ran (`r1.sh` to `r5.sh`) and both builds are in `/tmp/claude-1000/-home-luisc-Work-bend-projects-framebender-gz/344bf104-98d7-45c9-8322-c56328d2dcf7/scratchpad/fb8/`.
