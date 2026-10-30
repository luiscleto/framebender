**Round 2 verdict: ACCEPT once two wording fixes are made in law `machine`'s comment.** There are no blockers. Both fixes are should-fix items in the contract text (`data/tmp/index/machine.diff`); the design, the laws and the prototype are otherwise sound.

## Checks

**(1) Every decision is carried out.** Each of decisions 1–19 is in the note, the draft diffs and the prototype, as the "Round 1" section says.
- **The lock:** a line holding `END=` anywhere is parsed under a mutex. That is a superset of the condition under which htslib writes its static, and `tbx_parse1` has no other shared write once logs are off.
- **The FIFO:** `O_NONBLOCK`, with ENXIO reported as "not a regular file".
- **Index errors:** they have their own flag, read only at `out_close`.
- **URL names:** htslib gets `./` before a relative path.
- **The threads parser:** `io64_threads_of` recognizes the eight words and leaves them alone in value positions.
- **The empty index** and **the libcurl-free htslib**, with the `nm` check, the version check and the `static_assert`.

**`index_sink` is true.** Where an option is expected, an index word reaches `Args.word`'s new branch, which changes only `Drv.idx`. `ok`, `keep` and `pend` stay as they were, and no later step reads `idx`: `set_thr`, `set_out` and `set_typ` copy it through, and `Args.sink` and `Drv.thr` ignore it. If `pre` already holds an error, both sides are `None`.

**It says what decision 5 asks.** `Args.output` and `Args.threads` are unchanged, and `Args.index.done` applies `Args.idx.mk(Drv.idx(t), Args.sink(t))` to the same parse state that `Args.sink.done` uses. So the index is the index of `Args.output`'s file by definition.

**(2) Nothing new is broken.**
- No approved law or definition is weakened. Only `Args.parse` (on lines it used to refuse), `Drv` and `usage()` change.
- The eight words still end in the old VCF-path fallback with `ok` False, so every command line accepted before gives the same `Cfg`, sink and thread count.
- The open order in the prototype (`io64_out_open` and `idx_open`) is safe: every check, and the creation of the temporary file, comes before `ftruncate`.

## Should fix

1. **Law `machine`'s comment says "Once the open reached (6), a run that does not exit 0 leaves no index at either name."**
   - **Why it's wrong:** step (6) can itself fail, for example in a sticky directory, or when the first unlink succeeds and the second fails (`idx_unlink_old`). The run then exits 2, leaving an old index next to the emptied `-o` file.
   - **Fix:** say "once (6) completed", and add that a failure in (6) leaves the old indexes it could not remove. Or reorder the steps, as in question 2 below.

2. **Law `machine`'s comment says "no run leaves the temporary file unless it is killed"** (the note's decision 9 says the same).
   - **Why it's wrong:** Bend's runtime stops with `_exit(1)`; I generated the C from `main.bend` and checked `err_fail`. That covers "bend: out of memory" and "a Nat past 2^48", so the `atexit` handler never runs and `<index>.tmp` stays behind.
   - **Fix:** say "unless it is killed or Bend's runtime stops it". Add that case to the test plan, expecting the stray `.tmp` and no index. The stray file does no harm, since htslib never reads it.

## Answers to the round-2 questions

1. **The lock on a superset of htslib's test:** yes. It is correct, and its cost is within the noise.
2. **The open order:** accept, but I'd move step (6), the unlink, before step (5), the `ftruncate`.
   - After a successful `O_WRONLY` open of a regular file, `ftruncate` almost never fails.
   - With that order, every failure leaves the `-o` file's old bytes intact. At worst an unchanged file has lost its index, which only means re-indexing and never gives silently wrong results.
   - Today a sticky-directory failure leaves an emptied output.
   - If you keep the order, a cheap exact pre-check is available: refuse at step (3) when the directory has the sticky bit and neither the index nor the directory is owned by the effective user (root excepted).
3. **htslib without libcurl:** install `hts-nocurl` at a fixed prefix such as `~/.local/opt/htslib-1.24-static`, and point `build.sh` at it. Turn `build_hts.sh` into a tracked script under `test/` or `tools/`.
   - Refuse a libcurl `libhts.a`, with a message that names that script. The library set is part of what was tested.
4. **`<index>.tmp`, then `.tmp1` …, without the pid:** fine. `O_EXCL` prevents clashes, and the length checks at the open happen before the truncate.
5. **The usage message's second line:** acceptable, but I'd move it to the README. It prints on every usage error and runs past 130 columns. If it stays, cut it to one short clause, for example "-W also removes FILE's old .csi/.tbi".
6. **Removing old indexes on every BGZF rewrite without `-W`:** keep it out, as decided. Revisit only as an explicit option.
7. **The slow INFO/END check:** yes, worth its own phase before gVCF users meet it. 13× on chr22, and 419 s on the whole genome, is a performance cliff, not noise.

I changed nothing in the repository. I ran only `bend main.bend -o` into this session's scratchpad, to read the runtime's exit path.
