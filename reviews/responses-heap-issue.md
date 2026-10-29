# Review of the upstream bug report on heap stranding: responses

Reviewers: Claude (`claude-heap-issue.md`), GPT 6.1 Sol (`gpt-heap-issue.md`), Grok 4.7
(`grok-heap-issue.md`); prompt `HEAP_ISSUE_PROMPT.md`. All three: ACCEPT with changes. All three
confirmed the cause, the 256 KiB threshold, the one-block-per-thread-and-class bound, that the
reproduction does what it says, and that the patch is safe (one block per push, pushed once,
bank locked, `ALC_COLD` never set for these classes).

| # | finding | by | response |
|---|---|---|---|
| 1 | The short "Why" was wrong: the freeing thread reuses its kept block on its own next allocation; only other threads wait for a second free. "Never sees" / "keeps taking memory" overstated a bounded effect | all three | **Fixed:** paragraph rewritten. |
| 2 | `KEEP(c) = KEEP_WORDS >> c` quoted without its floor of 1 (gives 0 for the repro's class 21); unit of `KEEP_WORDS` missing | all three | **Fixed.** |
| 3 | The table's ranges did not reproduce (Claude 60–123 over 13 runs, GPT 85–100, Grok 101–115); unit is MiB (`ru_maxrss/1024`); Claude: every extra is a whole number of 16 MiB arrays; Grok: a thread sweep | all three | **Fixed:** re-measured, six runs at 1/4/8/16/32 threads, in MiB, with the 16 MiB steps noted. |
| 4 | The real-program paragraph attributed the 85 MB to stuck blocks and stated run time absolutely | all three | **Fixed:** "lowered peak memory by about 85 MiB ... I saw no change in run time." The build-script sentence dropped (GPT, Claude). |
| 5 | Name `ALC_COLD`; say why only large classes matter (smaller ones hold at most about 512 KiB per thread and class) | Claude | **Fixed.** |
| 6 | The fix paragraph: say why it is safe, the `bank_lock` cost, and the GPU case (`KEEP_WORDS` 256 there) | Claude | **Fixed.** |
| 7 | Repro comment: 2^d U32 values, not words; "at most two arrays" is exact | Claude | **Fixed.** |
| 8 | Drop or qualify the speculative alternative fixes | GPT (drop), Claude (note locking) | **Dropped.** |
| 9 | "On the same thread" is not fixed across rounds | GPT | Kept "on one thread": within a round both arrays are made on one thread, which is what the report needs. |

**Not posted.** A search before posting found bendlang/bend#1856 (closed 2026-10-26), the same
bug found in another program, fixed by PR #1869 (merged 2026-10-26, after 2.0.39): `heap_hand`
banks blocks of at least `CAP_WORDS` (256 KiB) at once, so the GPU's smaller `KEEP_WORDS` doesn't
widen the cutoff (Claude's item 6 had flagged that case). The earlier duplicate check missed it by
looking at open issues only. Once a release carries the fix, `build.sh`'s patch and guard can go.
