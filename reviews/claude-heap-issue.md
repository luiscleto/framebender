# Review of the heap-stranding bug report (data/tmp/heapissue/ISSUE.md)

## Context
The owner plans to post ISSUE.md to github.com/bendlang/bend. The brief (reviews/HEAP_ISSUE_PROMPT.md) asks for (A) an accuracy check against the generated C (strand.c, Bend 2.0.39) plus a reproduction of the table, and (B) a writing check against the owner's rules for public posts. Nothing was edited or posted. The only files written were the two binaries in my scratchpad.

## What I verified (no change needed)
- **Cause, detailed paragraph.** `heap_free` (strand.c:755–770) pushes the block onto the freeing thread's chain and calls `heap_hand` once `ALC_LEN >= KEEP_WORDS`. `heap_hand` (701–708) banks the old `ALC_COLD` and parks the chain as the new COLD. `heap_alloc_miss` (716–743) tries only its own COLD, then `bank_pop`, then fresh pages. This matches the report.
- **Threshold.** On the CPU `KEEP_WORDS = CAP_WORDS = 32768` words (2446, 228). `KEEP(c) == 1` holds exactly for c ≥ 15, and 2^15 words × 8 B = 256 KiB. Correct.
- **"Up to one block per worker thread and size class."** Correct for c ≥ 15: COLD holds one block and the chain is empty after every free. Each pool thread has its own row (`ALC[w]`, 1926). The main/IO thread uses `ALC[0]` (1983), which is also a worker, so "per worker thread" is exact.
- **The fix is safe.** For KEEP==1 classes the chain is always empty before a free. A fresh allocation has n = 1 (KEEP==1 implies cls ≥ NCLS = 8, so line 726 gives n = 1, and line 737 writes next = 0). Banked entries are single blocks with next = 0, so `ALC_AT = H[got] = 0` and `ALC_LEN = 0` (740–741). So the list being handed is exactly the block just freed (`e.mem[loc] = 0`). That means one block per push, pushed once, and it is no longer referenced by the thread (AT/LEN are zeroed). `bank_push` takes `bank_lock` (674–682). ALC rows are per thread. Bank entries stay single blocks, which is what `heap_alloc_miss` expects (`n = KEEP(cls) = 1`). COLD stays 0 for these classes, so the COLD path simply goes unused. Bank capacity is not a concern: it is 2× the number of blocks of that class that fit in the heap (2424). No race and no double push.
- **The reproduction does what the text says.** `Array.new(U32, 22, 7)` compiles to `blk_new(e, 0, d, 0, …)` (1296), which is a BUF of 2^22 u32 in word class `blk_wcls(false, 22) = 21`, so 2^21 words = 16 MiB exactly (1133–1150, 879). The generated `go` (1361–1405) builds both arrays on the current thread, forks `use(a)` and `use(b)` as two tasks, and continues to `go(m)` only in the join (`go_j4`). So the arrays are freed in their own tasks, one round at a time, 300 rounds. Output was 4200 = 300 × 14 in every run.
- **Writing rules.** The report uses first person throughout, has no AI footer, and points to no other issues or private files.

## Measurements (peak RSS via rss.py, `nice -n 19 timeout 300`, taskset 0-15, clang -O3; memory only)
| build | 16 threads (13 runs) | 1 thread (3 runs) |
|---|---|---|
| strand.c | 60, 72, 73, 75, 91, 91, 92, 107, 107, 107, 121, 123, 123 | 40 ×3 |
| strand_p.c | 44 ×13 | 40 ×3 |

The unpatched peaks are 44 plus a whole number (1–5) of 16 MiB blocks (+16, +31, +47, +63, +79). This is direct evidence that whole stuck arrays are the cause. rss.py prints `ru_maxrss/1024`, so the unit is MiB, not MB.

## Findings

1. **Table range is too narrow.** "92–108 MB" comes from two runs. Over 13 runs I got 60–123. Replace the table and its lead-in with:
   > Peak memory (from `getrusage`, in MiB, ten runs each, Bend 2.0.39, x86-64 with 32 hardware threads):
   >
   > | build | 16 threads | 1 thread |
   > |---|---|---|
   > | as generated | 60–123 (varies from run to run) | 40 |
   > | with the change below | 44 | 40 |
   >
   > Every value above 44 is 44 plus a whole number of 16 MiB arrays (1 to 5 in my runs).

   (Use the owner's own ten runs if they rerun. The last sentence still holds.)

2. **The short "Why" paragraph overstates and confuses.** "Only that thread can reuse it, and only once it frees another block of the same size" is wrong as written. The freeing thread can reuse its kept block on its very next allocation of that size. *Other* threads can reuse it only after the freeing thread frees another one (which banks it). "The thread that allocates never sees those blocks" and "keeps taking new memory, which is never given back" are also overstated. The allocator does get every block back except each thread's latest one, so the extra memory is bounded (1–5 blocks here), not growing. Also, the heap never returns memory to the OS with or without the fix (the only `munmap`, at 2398, is for a failed mapping attempt). Replace with:
   > In short: when a thread frees a large block (256 KiB or more), the runtime keeps the most recent one for that thread. Other threads can only get it after that thread frees another block of the same size. If it never does, and never allocates that size itself, the block sits unused, and the thread that allocates takes fresh memory instead. So with N threads, up to N large blocks of each size can sit unused.

3. **The KEEP formula is quoted without its floor.** The code is `KEEP(c) (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)` (695). As quoted, the formula gives 0 for c ≥ 16. The unit (8-byte words) is also missing. Replace the parenthesis with:
   > (`KEEP(c)` is `KEEP_WORDS >> c`, but at least 1; on the CPU `KEEP_WORDS` is 32768 words, so it is 1 from class 15, 2^15 words = 256 KiB, up)

4. **Name the kept block, and say why only large classes matter.** Maintainers will look for `ALC_COLD`. Smaller classes also hold freed blocks per thread, but at most about 2 × KEEP_WORDS (512 KiB) per thread and class (a COLD generation plus a partial chain). Large classes hold one whole block of any size. That is the reason the fix only touches KEEP==1. In the detailed paragraph, replace "It moves the thread's previously kept block to the shared bank and keeps the new one." with:
   > It moves the thread's previously kept block (`ALC_COLD`) to the shared bank and keeps the new one there.

   and replace the last sentence with:
   > So each thread can hold one freed block per large size class that no other thread can use. Smaller classes also keep blocks per thread, but at most about 512 KiB per thread and class, so only large blocks add up.

5. **The fix paragraph should say why it is safe and note the GPU case.** On a GPU run the host sets `KEEP_WORDS = CHUNK = 256` (2446), so `KEEP(cls) == 1` covers classes of 2 KiB and up there. This is still safe, but it means more `bank_lock` traffic. Replace "For these size classes, the block being handed over is exactly the one just freed, so this sends it straight to the shared bank, where any thread can reuse it." with:
   > For these size classes the thread's list is always empty before a free, so the list being handed over is exactly the block just freed, and bank entries stay single blocks as `heap_alloc_miss` expects. This sends it straight to the shared bank, where any thread can reuse it, at the cost of one `bank_lock` per large free. (On a GPU run `KEEP_WORDS` is 256, so there this covers blocks of 2 KiB and up.)

6. **The repro's comments are inaccurate.** "An array of 2^d words" is wrong: it is 2^d U32 values packed two per word, so 2^(d−1) words (16 MiB for d = 22). "Only a few arrays exist at any moment" can be made exact, because the next round starts only after both tasks return. Replacements:
   > `# An array of 2^d U32 values, all set to 7 (16 MiB for d = 22).`

   > `strand.bend` creates two 16 MiB arrays on one thread, frees each one in its own parallel task, and repeats this 300 times. At most two arrays exist at any moment.

7. **The "real program" paragraph claims more than a before/after measurement shows.** "The stuck blocks were about 85 MB" attributes the drop to stuck blocks. What was measured is presumably the peak with and without the change. "No change in run time" is also absolute. The build-script sentence is not needed by a maintainer. Replace the paragraph with:
   > In my real program (a VCF normalizer that allocates 2 to 32 MiB buffers on the main thread and frees them in 16 parallel tasks), applying the change below to the generated C lowered peak memory by about 85 MB, from about 600 MB, with no measurable change in run time.

   (If the 600 MB peak was in MiB like the table, say MiB.)

8. **Minor (optional).** The alternative-fix sentence could note that the second option touches another thread's unsynchronized `ALC_COLD`: "…or let a thread that runs out take a block another thread kept (this would need locking on the kept blocks)." The title is accurate; keep it.

## Verdict
**ACCEPT with the listed changes.** The cause, threshold, per-thread bound and fix are all correct, and the fix is safe. The reproduction holds, with a wider spread than reported. Findings 1–3 and 6–7 fix overstatements and inaccuracies. Findings 4–5 add one line each that a runtime maintainer would otherwise have to work out. Finding 8 is optional.
