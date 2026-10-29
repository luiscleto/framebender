The bug, the reproduction, and the patch all hold. `strand.c` matches a fresh `bend strand.bend -o` from Bend 2.0.39, and every run printed `4200`, which is `300 * (7 + 7)`. Four wording fixes before posting. Nothing else needs to be cut.

## Findings

### 1. The short "Why" says a parked block is reused only after another free, and that fresh memory keeps being taken

The plain paragraph says the freeing thread can reuse a parked block "only once it frees another block of the same size," and that the allocating thread "keeps taking new memory, which is never given back."

A parked block is `ALC_COLD`. The same thread takes it on its next allocation of that class, with no second free. `heap_alloc` misses on an empty hot list and `heap_alloc_miss` returns `ALC_COLD` first (`strand.c` lines 716–725, then 745–752). A second free does something else: `heap_hand` pushes the old `ALC_COLD` onto the shared bank, which any thread can pop, and parks the new block (lines 701–708).

Fresh memory is also bounded. Each free of class 15 or above hands the list over immediately (`heap_free`, lines 767–768). Steady state is one parked block per thread and size class, not one block per free. 300 rounds times two 16 MiB arrays is 9600 MiB if nothing were reused. Peak RSS stayed near 100 MB.

Unpatched peak was 101 MB and 115 MB at 16 threads, and 34 MB and 36 MB at 1 thread. One extra sweep of the unpatched binary: 2 threads 36 MB, 4 threads 52 MB, 8 threads 68 MB, 32 threads 182 MB.

Replacement for the "In short" paragraph:

> In short: when a thread frees a block of 256 KiB or more, the runtime parks it on that thread. That thread reuses it the next time it allocates the same size. No other thread can take it while it is parked. If the thread frees a second block of the same size first, the parked one moves to a shared pile that any thread can use, and the new block is parked instead. So the extra memory stops at one block per thread and size. The thread that only allocates never sees the parked blocks, and the pages for those blocks stay in the process until it exits.

### 2. `KEEP(c) = KEEP_WORDS >> c` is wrong for the 16 MiB blocks in the repro

The detailed paragraph says classes of 256 KiB and up keep at most one block because `KEEP(c) = KEEP_WORDS >> c`, with `KEEP_WORDS = 32768`. The macro is `KEEP_WORDS >> c` only when that is non-zero; otherwise it is 1 (`strand.c` line 695).

The 256 KiB threshold is right. `KEEP_WORDS` is 32768 on the CPU (lines 228 and 2446). Class 15 is `2^15 * 8 = 256 KiB`, and `32768 >> 15` is 1. Class 14 is 128 KiB and `KEEP` is 2.

The repro is class 21, not class 15. `go(300, 22)` builds a `BUF` of `2^22` `U32`s, and a `BUF` of logical class `c` is heap class `c - 1` (lines 879–881, 1028–1029, 1133–1150, 1505–1510). That is `2^21 * 8 = 16 MiB`. `32768 >> 21` is 0, and the macro returns 1. A maintainer who applies the formula as written to these arrays gets 0.

The rest of that paragraph matches the code. "Up to one block per worker thread and size class" is the right bound. This program only parks a few of them.

Replacement for the "In more detail" paragraph:

> In more detail: `heap_free` puts a freed block on the freeing thread's list for its size class. Classes of 256 KiB and up keep at most one block. `KEEP(c)` is `KEEP_WORDS >> c`, or 1 when that shift is 0, and `KEEP_WORDS` is 32768 on the CPU. Class 15 is the 256 KiB block, and `32768 >> 15` is 1. Larger classes hit the 0 case and still keep one. The 16 MiB arrays in this program are class 21. `heap_free` calls `heap_hand` once the list holds `KEEP_WORDS` words, and one of these blocks is already that long, so the first free hands it over. `heap_hand` moves the previously parked block to the shared bank and parks the new one. `heap_alloc_miss` uses this thread's parked block, then the bank, then fresh memory. It does not see another thread's parked block, so at most one block per worker and size class stays stuck.

### 3. The table's exact ranges did not reproduce

The effect is real. The printed ranges are tighter, and a few megabytes higher on the small numbers, than a repeat here (x86-64, 32 hardware threads). Built with the stated `clang -std=c11 -O3` line. Measured with `nice -n 19 timeout 300 python3 rss.py`, which pins `taskset -c 0-15`, two runs each. Every run printed `4200` and exited 0.

| build | 16 threads | 1 thread |
|---|---|---|
| as generated | 115 MB, then 101 MB | 34 MB, then 36 MB |
| patched | 37 MB, then 37 MB | 36 MB, then 36 MB |

The posted table says 92–108 MB and 40 MB unpatched, and 44 MB and 40 MB patched. Same shape, different digits. The 16-thread unpatched figure moves by more than that posted window.

Replacement for the "Peak memory…" sentence and the table:

> Peak memory (from `getrusage`, Bend 2.0.39, x86-64 with 32 hardware threads) is about 40 MB on one thread, with or without the change. On 16 threads it is about 100 MB as generated, and about 40 MB with the change. The 16-thread number moves by a few tens of megabytes from run to run.

### 4. The real-program sentence states the run time as a fact

This paragraph cannot be checked from the files here. "About 85 MB of a 600 MB peak" is properly limited to that one program. "With no change in run time" is stronger than an unchecked personal run can support, and "the stuck blocks were about 85 MB" states a label that was not measured directly.

Replacement:

> In my real program (a VCF normalizer that allocates 2 to 32 MiB buffers on the main thread and frees them in 16 parallel tasks), about 85 MB of a 600 MB peak went away with the change below. My build script applies that change to the generated C before compiling it. The run time looked the same.

## Checked, and left as written

On more than one thread, `FID_go` allocates both arrays on the thread running `go`, then builds two `FID_use` tasks (lines 1371–1392). Each `use` reads one word and drops the array (lines 1345–1356 and 1283). With `--threads 1`, alloc and free share one thread (line 2470), so the parked block is reused.

The patch is safe. `strand_p.c` adds only the early return at the top of `heap_hand`. For `KEEP(cls) == 1` the hot list holds exactly one block, the just-freed one, whose next word is 0, so `bank_push` publishes one block and not a chain. The early return clears the hot list and does not write `ALC_COLD`. `ALC_COLD` starts at 0 and nothing else sets it, so the block is not also left parked and a null head is not pushed. The block is already unreferenced. Other threads use their own `ALC` row. The bank is locked (lines 657–682). Patched runs still print `4200`, and the 16-thread peak falls to the 1-thread level.

The draft is already first person, with no "we", no generator footer, and no links to private files.

## Verdict

**ACCEPT with the listed changes.**
