1. **The short cause is misleading, and the detailed formula omits the minimum of one.** In [strand.c](/home/luisc/Work/bend-projects/framebender/data/tmp/heapissue/strand.c:716), an allocation miss immediately consumes the freeing thread’s kept block; another free is unnecessary. A subsequent free instead publishes the *previously* kept block. Thus “never sees” and “keeps taking new memory” overstate a bounded retention problem. The 256 KiB threshold and one-block-per-thread-per-large-class bound are correct: classes 15–31 contain `2^c` eight-byte words, and `KEEP(c)` clamps to one.

   Replace both “Why” explanation paragraphs with:

   > When a thread frees a block of 256 KiB or more, the CPU runtime keeps it privately for that thread. Other threads cannot reuse it until that thread frees another block of the same size. If it does neither, one block per thread and size class can remain unavailable to other threads, increasing peak memory.
   >
   > `heap_free` adds the block to the freeing thread’s list. Once the list reaches `KEEP_WORDS` (32768 eight-byte words on the CPU), `heap_hand` parks it in `ALC_COLD` and moves the previous parked list to the shared bank. `KEEP(c)` is `KEEP_WORDS >> c`, clamped to at least one, so classes of 256 KiB and up park one block. Allocation checks the thread’s active list, then its parked list, then the bank before taking fresh memory.

2. **The reproduction is accurate; “on one thread” can be made more precise.** [The generated allocation and fork code](/home/luisc/Work/bend-projects/framebender/data/tmp/heapissue/strand.c:1361) creates both arrays before making two `use` tasks. Each contains `2^22` four-byte values: 16 MiB. Both tasks free their arrays before the next round starts; `main` requests 300 rounds. The allocating thread need not be the same across rounds.

   Replace the description with:

   > Each of 300 rounds creates two 16 MiB arrays on the same thread, then frees each in a separate parallel task before starting the next round.

3. **The proposed patch is safe for this CPU runtime; its explanation can be shorter.** [The patch](/home/luisc/Work/bend-projects/framebender/data/tmp/heapissue/strand_p.c:701) starts with empty state and never populates `ALC_COLD` for these classes. Fresh allocations and bank entries contain exactly one block because `cls >= 15 > NCLS`. Each free therefore publishes one already-freed block with a null next link. It cannot publish a longer chain or publish the block twice. Bank operations share an acquire/release lock; after publication, the freeing thread only clears its private allocator fields, so another thread may safely allocate immediately.

   Keep the C snippet unchanged. Replace the final paragraph, including the speculative alternatives, with:

   > For these size classes, each free hands over exactly one block. This sends it directly to the shared bank, where any thread can reuse it. Smaller classes keep their existing behavior.

4. **The table’s units should be MiB.** `rss.py:5` divides Linux’s KiB measurement by 1024. I built both files with the specified flags and ran two measurements per configuration under `nice -n 19 timeout 300`, pinned to CPUs 0–15:

   | Build | 16 threads | 1 thread |
   |---|---:|---:|
   | Generated | 100, 85 MiB | 36, 36 MiB |
   | Patched | 37, 37 MiB | 36, 36 MiB |

   Every run returned `4200`, exit status zero. This reproduces the effect, though not the exact reported values. Keep your original measurements; replace the table introduction with:

   > Peak RSS in MiB (`getrusage`, two runs each, Bend 2.0.39, x86-64 with 32 hardware threads; runs pinned to CPUs 0–15):

5. **The real-program paragraph states attribution and performance too absolutely.** Those measurements cannot be checked here; “removed the stuck blocks” claims more than a peak-memory comparison establishes. Replace it with:

   > In my VCF normalizer, which allocates 2 to 32 MiB buffers on the main thread and frees them in 16 parallel tasks, this change reduced peak memory by about 85 MB from roughly 600 MB. I observed no change in run time.

   The post otherwise meets the writing requirements: first person, self-contained, and no AI footer.

**Verdict: ACCEPT with the listed changes.**
