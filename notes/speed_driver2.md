# Driver, phase E step 4: parallel reference reads, VCF read further ahead

Brief: `notes/briefs/PARALLEL.md`, step 4; the lead's message of 2026-10-28 (trusted code only:
`main.bend`, `io64.c`, `io64.js`, `build.sh`; no change to the contract or a proof file). Branch
`parallel`, on 26b6f92. Nothing committed.

## What changed, and why

After phase E step 3 the machine runs a batch of 16 pieces in parallel, but the driver still did
everything one at a time: it read the 16 pieces one after another (one piece read ahead), and
answered the batch's reference reads (up to 32 per Ask) one after another. Timed in the generated C
(`patch.py`'s timers), pinned, to /dev/null, 1.82-1.89 s wall: FASTA reads 0.67-0.73 s, waiting for
VCF pieces 0.35-0.37 s, the machine 0.76-0.78 s.

1. **Reference reads in parallel** (`main.bend`'s `answers`, `io64.c`'s `Io.fa_start` /
   `Io.fa_wait`; `Io.fa_read` is gone):
   - `answers` takes an Ask's reads in groups of at most 32. For each group it first starts every
     read (`starts`: an unknown contig, an empty span and a read too large need no read; the
     others `Io.fa_start`, which takes `Io.fa_read`'s arguments, allocates the read's block on the
     calling thread, and starts a helper thread that fills it), then takes the answers in order
     (`waits`: `Io.fa_wait` joins the read's thread and answers exactly what `Io.fa_read` did;
     `answer.k` checks it as before). A later group starts only once every earlier read was taken.
   - So the answers are the same and in order, and the error reported is the first one in order:
     a failed read stops the driver when its turn comes; "FASTA read too large" (`PBig`) too, in
     its place. Reads started after it (side-effect free) are dropped when the driver exits.
   - `io64.c`: the read itself (`io64_fa_do`) is the old loop unchanged, moved into a function
     that touches no heap (it runs on a helper thread); a ticket table of 32 slots (`io64_fa`). A
     read whose block cannot be allocated fails with ENOMEM at its wait; one whose thread cannot be
     created is done at once in `Io.fa_start`. A ticket that is not pending fails with EINVAL
     (never happens: at most 32 are started before they are waited for).
   - The read's bounce buffer is now 1 MiB (`IO64_PART`, was 16 MiB): with 16-32 reads at once,
     16 MiB each was 0.5 GB of fresh pages to fault in and zero per batch (measured: 1.38 → 1.31 s).
     The parts only cut the span; the column count goes on across them as before.
2. **VCF pieces read further ahead** (`io64.c`'s `Io.read_block`): the single read-ahead slot is
   now a ring of up to 16 (`IO64_AHEAD`), filled in order by the same single helper thread through
   its duplicate descriptor:
   - the calling thread allocates the blocks (and frees them), hands out one piece per call, in
     order, and gives the freed slots new blocks; the helper fills the next slot it has a block for,
     and stops after a piece that is short (the stream's end) or failed;
   - a piece's error is kept with it and reported when that piece is asked for, as before;
   - if the heap gives no block, the queue is empty: the call ends the helper (nothing past the
     pieces handed out was read) and reads the piece itself, as the old code did;
   - switching to another file stops the helper and fails with EBUSY if a piece read ahead holds
     bytes (as before: only an empty end may be left); a call with another `max` fails with EINVAL
     (as before).
3. Comments: `main.bend`'s header says both; `io64.c`'s says what each effect does now.

No change to `MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`, `norm*.bend` or any proof file.
`build.sh` is unchanged.

## Measured

Whole genome (4,048,342 records, `-c w`), `data/tmp/parallel/bench2.sh` (bench4's protocol:
`nice -n 19`, interleaved, inputs in the page cache, nothing else running; 3 rounds, unpinned to
/dev/null 2): cur = the current build (`fb_final`, 26b6f92), new = this driver (`fb_d4`).

| input, output | pinned 0-15: cur / new / bcftools | unpinned: cur / new / bcftools |
|---|---|---|
| plain, file | 2.45-2.59 / **1.82-1.86** / 7.82-7.88 s | 3.33-3.42 / 2.11-2.19 / 7.85-7.93 s |
| `.vcf.gz`, file | 2.76-2.79 / **1.83-1.86** / 7.98-8.26 s | 3.94-4.19 / 2.21-2.29 / 7.97-8.13 s |
| plain, /dev/null | 1.83-1.87 / **1.31-1.32** / 5.50-5.80 s | 2.55-2.67 / 1.35 / 5.81-5.86 s |
| `.vcf.gz`, /dev/null | 2.16-2.19 / **1.33-1.34** / 5.81-5.94 s | 3.57-3.65 / 1.35-1.39 / 5.85-5.97 s |

To a file, pinned: 4.3x bcftools on the plain file (was 3.2x), 4.4x on the `.vcf.gz` (was 2.9x);
unpinned 3.6x. chr22 (pinned, /dev/null, 5 rounds): cur 0.056-0.059, new 0.051-0.055, bcftools
0.075-0.078 s. Peak memory (whole genome): plain 606 → 628 MB, `.vcf.gz` 567 → 665 MB.

Where the time goes now (timers in the generated C, pinned, /dev/null, 1.34 s wall with the 16 MiB
parts): FASTA waits 0.36-0.38 s (one batch's slowest window at a time), VCF waits 0.03 s (was
0.35), starting reads 0.02 s, the machine 0.92 s.

Each step: parallel reads alone 1.86 → 1.55 s; with the read-ahead ring 1.38 s; with 1 MiB parts
1.31 s (pinned, /dev/null).

## Checks

Builds: normal, and `piece()` 70,001, 1,000 and 300 (the source restored after each).
- The gate, through `test/bcheck.sh`: `PROOF.bend --check-only` and `--verdict` ALL PROOFS CHECK;
  `examples.bend` 15 TODOs, `MACHINE.bend` 15 TODOs (as before); `main.bend` 75 defs rely on
  unsafe or foreign code (62 before: the new driver functions; the gate only asks for the message).
- `test/same.sh` 128/128 and `test/par.sh` 312/312 on all four builds.
- Whole genome `-c w` and `-c e`, plain and `.vcf.gz` (same relative path): stdout, stderr and
  exit code identical to the current build.
- `test/compare.sh`: chr22 0, scr 0, `test/edge/sorted.vcf` 1 (the `<DEL>` record, as before),
  whole genome 0, whole genome from `.vcf.gz` 0.
- `data/tmp/speed/gztest.sh` on the four builds: ALL IDENTICAL (1,008 comparisons).
  `data/tmp/speed/eoftest.sh`: as expected on the normal, 70,001 and 1,000 builds; on the 300 build
  the same 8 lines as the current build's 300 build (`edge_in`, `edge_in2` under `-c e` stop at
  line 10 before the missing end block is read; known, notes/parallel.md).
- A pipe (`cat | ... /dev/stdin`) and a named FIFO (`data/tmp/parallel/fifotest.sh`): chr22, scr
  and `snp_sorted` under `-c w`/`-c e` on the normal, 1,000 and 300 builds (36 comparisons), and
  the whole genome plain and `.vcf.gz` through both: identical to the current build.
- FASTA errors in the middle of the run (chr22 with a space or a CR in place of a letter at 30 or
  45 MB, the FASTA cut at 40 MB, and both a CR at 30 MB and the cut at 40 MB), normal, 70,001 and
  1,000 builds, `-c w`/`-c e`: stdout, stderr and exit code identical to the current build (the
  earlier error wins in the combined file).

## Open questions for the reviewers

1. **Threads writing heap blocks.** Both helpers write into Bend heap blocks through raw pointers
   while the calling thread runs the machine (the old read-ahead did this for one block). The blocks
   are allocated before and freed after, on the calling thread, and no term refers to a block until
   it is handed out. Is that enough for Bend's runtime (no moving or compacting of the heap, no
   allocator state shared with those pointers)?
2. **The ticket invariant.** `Io.fa_start` fails at the wait (EINVAL, so "cannot read") when all 32
   slots are pending. `answers` starts at most 32 before waiting for each; a die in `waits` leaves
   the rest pending, but the driver then exits. Is there a path that starts a 33rd read before a
   wait (for example two Asks in a row without their waits)?
3. **Error order.** The first failing read in Ask order is reported, whatever the threads finish
   first. A read's errno, its layout code (1 or 2) and "FASTA read too large" are all decided at its
   wait, in order. The combined-error test may not have put both errors in one Ask at every piece
   size; please check the order argument on the code.
4. **The read-ahead ring.** The conditions in `io64_ahead_take` (wait while the head slot is not
   full, there is a slot queued, and the helper has not stopped with nothing more filled) and in
   `io64_ahead_run`. In particular, the fallback when the heap gave no block (empty queue: the
   helper is ended and the call reads itself): can data read by the helper be lost, or a piece be
   handed out twice or out of order? And the stop on a stream switch while the helper is in a read
   (it finishes that read; the piece is then counted as left, EBUSY).
5. **A pipe or FIFO.** The helper reads up to 16 pieces past what the machine has taken. A run that
   stops early (an error, `-c e`) exits with the helper possibly blocked in `read`. Fine on exit;
   anything else to consider (a writer that never closes)?
6. **Memory.** Up to 16 more 4 MiB blocks read ahead and up to 32 bounce buffers of 1 MiB:
   measured +22 MB (plain) and +98 MB (`.vcf.gz`) at peak. Acceptable, or a smaller ring?
7. **The out-of-memory message.** A read's block that the heap cannot give fails with ENOMEM at its
   wait ("out of memory"), as before; on a CPU build the runtime stops first ("bend: out of
   memory"). Unchanged in substance; worth a look at the order (the read is no longer the first
   thing to fail when several are started).

## Scratch (`data/tmp/parallel`, ignored)

`fb_d4`, `fb_d4_{70001,1000,300}` (this driver), `fb_final*` (the current build), `bench2.sh`,
`fifotest.sh`, `faerr/` (the damaged FASTAs), `patch2.py` (timers for the new effects),
`io64.c.before`, `main.bend.before`, `gzsuite.out`.
