# Review of driver2 (reviews/DRIVER5_PROMPT.md): ACCEPT

I found no way the new driver does anything other than what the comment above `law machine` says. I have no blocker and nothing that should be fixed. Below are three minor notes (none needs a change), the evidence, and answers to the seven open questions in `notes/speed_driver2.md`.

I wrote nothing in the repository. Everything was built and run under `/tmp/fbr` and `/tmp/fb_rev5`. The two other untracked files, `reviews/gpt-driver5.md` and `reviews/grok-driver5.md`, are not mine.

## Minor notes
1. **minor: an out-of-memory failure can now beat an earlier error.** Place: `main.bend` `starts` and `io64.c:636-649`.
   - **What happens:** a group's later reads get their blocks and start filling before an earlier read's error is reported.
   - **Input:** an Ask whose first read hits a bad FASTA byte, followed by up to 31 reads of about 2^31 letters each.
   - **Old driver:** `error: unsupported FASTA`, exit 2.
   - **New driver:** it may first hit the kernel's OOM killer, or `bend: out of memory` with exit 1.
   - **Scope:** only in that error case. A successful Ask's peak is unchanged, because the old driver also held all of an Ask's answers before `Norm.step`.
   - **Fix, if wanted:** none needed in practice; or cap the bytes started per group.
2. **minor: a full ticket table would report "cannot read".** Place: `io64.c:640` together with `io64.c:654`.
   - A full table hands out ticket 32, and its wait then fails with EINVAL, which prints the misleading `cannot read <ref>`.
   - This cannot happen (see question 2), so I have no triggering input.
   - **Fix, optional:** `err_fail` there, so a broken invariant can't pass as an I/O error.
3. **minor: the heap-full fallbacks are dead code on CPU builds.** Place: `io64_block` at `io64.c:68-72`.
   - `err_seen` is `DEVICE && …`, and on the host a full heap means `err_fail` then `_exit(1)`.
   - So the ring's "heap gave no block, read the piece yourself" path and ENOMEM at a read's wait never run on CPU builds.
   - The reasoning about them is sound, but no test can exercise them. The header comment (`io64.c:17-20`) already says the full-heap part.

## Evidence (new driver against the old one built from the `parallel` branch; stdout, stderr and exit code compared)
- **Damaged inputs:** 264 identical comparisons at each piece size (300, 1000 and 3,670,016 bytes), under `-c w` and `-c e`, read as a file, through a pipe and through a FIFO.
  - FASTA: 11 variants (space, CR, tab or LF in the wrong place; cut short; cut short plus a bad byte; several bad bytes).
  - VCF: plain, BGZF, and BGZF damaged 8 ways (cut mid-block, cut at a block boundary, no end marker, wrong CRC, damaged deflate data, wrong ISIZE, wrong BSIZE, concatenated), plus a plain gzip file.
- **Long input:** a 61 MB, 647,724-record VCF on 112 contigs, which is about 17 pieces at the normal size, so the 16-slot ring fills. Variants: plain, BGZF, CRC damaged, cut short, a late REF mismatch, a late bad FASTA byte. 48 identical comparisons at the normal size and 48 at 1000 bytes.
- **Error order:** in the 300-byte build, one group held 5 reads of a cut-short contig (code 2, ".fai index does not match") followed by 6 reads with a bad byte (code 1, "unsupported FASTA"). The first in order is reported, the same as the old driver, at all three sizes.
- **Thread races:** none reported by ThreadSanitizer on the 300-byte and normal builds, including the long and BGZF inputs with the ring full. The only report was "thread leak": FASTA read threads left unjoined on the error-exit path, which is expected because the process exits.
- **Memory errors:** none reported by AddressSanitizer or the undefined-behaviour sanitizer.
- **Fault injection:**
  - Every 1st, 2nd, 3rd or 7th thread creation for the FASTA reads and the read-ahead made to fail: all outputs identical to the old driver.
  - The n-th 1 MiB read buffer allocation made to fail: `error: out of memory`, exit 2.
- **Build paths:** the one-step `bend main.bend -o` build matches `./build.sh` everywhere except a BGZF VCF, which gives `error: no BGZF in this build <path>`.
- **Early stop with the pipe kept open** (`(cat v; sleep) | fb -c e … /dev/stdin`): with the error in the first piece, both drivers exit at once with exit 1 and identical output. With a late error, both stall at the same place (3.35 MB of output). That is because the machine needs the batch's last piece, which ends only when the stream does; it is not a driver regression.

## Answers to the open questions
1. **Helper threads writing heap blocks.** Yes, that is enough. I read Bend's runtime C source, embedded in `~/.bend/bin/bend`:
   - The heap only grows in place: `corpus_grow` maps the range right after it and moves only the free-list banks, never the pages. There is no garbage collection or compaction.
   - Effects run on the event-loop thread, with its own allocation lane.
   - The free-list link is written into a block only when it is freed, and the code frees a block only after its helper is joined or after the block is handed out.
   - Memory visibility: the mutex covers the ring (the helper's writes are visible to the main thread once it locks and sees the slot full), and `pthread_join` covers the FASTA reads.
2. **The ticket invariant.** There is no path that starts a 33rd read. Each `answers` call waits for every ticket it started before it returns, and the next Ask starts only after that. Only `die` leaves tickets pending, and it exits.
3. **Error order.** The argument holds on the code. `waits` goes through the reads in Ask order, and a read's errno, its layout code and `PBig` are all decided at its wait. Groups run one after another. It is confirmed by the mixed code-1/code-2 test above.
4. **The read-ahead ring.** I checked ti ≤ fi ≤ ai ≤ ti+16:
   - The helper fills only slots waiting for data, and in order.
   - The `ai == ti` fallback happens only while the helper is idle, so no piece is lost or handed out twice.
   - On a stream switch, a slot that was mid-read when the stop came ends up full and counts as left over, giving EBUSY.
   - In this driver the switch happens only after the `.fai`'s helper has already ended.
5. **A pipe or FIFO.** Fine. No exit path joins the helper. `IO.exit` is `fflush(stdout)` then `exit`, and the runtime registers no exit handlers, so a helper blocked in `read` is simply killed. A writer that never closes behaves exactly as it did with the old driver. The only difference: up to 16 pieces of stdin (about 56 MB) are consumed instead of 1.
6. **Memory.** Acceptable as measured; it is a performance choice.
7. **The out-of-memory message.** The wording is unchanged. A full heap on a CPU build is still `bend: out of memory`, exit 1. A failed read buffer is still `error: out of memory`, exit 2, in its place. The ordering caveat is note 1 above.
