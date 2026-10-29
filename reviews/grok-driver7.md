# Driver review 7 (memory): Grok 4.7

## Driver review, branch `memory`

Not accepted. Two findings. On Bend 2.0.39 as generated, the heap patch itself is sound, and patched and unpatched binaries match on the edge VCF (default, `-c w`, `-c e`, `--threads 1`, `--threads 4`) and on a short FASTA.

1. **Should fix.** `io64.c:533` (`char buf[IO64_PART]`), reached from `pthread_create` at `io64.c:663` and from the caller at `io64.c:664`. The frame is `sub $0x20078,%rsp` (131192 bytes). A thread created with default attributes gets the soft `RLIMIT_STACK` (2 MiB when that limit is unlimited). Input: `ulimit -s 128` then `fb norm --threads 1 -c w -f test/edge/ref.fa test/edge/sorted.vcf`. Exit 139, stderr empty, stdout 372 bytes (a prefix of the good header). The same command at `ulimit -s 64` dies the same way. `ulimit -s 136` exits 0. Usage alone at 64 and 128 exits 2, so the process can start; the fault is this frame. The fallback runs the same frame on the caller, whose stack is the same limit. Fix: keep the part buffer off the stack. One `static` row per slot, `char io64_fa_buf[IO64_FA_MAX][1 << 17]`, covers the helper and the fallback; a slot is owned until join, and untouched pages stay uncommitted.

2. **Minor.** `build.sh:34–40`. The four anchors match this runtime (`heap_hand` body, the `KEEP` macro, the `n = got ? KEEP(cls) …` line, the `ALC_LEN >= KEEP_WORDS` line). They still accept a generated file that differs only in `#define CAP_WORDS 32768` → `49152`, or in `#define NCLS 8` → `16`, or in a second `#define KEEP(c) (1)` after the real one (`grep -c -x -F` stays 1). With `CAP_WORDS` 49152, `KEEP(15) == 1` while one class-15 block is 32768 words, so the second free hands a two-block chain. `heap_alloc` follows that chain’s links, and the unpatched `heap_hand` banks the same chain one free later. Fix: also require, each exactly once, `#define NCLS      8`, `#define CAP_WORDS 32768`, `#define CHUNK     256`, the `QUANTUM` macro, `KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;`, and a single `#define KEEP(`.

### Open questions

1. The one-block argument holds for this runtime. `KEEP_WORDS` is 32768. In the patched binary the `KEEP(cls) == 1` test is `(1 << 15) >> cls > 1`: classes 0–14 take the old body, class 15 and up take the patch. A fresh block of those classes is one block (`cls >= NCLS`, so `n = 1`, link 0), and one free reaches `KEEP_WORDS`, so the chain pushed is that block, once. It is already unlinked by `heap_free`. `bank_push` and `bank_pop` take `bank_lock`; the link is stored before the unlock. Cold stays 0 because the patch returns before the old body. The bank for class `c >= NCLS` has `2 * (cap >> (c - 7))` entries, two per block that fits. `BANGS` is 0, so `--gpu` still calls `corpus_setup` with the GPU flag false, and `build.sh` compiles host code. No path on this runtime pushes a longer chain, the same block twice, or a block still in use. The checks do not refuse every other runtime: finding 2.

2. At the default here (16384 KiB) and when the limit is unlimited (glibc’s 2 MiB), yes. At 128 KiB, no: finding 1.

3. Acceptable. For a FASTA that is not `P.Fasta.plain`, the comment on `law machine` says the law says nothing. The driver contract for a byte the `.fai` layout does not explain is one stderr line and exit 2 (`MACHINE.bend` around lines 190–198). It does not fix how much stdout is written before that line. A shorter prefix of the good output, the same `error: unsupported FASTA <path>` (or `.fai index does not match`), and exit 2, meets it. A short file (`.fai` promises 100 letters, file cut to 13 bytes) gives that line and exit 2 from both binaries, with the same stdout.

## Follow-up

The patched and unpatched binaries match on every real case in that run: the edge VCF, contigs that cross the 128 KiB part boundary (LF and CRLF, line widths 16, 60, and 70), `--threads 8`, a damaged FASTA (exit 2, `error: unsupported FASTA`, same stdout prefix), bgzip, and a pipe.

The one `DIFF` is the fifo harness. A single `cat` wrote the fifo once. The unpatched process read it and exited 0. The patched process then blocked on the same fifo and was killed (`Terminated`, exit 143). The pipe case already covers stdin. The review stands.
