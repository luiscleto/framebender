# Driver review 7 (memory: runtime patch, read buffers): responses

Reviewers: Claude (`claude-driver7.md`: ACCEPT once item 1 is fixed), GPT 6.1 Sol
(`gpt-driver7.md`: two should-fix), Grok 4.7 (`grok-driver7.md`: one should-fix, one minor).
Prompt: `DRIVER7_PROMPT.md`. All three agree on the notes' three questions: the patch's one-block
argument holds on Bend 2.0.39's runtime (bank lock, bank capacity, no chain of two blocks); the
stack is enough at normal limits only; a damaged FASTA met at a different read (a shorter prefix
of the good output, the same error line and exit code 2) is acceptable under law machine's
comment.

| # | finding | by | response |
|---|---|---|---|
| 1 | The 128 KiB part buffer on the reading thread's stack (`io64.c`, `io64_fa_do`): under a small `ulimit -s` (64 or 128) the run dies with SIGSEGV (exit 139, a prefix of stdout), and the fallback on the calling thread does the same; Claude: below the guard page it can write into another thread's stack, so wrong letters with exit 0 are possible | all three (GPT, Grok reproduced it) | **Fixed:** one static buffer per read slot, `io64_fa_buf[IO64_FA_MAX][IO64_PART]` (Claude's and Grok's fix): no allocation and no stack, the same for the helper and the fallback, a slot owned by one read until `Io.fa_wait` joins it; untouched pages stay uncommitted. |
| 2 | `build.sh`'s checks accept runtimes the patch was not written for: `CAP_WORDS` 49152 (then `KEEP(15) == 1` with two blocks per keep, a two-block chain), `NCLS`, `QUANTUM`, a second `#define KEEP(`, a second `heap_hand` spelled differently or a second call | GPT (should fix), Grok, Claude (minor) | **Fixed:** also pinned, each exactly once: `NCLS`, `CAP_WORDS`, `CHUNK`, the `QUANTUM` macro, the `KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;` line, one `#define KEEP(`, and `heap_hand` named exactly twice (its definition and the call in `heap_free`). Tested with a fake `bend` per case. |
| 3 | Stale comments: a reference read no longer allocates (`io64.c` header, `main.bend` header, the comment on law machine's driver errors in `MACHINE.bend`) | Claude | **Fixed** (comments only; the `MACHINE.bend` change is in law machine's comment, not the law, and is listed for the owner's sign-off). |

Round 2: GPT re-ran its reproducers on 0d6be10 (the 128 KiB stack, the forced fallback, the four altered runtimes): ACCEPT.
