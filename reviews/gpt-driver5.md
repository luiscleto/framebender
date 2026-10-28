# GPT driver review 5 (Codex, read-only)

ACCEPT.

Answers to the seven open questions:

1. Heap blocks remain stable: allocation does not move them, and pending buffers are not freed. Mutexes and joins provide visibility.
2. `split(32n, ...)` bounds each group; all waits finish before another group starts. A 65-request Ask passed.
3. Waits report failures in request order. Tests passed for competing layout, truncation, and oversized-read errors, including a later-group failure.
4. Ring ownership preserves order. Empty-queue fallback joins before reading synchronously; switching files or sizes joins before freeing buffers.
5. Early exit does not join blocked readers. Both builds exited correctly while a pipe writer remained open.
6. The bounded memory increase is acceptable; a smaller ring is optional.
7. Buffer allocation failures surface at their ordered wait. CPU heap exhaustion retains the documented runtime exit-1 exception and can occur earlier with speculative allocations.

Validation: 49 focused checks passed, including BGZF corruption, 1 MiB reference boundaries, and both build paths. Repository unchanged.
