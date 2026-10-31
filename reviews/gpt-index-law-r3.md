ACCEPT.

Decisions 20–24 are carried out. The copied prototype passed staging, rollback, backup-collision and per-format checks under `/tmp`. No new blockers or should-fix items found.

Answers to the round-3 questions:

1. The current double-fault error is sufficient: the output remains unchanged and the stranded index is recoverable.
2. Keep failed `.old` cleanup silent; those names cannot shadow the new index.
3. Use `renamex_np(..., RENAME_EXCL)` on macOS. Refusing unsupported filesystems before truncation is acceptable; no link/unlink fallback is needed.
4. The tracked download script is acceptable with its pinned SHA-256 and local-tarball option.
