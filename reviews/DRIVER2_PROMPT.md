Round 2 of the driver review (read-only: do not modify, create or delete files).

Your round-1 findings (`reviews/gpt-driver.md`, `reviews/claude-driver.md`, `reviews/grok-driver.md`)
led to these changes (commit "Driver hardened after review"):
- `io64.c` (new, trusted C, about 70 lines): `Io.pread_full` reads n bytes at a 64-bit offset
  (hi * 2^32 + lo), retrying until n bytes or end of file; `Io.write_fd` writes all bytes to an
  inherited descriptor (1 or 2). `main.bend` uses them for every reference read and for stdout and
  stderr (no reopening of /dev/stdout).
- Arguments come from `IO.args_bytes` (one Char per byte) and paths are opened with
  `File.open_bytes`, so non-ASCII arguments are copied exactly.
- The `.fai` is parsed strictly (a line that is not a name and four numbers, or a contig with
  letters but no letters per line, stops with "bad .fai index"); a contig is looked up as present or
  absent (`Map<Maybe<Fai>>`); a present contig with an empty slice answers `Known{n, a2, ""}`
  without reading.
- Every byte read is checked against the `.fai` line layout (`fits`: LF only at the end of a line,
  CR only just before it when lines end in CR LF, no space or tab, letters only in the first lb
  columns), and the number of letters read must equal b2 - a2 (stale index, short read).
- Every driver error prints exactly one line "error: ..." (with the path) as bytes and exits 2.
- `P.Fasta.plain` (in `protocol.bend`) now also excludes a kept contig without letters (samtools
  leaves it out of the index) and a CR inside a line; the trust-boundary comment of `machine` in
  `MACHINE.bend` lists every driver error.
Tested: usage bytes, normal run, empty contig, mid-line CR, path "é α.fa", missing file, bad .fai,
stdout as a socket.

Check `main.bend` and `io64.c` against the comment on law `machine` again. Report a numbered list
(severity, place, concrete input, fix), or say it is correct. Be brief; final answer.
