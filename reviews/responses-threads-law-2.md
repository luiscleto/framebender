# Law review `--threads`, round 2: responses

All three accept the revised statement (`law threads` over `Args.expecting(pre)`; `Args.threads`
only for accepted lines): `claude-threads-law-r2.md`, `gpt-threads-law-r2.md`,
`grok-threads-law-r2.md`. Claude's four minor items, all accepted for step 2:

| # | finding | response |
|---|---|---|
| 1 | `Args.expecting` includes `ok`, so it is narrower than "where an option may come" (after an error the parser still reads `--threads` as the option; both sides are usage errors) | Drop `ok`: `expecting` means "no option waiting for its value". The law is strictly stronger and still true; the proof needs the lemma that a false `ok` stays false. |
| 2 | The bound on `Args.threads` (None for refused lines, 1 <= n <= 128) is a comment, not a proof; `Args.thr.done` copies `Args.done`'s pattern | Prove the lemma (`Args.threads(argv) == Some{n}` implies `Args.parse(argv)` is `Some` and n in range), and cap the value at 128 in `io64.c` as a second guard. |
| 3 | The `docs/LAWS.md` text is not in the shown diff | Include it in step 2's diff. |
| 4 | The C constructor's copy of the grammar (a lone `-`, an empty word, `+RTS`/`--RTS`) is exact only as far as the copy is | "At most" in the notes; test these cases in the driver review. |

Q4: Grok's round-1 blocker (the law covered only `--threads` right after `norm`) was the one
that changed the statement; GPT raised the same point as should-fix; Claude had argued for the
narrow form. All three independently caught `Args.threads` returning counts for refused lines.
