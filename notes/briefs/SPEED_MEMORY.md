# Brief: -m memory (fb-memory)

Read `notes/briefs/SPEED_COMMON.md` first. Under `-m -any`, memory grows with the records a line
makes and with the file (driver review 10, decision 14 in `reviews/responses-driver10.md`;
`reviews/claude-driver10.md` finding 2 has the figures):

- one 410 KB line (100k samples, GT only) with 200 ALTs uses 994 MB, about 12 bytes per byte of
  records; with 1300 ALTs it did not finish in 900 s under a 4 GB cap. bcftools: 2.2 s, 553 MB.
- 2000 samples x 30 ALTs x 3000 lines (GT only): 1.6 GB on one thread, 2.5 GB at the default,
  49-60 s. bcftools: 20 s, 157 MB. The same records already split, run without `-m`: 8.2 s.
- 5 ALTs x 12,000 lines: 22.4 s on one thread, 14.4 s on 16; bcftools 4.1 s.

**Your part:** find where the memory goes (a line's records held as a list before they are
written? per-record buffers? a piece's output held whole?) and stream a split line's records
through instead of holding them, in the proven part, proven equal to what it replaces. Then the
speed on the shapes above. This branch already has fb-tasks (the merge keeps a task's warnings)
and fb-refuse (refused lines on bytes); fb-end is changing the bytes fast path (`norm_fast.bend`,
`norm_fix.bend`) at the same time, so stay out of those. If streaming needs a change to the
output contract in `MACHINE.bend` (what a piece returns, `bound`, `out_len`), stop and report: that
is a law change.

When it is fixed, the README's results clause and `docs/USAGE.md`'s "Speed and memory" note
about `-m` memory change to what is still true (those are the docs edits allowed).

**Measure** max RSS (`/usr/bin/time -v`) and wall time on the shapes above (make them with
`test/gen_split.py` or a script of yours under `data/tmp/memory/`), at `--threads 1`, the default
and 16, before and after, with bcftools beside them; and the cohort, joined and HG002 with `-m`,
and HG002 without `-m`, which must not get slower or use more memory.
