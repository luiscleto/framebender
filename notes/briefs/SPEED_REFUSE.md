# Brief: refused lines under -m on bytes (fb-refuse)

Read `notes/briefs/SPEED_COMMON.md` first. With `-m -any`, a line the byte splitter
(`norm_split.bend`) cannot split returns `None`, and the machine (`split.out` in `norm_seq.bend`)
sends it to the String path (`slow.parts`, which runs `B.Rec.parts` on decoded Strings). On a
cohort line that is about 0.15 s per 146 KB line, 100x bcftools (driver review 10, decision 13 in
`reviews/responses-driver10.md`; `reviews/claude-driver10.md` finding 1 has the inputs: a cohort
file with one `##FORMAT` line removed, under `-c w`). Harmless under `-c e` (the run stops), very
slow under `-c w`.

**Your part:** let the byte splitter return the refusal (the split problem's code and what the
warning needs), proven equal to `split_problem` the way `split_t` (`proof_s_drv.bend`) covers the
pieces, and let the machine pass the line through on bytes with that outcome. `docs/USAGE.md`'s
"Speed and memory" note about refused lines changes when it is fixed (that is the one docs edit
allowed). fb-end changes the bytes fast path (`norm_fast.bend`, `norm_fix.bend`) and fb-tasks the
merge at the same time; stay out of those.

**Measure** the reviewer's inputs (a cohort with an undefined FORMAT tag, `c100`/`c300` in
`data/tmp/split/gen/`), before and after, and the cohort and HG002 with `-m`, which must not get
slower.
