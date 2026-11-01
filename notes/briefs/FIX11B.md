# Brief: driver review 11, round 2's fixes (fb-fix11b)

Read `notes/briefs/SPEED_COMMON.md` first (same rules). Decisions 6-8 in
`reviews/responses-driver11.md`; the reports are `reviews/*-driver11-r2.md`.

1. **Decision 6, the stand-in key's guess** (`norm.bend`, `plan.ph.if`, `plan.ph.ref`,
   `plan.ph.t5`, `plan.est`, `plan.trim`, `plan.trims`, from fb-fix11's 0c01467). It decodes the
   first line's REF and ALT into Strings and recomputes REF's length and reversal for each ALT.
   GPT's input: `/tmp/fb-r11/r2/plan_long_500.vcf` (a 100,000-base REF and 500 symbolic ALTs
   first in a task): 1.54-1.61 s against main's 0.06 s at `--threads 1`. Claude's: 40 chr22 lines
   of 1 MB deletions or insertions (`/tmp/fbrev/gen/gen_bigref.py`): about 30% slower than main.
   Fix: take the key as POS (no guess) when the REF and ALT bytes (from the tab offsets, before
   any decoding) exceed a small bound (try 4 KiB); compute REF's values once; stop when the
   minimum trim reaches zero. Any key is correct, so no statement should change. Keep fb-fix11's
   results (cohort, `sub.vcf`, scr, scr30).
2. **Decision 7, README's scrambled-indels row and clause:** re-measure `data/scr.vcf -c w` with
   framebender and bcftools interleaved (5 rounds); the clause says such files are still somewhat
   slower and that with many copies (scr30) framebender is faster.
3. **Decision 8, USAGE's many-ALT `-m` bullet:** state the measured memory (325 ALTs, GT:AD:
   10,000 samples 7.9 s / 257 MB, 100,000 samples 83 s / 1384 MB; re-measure what you can).

Measure the two reviewers' inputs, the cohort with and without `-m`, `sub.vcf`, scr and scr30,
before and after, at `--threads 1` and the default, against main's build.
