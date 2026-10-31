Review of `9621667`:

1. **Should fix — [io64.c:1857](/home/luisc/Work/bend-projects/framebender-split/io64.c:1857).** `io64_threads_of` does not recognize `-m`, its glued forms, or `--multi-overlaps`, so these options disable the runtime’s `--threads` setting. On 10,000 sorted multiallelic records with 1,000-byte IDs, `--threads 1 -m -any` used the default pool—33 OS threads here. **Fix:** mirror the new argument syntax and validation in the C parser; test actual worker counts with these options.

2. **Should fix — [test/split.sh:24](/home/luisc/Work/bend-projects/framebender-split/test/split.sh:24).** Counting only diff lines beginning `<` misses records absent from framebender’s output. A wrapper running `fb "$@" | sed '$d'` still produced `ALL 2 RUNS THE SAME AS BCFTOOLS` for seed 1. **Fix:** fail on any nonzero `diff` status, checking both directions.

3. **Should fix — [main.bend:407](/home/luisc/Work/bend-projects/framebender-split/main.bend:407).** The informational warning uses fatal `put`, violating the promise to preserve output and exit behavior. With an existing output and `2>/dev/full`, adding an old index makes the run preserve the old output instead of truncating it. Injecting EIO specifically on the warning changes an otherwise successful exit from 0 to 2. **Fix:** make warning emission best effort.

Checks passed: splitter refinement proof with `--verdict`; 80 splitter comparisons using a corrected comparator; 80 runs without `-m` against the merge base; ALT/sample stress cases and warning-path checks. The full `PROOF.bend` was not run, as requested.
