**ACCEPT.** All 12 decisions are carried out correctly, and I found nothing new broken in `git diff 9621667 58d69d2`. I agree with the judgement call in decision 4.

1. **`--threads` with `-m` (decision 1): fixed.** `io64_threads_of` now handles `-m` and `--multi-overlaps` exactly as `Args.word` and `Args.step` do, in the same order. I counted threads while the program ran a 3000-line, 2000-sample file, with 7 forms of the options and `--threads` 1 and 3:
   - **Before (9621667):** 34–35 threads with any `-m` form, which is the runtime's default pool.
   - **Now:** 3–5 threads, within `test/threads.sh`'s 2N+2 limit.

2. **`test/split.sh` (decision 2): fixed.** It now counts `<` and `>` diff lines. With 10 seeds on the new build: all 20 runs the same as bcftools.

3. **Unwritable stderr (decision 3): fixed.** The warning now goes through `put.try`, which ignores a failed write.
   - With `2>/dev/full`, the run exits 2 and leaves the same `-o` bytes whether or not an old index is there.
   - With stderr a pipe nobody reads, it exits 2 with a 0-byte `-o` file either way.

4. **The first name htslib finds (decision 4): fixed.** `stale.name` and `stale.at` stop at the first name that is the `-o` path itself or that `stat` finds. They warn only when that is a file. These matched htslib 1.24's order:
   - a directory at `o.vcf.gz.csi` with an old `.tbi`: no warning;
   - a directory at `o.vcf.csi` with an old `o.vcf.gz.tbi`: no warning;
   - only `o.vcf.tbi`: a warning;
   - a symlink loop at `.csi`: skipped, like `stat` in htslib, so the next name is warned about;
   - `-o x.csi` with an old `x.csi.csi`: a warning;
   - `-o x.csi` with only `x.csi.tbi`: no warning, as htslib stops at `x.csi`, the output itself;
   - `-o ./x.csi`: the same;
   - `-o x.tbi` with an old `x.csi`: a warning;
   - plain `-o` and stdout: no warning.

   **The judgement call is right:** once the run has written `x.csi`, htslib finds the output at `<stem>.csi`, fails to load it as an index, and never reads `x.csi.tbi`. The `MACHINE.bend` comment, `docs/USAGE.md` and `docs/LAWS.md` describe the same behaviour.

5. **One header parse (decision 5): fixed, and the regression is gone.** The machine's `Cx.line` now calls `Norm.defs.line`.
   - **Proof:** `proof_b_defs_line.bend`'s `line_eq` checks on its own: "ALL PROOFS CHECK" through `bcheck.sh --check-only`. The three changed `proof_b_adv_*` files use it; I didn't check those, as they belong to your `PROOF.bend` run.
   - **Timings** (3 rounds, holding the bench lock):

     | input | 58d69d2 | 9621667 | main |
     |---|---|---|---|
     | 100k-sample header, 1 record | 0.12–0.13 s | 0.44–0.46 s | 0.10–0.11 s |
     | the same, 200 records | 0.35–0.38 s | 0.68–0.70 s | 0.33–0.36 s |
     | the same with `-m` | 2.27–2.42 s | 2.61–2.69 s | — |

6. **Docs (decisions 6–12): correct.** I ran the new claims through both tools, and each does what USAGE and LAWS.md now say:
   - the PL example, with both tools giving `10,20,30` / `10,40,60` and `7,8` / `7,9`;
   - END plus a CR under `-c e` stops with BAD_END;
   - under `-c w`, a REF mismatch with an undefined tag gives only UNDEFINED_TAG;
   - a split line gives one REF_MISMATCH per record, as in bcftools;
   - `<*>,<*>`: refused with `-m`, passed through without it, and bcftools writes two records;
   - `|0|1` is BAD_GT, passed through without `-m`, and bcftools exits 255 both ways;
   - a lone `.` in INFO A/R/G stays `.`, where bcftools exits 255;
   - a tag with no Number gets UNDEFINED_TAG, where bcftools copies it;
   - a flag with no header line is split, where bcftools aborts (exit 134);
   - an undefined tag is dropped by bcftools after a warning;
   - `PL=1,2,3` in a sample with no GT is BAD_COUNT, where bcftools writes `1,2` / `1,3`.

   The README row is shorter than decision 12 asked for (it leaves out "they stop the run under `-c e`"), but it points to USAGE, which says it. That's fine.

7. **The speed and memory text (decisions 13–14) still holds after the thread fix.** My round-1 `--threads` figures under `-m` were measured with the bug, so I timed them again with real thread counts. The figures barely change:

   | input | `--threads 1` | 16 | 128 | bcftools |
   |---|---|---|---|---|
   | 5 ALTs × 2000 samples × 12,000 lines | 22.6 s, 217 MB | 14.2 s, 879 MB | 13.1 s, 1.4 GB | 4.1 s |
   | 30 ALTs × 2000 samples × 3000 lines | 61.5 s, 1.57 GB | 50.8 s, 2.39 GB (default 49.4 s, 2.47 GB) | — | — |

   So "2.5 GB", "2.5 to 3 times as long" and "more `--threads` helps only a little" are still accurate. My earlier measure of the refused-line path, about 1 s per MB, also matches USAGE.

**Not run:** the whole `PROOF.bend` and the three changed proof files (yours to run), and the whole `test/index.sh` and `test/threads.sh`, which use chr22. I read their new parts instead; the expected outputs are right. My scripts for the warning cases are `/tmp/claude-1000/-home-luisc-Work-bend-projects-framebender-split/205008d9-175d-4f57-8822-33674e7e9464/scratchpad/ix/t2.sh`, and for the doc claims `/tmp/claude-1000/-home-luisc-Work-bend-projects-framebender-split/205008d9-175d-4f57-8822-33674e7e9464/scratchpad/dc/d.sh`.
