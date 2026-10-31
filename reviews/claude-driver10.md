I don't accept this yet: there are no blockers, but three findings should be fixed first. The laws and the proof structure check out: nothing unapproved changed, and no approved law got weaker.

**Laws (item 1).** The branch's `LAWS.bend`, `types.bend` and `run.bend` are the approved `data/tmp/split/draft_cr`, plus decisions 24–28 and main's `-W`. The laws that don't involve `-m` are reached only through `out_items` and `items_without_m`, as decision 12 approved. `splits.of`, `split_room` and the comment on `bound` match decisions 33, 35 and 36.

**Proof (item 2).** I checked this by reading only; I did not run `PROOF.bend`. All 40 laws are imported and proven there. No `?TODO` holes, and no `@unsafe`, `def f?` or foreign import outside `main.bend`.

**Old-index warning (item 3).** The names and their order match `hts_idx_check_local` in htslib 1.24's source: the last `.` at index > 0 anywhere in the path, the csi pair before the tbi pair. Symlinks, the `-o` path itself, names with a LF, nothing being opened, and the check coming before any input is read all behave as documented.

**Tests (item 5).** `test/split.sh` on 10 seeds: all 20 runs the same as bcftools. On lone `.` values, only the numeric R value differs from bcftools (`.` against `.,.`), as `USAGE.md` says; a `PL` of `.` is the same in both.

**Speed without `-m` (item 4).** No measurable regression on `joined.vcf`, `scr.vcf` or HG002 chr22, three interleaved rounds against the merge-base build. Wide headers are the exception (finding 3).

All test files were made and run under /tmp. Other reviewers were running at the same time, so the timings are rough.

1. **Should fix: a refused line takes the slow path under `-m`, about 100× bcftools.**
   - **Place:** `norm_split.bend` gives `None` for every refusal, so `split.out` in `norm_seq.bend` sends the line on through `decoded` to `slow.parts`, which runs `B.Rec.parts` on decoded Strings.
   - **Input:** `data/tmp/split/gen/c100.vcf` with its `##FORMAT=<ID=GQ…>` line removed, `-c w -m -any`. It takes 14.3 s, against 0.21 s for the unchanged file and 0.10 s for bcftools; with one extra PL value in the last sample, 16.9 s.
   - **Scale:** `c300` takes 43.9 s, so the cost is linear at about 0.15 s per 146 KB line. A cohort chr22 missing one header line would run for days under `-c w`.
   - **Fix:** let the splitter return the refusal code, proven equal to `split_problem` the way `split_t` covers `Pieces`. At the least, document the cost in `USAGE.md`.

2. **Should fix: under `-m`, memory grows with a line's records and with the file.**
   - **Per line:** one 410 KB line (100k samples, GT only) uses 482 MB with 100 ALTs and 994 MB with 200, about 12 bytes per byte of records. With 1300 ALTs (520 MB of records, under the 2^29 limit) it didn't finish in 900 s under a 4 GB cap, writing 423 of 520 MB. bcftools takes 2.2 s and 553 MB.
   - **Per file:** 2000 samples, 30 ALTs, GT only: 1000 lines use 807 MB; 3000 lines use 1.6 GB on one thread, 2.5 GB at the default, and take 49–60 s. bcftools takes 20 s and 157 MB. The same records already split, run without `-m`, take 8.2 s.
   - **Threads:** they help little here. With 5 ALTs × 12,000 lines: 22.4 s on one thread, 14.4 s on 16, 13.9 s on 128; bcftools 4.1 s.
   - **Many ALTs:** one line with 3000 ALTs × 200 samples of GT:AD takes 12.2 s against 0.66 s; with 6000 ALTs, 48 s against 2.6 s.
   - **Fix:** feed a split line's records through without holding them all, or at least state in `README.md` and `USAGE.md` that `-m` memory grows with the records a line makes and with the file.

3. **Should fix (small): a regression without `-m` on wide headers.**
   - **Place:** `B.Defs.line` (`types.bend:1325`) uses `Bool.pick`, which evaluates both branches. `Hdr.tag` therefore parses every header line twice, the `#CHROM` line included, on every run.
   - **Input:** a 100k-sample header with one record takes 0.46 s against the merge base's 0.11 s, 3 rounds each.
   - **Fix:** match on the prefix in the machine's `Cx.line`, with an equality lemma, or build the definitions only under `-m`.

4. **Minor: the warning claims htslib reads a file that a directory hides.**
   - **Place:** `stale.each` in `main.bend`, and the comment on `law machine` in `MACHINE.bend`.
   - **Input:** a directory at `o.vcf.gz.csi` and an old file at `o.vcf.gz.tbi`. framebender warns that htslib would read `o.vcf.gz.tbi`, but `tabix` and `bcftools view -r` stop at the directory with "Could not load … Is a directory".
   - **Fix:** stop the list at the first name `stat` finds, and print no warning if that is a directory.

5. **Minor: an unwritable stderr changes the `-o` file.**
   - **Place:** `stale.one` writes through `put`, which exits 2 on a failed write.
   - **Input:** `-o o.vcf.gz 2>/dev/full` with an old `o.vcf.gz.csi`. The run exits 2 before the output is opened, so the old `o.vcf.gz` keeps its 11 bytes. Without the old index the same run exits 2 with `o.vcf.gz` emptied. That contradicts "the output bytes … are as above".
   - **Fix:** ignore a failed write of the warning, or state the exception in the comment.

6. **Minor: docs planned by decisions 16 and 22 are missing.**
   - `docs/LAWS.md` has no worked PL example for n = 2; it is drafted in `notes/split.md`'s Terms.
   - `USAGE.md` doesn't say that under `-c w` a split line gives one REF_MISMATCH warning per record.
   - It also doesn't say that an unsplittable line with REF_MISMATCH or BAD_END reports only the split's code (decision 22).
   - Also missing: `A <*>,<*>` stops under `-m -c e` but passes without `-m`.
   - Also missing: a lone `.` for a numeric A/R/G INFO tag stays `.` where bcftools stops.
   - **Fix:** add these to the `-m` section and to the differences list.

7. **Minor: the README's `-m -any` row leaves out refusals.**
   - Under the default `-c e`, a line that can't be split safely stops the run. A user of `bcftools norm -m -any` is most likely to be surprised by an undefined tag: bcftools drops it and splits the line.
   - **Fix:** add "lines it cannot split safely are refused (they stop the run under `-c e`; see USAGE)".

I didn't run `check.sh`, `test/index.sh` or the whole `PROOF.bend`; I used my own scripts for the warning cases instead. The binaries and scripts are in /tmp/claude-1000/-home-luisc-Work-bend-projects-framebender-split/205008d9-175d-4f57-8822-33674e7e9464/scratchpad (the `m/` and `ix/` folders).
