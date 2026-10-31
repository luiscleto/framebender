The law/parser draft is sound at the abstract-machine layer: no approved law statement is weakened, previously accepted commands retain their `Cfg`, and `index_ok` mirrors `output_ok`. The laws do **not** guarantee unconditional equivalence of actual runs: indexing errors can change the written prefix, diagnostics and exit status.

1. **Blocker — parallel `tbx_parse1`, [notes/index.md:714](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:714).** htslib’s [tbx.c:218](/home/luisc/Work/bend-projects/framebender-index/data/tmp/index/src/htslib/htslib-1.24/tbx.c:218) reads and writes a shared `static int reported` for invalid INFO/END. Disabling logging does not prevent this data race. **Fix:** use a thread-safe parser implementation or serialize parsing; pinning version 1.24 alone is insufficient.

2. **Blocker — sidecar removal, [notes/index.md:767](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:767).** Suppose `out.vcf.gz` is a symlink to the existing `out.vcf.gz.csi`. Opening succeeds, then removing `.csi` unlinks the opened data file. Publishing the index recreates that path, leaving the output symlink pointing to CSI bytes and losing the VCF. **Fix:** check both sidecar names against the opened output’s device/inode before either removal; reject this aliasing case.

3. **Should fix — empty CSI initialization, [idx_proto.h:151](/home/luisc/Work/bend-projects/framebender-index/data/tmp/index/proto/idx_proto.h:151).** `idx_finish` calls `idx_first`, which adjusts levels even without records. Upstream’s empty-index branch retains its initial settings. Confirmed under `/tmp`: header-only output gives prototype `(min_shift,n_lvls)=(14,8)`, versus `(14,6)` from `bcftools index`; bytes differ. **Fix:** reproduce upstream’s separate empty-index initialization.

4. **Should fix — FIFO rejection, [notes/index.md:764](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:764).** Adding the regular-file check after the existing blocking `open(O_WRONLY)` can hang forever on a FIFO without a reader. **Fix:** reject special files before blocking, and verify the opened descriptor before changing files. Test a FIFO with no reader.

5. **Should fix — runtime argument parser, [io64.c:1243](/home/luisc/Work/bend-projects/framebender-index/io64.c:1243).** The implementation plan omits updating `io64_threads_of`. It treats every new index spelling as an unknown option, so adding `-W` disables the constructor’s `--threads` setting. **Fix:** recognize all eight spellings there, preserving pending-value handling; test each spelling.

6. **Should fix — prototype memory handling, [idx_proto.h:61](/home/luisc/Work/bend-projects/framebender-index/data/tmp/index/proto/idx_proto.h:61).** Allocation and kstring/hash failures are unchecked throughout scanning, name insertion and metadata construction; these can crash rather than return 2004. Metadata/error entries also leave `ss` uninitialized before it is incremented and used in pointer arithmetic. **Fix:** check every allocation result, initialize entries, and access CHROM offsets only for records. Add allocation-failure injection before promoting this prototype.

7. **Minor — lifecycle guarantee, [notes/index.md:790](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:790), also the new machine comment.** “A run that does not exit 0 leaves no index” contradicts early rejection preserving an existing output/index. “Output is complete exactly when the index is there” also fails when the duplicate’s close fails: the design removes the index but leaves EOF. **Fix:** scope these statements to replacement having begun and cleanup succeeding, retaining phase H’s rollback exceptions.

8. **Should fix — test oracles, [notes/index.md:891](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:891).** Several expectations are wrong:
   - Removing EOF makes `bgzip -t` warn but exit **0**, confirmed locally. Check the EOF bytes explicitly.
   - MALFORMED POS and blank body lines stop normalization even under `-c w`; confirmed exit **1**, without passing that line to indexing.
   - A `-c e` stop and Bend OOM likewise do not uniformly exit 2.
   - A plain build lacks libdeflate too, so valid indexed output encounters “no BGZF” before `Io.out_index`. Add a libdeflate-only build to exercise “no index”.

   Correct these expectations and add the failures above, boundary-region queries, and injected save/rename/close failures. Then the plan is reasonable validation of the trusted part, although it remains testing rather than proof.

For the author’s seven questions: **1:** accept approach A only after resolving thread safety; otherwise prefer A′. **2:** accept `BadIdx` in the driver. **3:** remove both sidecars with `-W`; address removal without `-W` as a separate phase H change. **4:** accept stopping on index failure. **5:** accept regular-file-only output with nonblocking rejection. **6:** accept the eight spellings and stated exclusions. **7:** keep the separate `index` law.

Repository unchanged; executable checks used copies under `/tmp`.
