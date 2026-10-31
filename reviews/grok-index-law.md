Not ACCEPT. No approved law is weakened (`law output`, `out_opt`, the `law machine` statement, `law usage`, `law threads` stay). `law index` is the right shape and is not false. The success-path index matches `tbx_index` / `bgzf_getline`. Fix the file protocol before implementation.

## Findings

1. **should fix.** `notes/index.md`, "The files", steps 4–5, and the new `law machine` bullet "a run that fails leaves no index at either name". Both indexes are unlinked before the `-o` file is truncated. Unlink of `<out>.csi` can succeed and then truncate can fail (read-only `out.vcf.gz`, writable directory): the old file is intact and its index is gone. Unlink of one name can succeed and the other fail (the other is a directory): one good index is already gone and the file was not emptied. The comment overclaims: a failure before open (missing FASTA, bad `.fai`) must leave the old indexes, because they still describe the old file.
   **Fix:** lstat both names first; if either is a directory or an input, exit 2 with nothing changed. Then open and truncate. Only then unlink both. Say that in the `law machine` comment.

2. **should fix.** Same section, and the brief's "never a stale index left next to a new file". Removal happens only with `-W`. A later `framebender -o out.vcf.gz` (no `-W`) replaces the file and leaves `<out>.csi`, which htslib reads with no warning. That is the 0-vs-13335 failure this design already measured (`ex7.sh`), on the feature's own second run.
   **Fix:** on every successful truncate of a regular BGZF `-o` file, unlink both `<out>.csi` and `<out>.tbi`, with or without `-W`. Phase H's contract gains that sentence. Do not unlink on plain output. Test: `-W`, then the same run without `-W`, then `tabix` must not open an old index.

3. **should fix.** Three error orders disagree. `main.k` is specified to refuse `BadIdx` before the run ("needs a BGZF -o file"). `Io.out_set` already returns 2002 for any BGZF output in a build without libdeflate, and today that is after the `.fai` is read. The test plan says plain `bend main.bend -o fb_plain` prints "no index in this build" for `-W`, and "no BGZF" first for `-Oz -W`. `build.sh` always links libdeflate and would require htslib 1.24, so "no index" is unreachable if 2002 is checked first: the plain binary has neither library.
   **Fix:** one order. (1) `BadIdx` in `main`, before opening inputs. (2) Existing 2002, "no BGZF in this build", for any BGZF output. (3) "no index in this build" only when BGZF works and htslib does not. Name that binary (`FB_LIBDEFLATE` without `FB_HTSLIB`); do not claim the plain `bend` binary prints "no index". Point the test plan at those commands.

4. **should fix.** "Building the index". The prototype reads CHROM from the live block (`b + ss`) and copies a carried tail in the writer. Today's `io64_wrun` frees `j->own` and the compressed buffer right after the write, and `out_write` then frees the piece. Freeing first indexes garbage and still exits 0. Same class as the phase H carry-before-`blk_free` bug.
   **Fix:** push the block, and copy any tail that has no LF yet, before those frees. Include the last short block queued at `out_close`. An empty line (`kstring` still NULL) is "cannot index", not a dereference.

## Minor

5. A final line with no LF is pushed at the EOF block's address (`eof << 16`), not at an offset inside the last data block. `bgzf_getline` does `block_offset += l + 1` and moves to the next block even when the delimiter is missing (`bgzf.c`). `idx_finish` in the prototype does this, and `ex6.sh`'s `nolf.vcf` matched. Say it in the driver section so a rewrite does not "correct" it. `hts_idx_finish`'s argument is that same address, the file offset where the 28-byte EOF block will be written, not the offset after it.

6. "never for a sorted, well-formed output" is too wide. `law sorted` orders by decimal `Pos.read` (leading zeros allowed, `types.bend`). `tbx_parse1` uses `strtoll` base 0, so `9` then `010`, or `0x1A`, is sorted for the law and refused by `hts_idx_push`. Keep the failure. Narrow the sentence to a decimal POS with no leading zero and no `0x`.

7. `tbx_parse1`'s `static int reported` (the INFO/END warning in `tbx.c`) is a data race when compressor threads call it. With `hts_set_log_level(HTS_LOG_OFF)` it does not change the index or stderr. Do not serialize the parse to avoid it. One sentence next to the log line is enough.

8. The prototype's metadata copy skips `ed_is_big()` (`tbx_set_meta`). Byte-identity holds on little-endian. Copy the swap.

9. Examples to add: `-W -o x.vcf.bgz` and `-W -o x.VCF.GZ` (indexed; suffix appended to the spelling given), and `--write-index tbi` as the only VCF path (accepted, CSI, file `tbi`). Tests to add: failure before open leaves both old indexes; one index name is a directory and the other is a real index (the real one remains, file unchanged); read-only `-o` in a writable directory (truncate fails, indexes remain).

10. The summary "changes nothing the program writes" is the machine report, not the process. `law index` already puts BadIdx, "cannot index" and "cannot write `<path>.csi`" outside the law, as `law output` does. Keep that. Do not let `docs/LAWS.md` say the process exit code is unchanged. No need for a Bend-heap sentence: the index is C heap (`malloc` failure is "cannot index" or the existing "out of memory", pick one and list it).

## The five review questions

1. **Laws.** Together they say what `law output` says. `law index` is launch equality wherever `Args.expecting(pre)` and `Args.idx_opt(x)`. At that position the new `Args.word` branch changes only `Drv.idx`, so `Cfg`, `Opts.args` and `launch` match the line without `x`, including a line that was already going to be refused. No previously accepted line changes: the eight words are usage errors today, and in value position (`-o -W`, `-f --write-index`) they never reach that branch. `Args.index` is `Some` on the same `ArgSt` as `Args.done` / `Args.sink.done`, so `index_ok` is `output_ok`'s counterpart (`NoIdx` and `BadIdx` included). The process can still exit 2 where the machine exits 0. That is named, and it is not a weakening. The holes are findings 1 and 2, where the new comment's "leaves no index" is false or incomplete.

2. **Parser.** The eight spellings, glued and with `=`, last one wins (`Drv.set_idx`), `-Ov -o o.vcf.gz` indexed, `-Oz -o o.vcf` and stdout and `-o -` are `BadIdx`, another format and `--write` refused, a format in the next word is a path. Unambiguous. `Args.output` and `Args.threads` ignore `idx`.

3. **Driver.** On the fly is the right call (finding 4 and minors 5–8 are the gaps). Virtual offsets match `bgzf_tell`: low 16 bits are the uncompressed offset after the LF, and a line that ends on the last byte of a block is `(addr + size) << 16`, which is also how a 65536-byte block avoids dropping a bit. Meta lines move `offset0` only until the first record; `##contig` lengths use htslib's scan and set CSI levels only then; a file with no records still `hts_idx_init`s at finish. Contigs are first-seen order, so a header order that differs is fine. `grouped_in` plus `sorted` means a successful run does not repeat a contig or go backwards in decimal POS; the remaining refusals are minor 6, TBI past 2^29, and a short `##contig` length whose CSI levels cannot hold a passed-through POS. Those must fail the run (question 4). A crash during `hts_idx_save_as` can leave a complete file, no final index, and `<path>.<pid>.tmp`; the note's "complete exactly when the index is there" should say "on a normal exit".

4. **Author's questions.**
   - **A, static htslib 1.24.** Accept. The parse is the floor, and A is the only one that runs it on the compressor threads. Guard it with a `static_assert` on `tbx_intv_t` (the prototype's layout matches 1.24: `beg`, `end`, `ss`, `se`, `tid`) and with the byte-identity test. A′ and B stay the fallback if the static link is rejected. Minors 7 and 8 go with this.
   - **BadIdx, not a usage error.** Accept. A usage error would make "adding `-W`" change whether the line parses, and `law index` would need a premise on the whole line. Same choice as `-Oz -o x.vcf` in phase H. The separate message is the point.
   - **Remove both names.** Yes when `-W` opens the file, and also when any BGZF `-o` truncate succeeds (finding 2). Not when `-W` is absent and the file is not replaced.
   - **Index failure stops the run.** Yes. Exit 2, no EOF block, no index. Exit 0 without an index, or with a partial one, is the bad outcome.
   - **Refuse a non-regular `-o`.** Yes. The offsets do not need a seek, but a FIFO or `/dev/null` cannot be queried afterwards, and `<path>.csi` must not be created.
   - **Eight spellings.** Yes. No abbreviations, no `##idx##`. Paths stay literal.
   - **New law, do not widen `out_opt`.** Yes. Widening `out_opt` would change an approved definition. The proof sketch (`parse_idx`, `FT.same_parse`, `FO.texts_drop` on `[x]`, `index_ok`) matches `proof_f_out.bend`. The three `Drv{...}` patterns in `proof_f_args.bend` are the only ones outside `types.bend`.

5. **Tests.** Byte-identity with `tabix -p vcf` and `bcftools index` of the same file, across threads and levels, is a fair substitute for a proof of the writer, the same standard as phase H against `bgzip`. It is not a substitute for the proof of `law index`. Add the cases in finding 9, and the no-`-W` rewrite in finding 2. The success-path oracle is the right one; do not compare against `bcftools norm -W`, whose blocks differ.
