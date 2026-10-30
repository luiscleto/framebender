# Review of phase J (`-W`, law `index`): report

Context: a read-only law and design review that `framebender/reviews/INDEX_LAW_PROMPT.md` asked for. I read `notes/index.md`, the brief, the draft diffs, `MACHINE.bend`, the parser in `types.bend`, `main.bend`, `io64.c`, `build.sh`, the prototype (`data/tmp/index/proto/`) and the htslib/bcftools 1.24 source. Every finding below comes from reading the source, and its line is cited. #1 was also confirmed by running the prototype on a scratch copy.

Verdict: **not ACCEPT as drafted.** The law draft is sound once #3 is added. The driver design needs #1, #2, #4 and #5 fixed. There is no blocker.

## Findings

1. **Should fix: htslib treats the index's file name as a URL when it starts with a registered scheme. (Confirmed with the prototype.)**
   - Where: `notes/index.md` "The files", end steps 3–4, and the prototype's `idx_finish` (`hts_idx_save_as(idx, "x", path, fmt)`).
   - Why: `hts_idx_save_as` opens the file through `bgzf_open` and `hopen`, which call `find_scheme_handler` (`hfile.c`). An unknown scheme falls back to a local file, so `-o chr1:1-1000.vcf.gz` works. A registered scheme does not: `file`, `data`, `mem`, `preload`, `crypt4gh`, `s3*`, `gs*`, and libcurl's `http`, `https`, `ftp` and others. framebender opens `-o` itself with `open(2)`, so the output is written but the index is not:
     - With the prototype, `-o file:x.vcf.gz` exits 2 ("cannot write file:x.vcf.gz"). The output is left without its EOF block, and no index is written.
     - With libcurl linked, an `http:`, `https:`, `ftp:`, `s3:` or `gs:` prefix (when a local directory has that name) makes the trusted driver send the index over the network.
   - Fix: give htslib a name it cannot read as a URL. Prefix `./` to a relative path; an absolute path already starts with `/`. With either, `find_scheme_handler` returns NULL and htslib opens a local file. `hts_idx_write_out` is static, so there is no way to save to a file descriptor instead.
   - Test: `-o file:x.vcf.gz`, `-o data:x.vcf.gz`, and `-o http:/x.vcf.gz` (with a directory `http:`) must each write exactly the local files with those names. Keep `-o chr1:1-1000.vcf.gz` as a test that must keep working.

2. **Should fix: an index failure stops the run mid-way, so what it prints depends on thread timing.**
   - Where: `notes/index.md` "The first failure stops indexing … next `Io.out_write` answers 2004". That error is stored in `io64_out.err`, and `put_bytes` then calls `out_fail` in `main.bend`.
   - Why: the writer thread finds the failure at some later point. How many `-c w` warnings get printed, and whether a `-c e` stop message gets printed, before "cannot index" depends on thread timing and on `--threads`. Also, `out_close` reports a stored error for any exit code. So a `-c e` run that stops (code ≠ 0) after an unindexable line exits 2 with "cannot index" instead of its own stop message.
   - Fix: keep index errors in their own flag, as the prototype already does, and never in `io64_out.err`. Then at `out_close(c)`:
     - c ≠ 0: ignore the flag. No index is written anyway, and the run is byte-for-byte the run without `-W`.
     - c = 0: after all of the machine's messages, print "cannot index <path>", write no EOF block, and exit 2.
   - Cost: the run no longer fails early, but only on rare unindexable outputs.

3. **Should fix: nothing proves that `-W` leaves the sink alone, or that the index belongs to the sink's file.**
   - Where: the draft `law index`, `Args.idx.of`, and the examples `idx_sink` and `idx_threads`, which each pin just one command line.
   - Why: "the same text, plus an index file" needs two facts. Law `index` gives the first: the same launch. The second, that the bytes are written to the same place in the same way, is only in examples. A wrong `Drv.set_idx` could change the sink or the level without breaking law `index`.
   - Fix: add a law or proved theorem `index_sink`. Under `he` and `hx`, it says `B.Args.output(command(pre, x <> post)) == B.Args.output(command(pre, post))`, and the same for `B.Args.threads`. That is the same walk as `same_parse`.
   - Also prove `Args.index` against `Args.output`:
     - `Idx{f, p}` holds exactly when `-W` is given and `Args.output` writes BGZF to a file `q`, with `p == q ++ IFmt.ext(f)`;
     - `BadIdx` holds exactly when `-W` is given and the output is stdout or plain text.

     Alternatively, compute `Args.index` from `Args.output`'s `Sink`, so the two agree by definition.

4. **Should fix: the claim "never for a sorted, well-formed output" is false.**
   - Where: the draft comment on law `machine` (the "cannot index" item), and the note's section "When the index fails, and never".
   - Why: four cases break it.
     - **Leading zeros:** `Pos.read` accepts them (`types.bend:197`), and unchanged records keep their text. So a `-c e` output with POS `9` then `010` is valid and sorted for framebender. `tbx_parse1` reads `010` with `strtoll` in base 0, as octal 8, and refuses the order as unsorted.
     - **CSI with no `##contig` length:** the 8 levels hold positions only up to 2^38.
     - **CSI with lengths:** the levels only cover the longest declared length plus 256 (`hts_adjust_csi_settings`). A POS or INFO/END past that fails.
     - **TBI:** the limit is 2^29, and it applies to INFO/END as well as POS.
   - Fix: state the rule by reference: "cannot index" exactly when `tabix -p vcf` (TBI) or `bcftools index` (CSI) refuses the same file. Then list the known causes, and drop "never".
   - Tests:
     - a `-c e` run with a leading-zero POS;
     - CSI with no length and a POS past 2^38;
     - CSI with a short declared length and a POS past 2^32;
     - `-Wtbi` with INFO/END past 2^29;
     - a `##contig` length past 2^41, which changes `min_shift` (htslib's warning must not appear).

5. **Should fix: a FIFO `-o` blocks before it is refused.**
   - Where: "The files", step 2. `io64_out_open` opens with `O_WRONLY` before its `fstat` (`io64.c:1045`).
   - Why: with `-W` and no reader on the FIFO, the run hangs forever, although it would be refused anyway. With a reader, the reader gets an empty stream.
   - Fix: with `-W`, open with `O_NONBLOCK`. A FIFO with no reader then fails with ENXIO; report that as "not a regular file". Then check `fstat` as planned. Spell out the order: open (no truncate), the `fstat` and input checks, the checks on the index names, remove both old indexes, then `ftruncate`.

6. **Minor: the temporary file is created only after the whole run.**
   - Where: end step 3, `<index>.<pid>.tmp` with `O_EXCL`.
   - Why: some failures are found only after a full run, which then cuts a complete output:
     - a name collision;
     - a name past `NAME_MAX`, which happens when the `-o` name is about 240 bytes or longer;
     - a directory where new files cannot be created.
   - Fix: create the temporary file, and check the index name's length, at the open, right after removing the old indexes. Retry on EEXIST with a counter, and remove the file on every failure path. The cost: a stray `.tmp` file is left only if the process is killed.

7. **Minor: the static binary pulls in libcurl and libcrypto.**
   - Where: `build.sh`, and `static_libs` (`-lcurl -lcrypto`).
   - Why: the binary grows by 4.3 MB and gains dynamic dependencies for code that is dead once #1 is fixed.
   - Fix: build the static `libhts.a` with `--disable-libcurl --disable-gcs --disable-s3`, or accept the cost and record it. Also add an `nm` check that `libhts.a` defines `tbx_parse1` and `hts_adjust_csi_settings`, for a clear error message.

8. **Minor: an unsynchronized write inside `tbx_parse1`.** The static `reported` (`tbx.c:213`) is written by every compressor thread. The race is harmless (it only gates a log line, and logs are off), but say so in the `io64.c` comment.

9. **Minor: the spellings are worded wrongly.** The note calls them "all of bcftools' one-word forms". bcftools 1.24 also accepts `--write-index==csi` and `--write-index==tbi`, because `write_index_parse` accepts `=csi` and `=tbi` (`version.c:132–135`), and it accepts abbreviations. Accepting only a subset is safe. Fix the wording: "the eight documented forms".

10. **Minor: make the test plan differential over the whole corpus.**
    - The rule: for every case and setting, run `tabix -p vcf` and `bcftools index` on a copy first. If either refuses, `-W` must fail with "cannot index", exit 2, no EOF block and no index. Otherwise the index bytes must be equal.
    - Add these cases:
      - lines of 65,279, 65,280 and 65,281 bytes;
      - a header that ends exactly at a block's end;
      - a NUL byte in a body line;
      - a `-c e` stop after an unindexable line (#2);
      - stderr on failing runs compared across `--threads` 1, 16 and 128 (#2);
      - the scheme paths (#1);
      - a FIFO with no reader, under a timeout (#5).

## Answers to the prompt

1. **The laws.**
   - Law `index`, law `machine` and law `usage` together say the machine's report is the same with or without `-W`.
   - No approved law is weakened. `Args.parse` only gains command lines it used to refuse. Each of the eight words ends in today's VCF-path fallback with `opt` True, so `ok` becomes False. The new branch is taken only for those words. So every command line accepted before gives the same `Cfg`, sink and thread count.
   - Gaps: the sink (#3); the driver's failure behavior (#2); and the misleading "never" claim (#4).
2. **The parser is correct.**
   - The new branch comes after the glued `-O` forms. None of the eight words equals `-f`, `-c`, `-w`, `--threads`, `-o` or `-O`, or starts with `-O`.
   - As values (`-f -W`, `-o -W`), the words stay values.
   - The last one counts, because `set_idx` overwrites the earlier one.
   - In `-W tbi`, the word `tbi` is read as the VCF path.
   - `-Ov -o x.vcf.gz` is indexed, by `Args.sink`'s own rule (the extension wins).
   - Stdout, `-o -` and plain output give `BadIdx`.
   - `index_ok` is the exact counterpart of `output_ok`.
3. **The driver.** These parts were checked against `tbx.c` 1.24 and the prototype, and they match:
   - the virtual offsets: a line that ends at a block's end gets the next block's address with offset 0, and the index is finished at the EOF block's address;
   - the CR rule, and `#` lines skipped wherever they are;
   - the `##contig` scan before the first record, and the 8-level rule when there is no length;
   - the order of contig names.

   `io64_out_drain` waits for the writer, so the writer reads each block's text before the buffer is freed. Memory and speed are fine. A plain `bend` build still builds without htslib, and `build.sh` already requires libdeflate, so requiring htslib there is consistent. The remaining issues are #1, #2, #5 and #6.
4. **The author's seven questions.**
   1. On-the-fly indexing with the static link pinned to 1.24: yes, guarded by the version pin and the byte-identity suite, plus #7's `nm` check. Keep A′ as the documented fallback.
   2. `BadIdx` refused by the driver rather than by the parser: yes, together with #3.
   3. Removing both old indexes with `-W`: yes, because a stale `.csi` silently hides a fresh `.tbi`. Without `-W`: no. Don't delete files the user did not name. htslib already warns when an index is a whole second older than its data; say that in the README.
   4. Stop with exit 2 and no EOF block: yes, but at the close only (#2).
   5. Refusing an `-o` that is not a regular file: yes, without the blocking open (#5).
   6. The eight spellings, with no abbreviations and no `##idx##`: yes. Fix the wording (#9).
   7. A new law rather than a wider `out_opt`: yes, together with #3.
5. **The test plan as a substitute for a proof: yes, it is a fair one.** The oracle is htslib's own `tbx_index` loop on the same bytes. Matching its bytes, and refusing exactly what it refuses, is the right specification for the trusted part. It needs #10's differential rule.

## Next step

None. This was a read-only review: nothing in the repository was changed. The lead relays the report to the author.
