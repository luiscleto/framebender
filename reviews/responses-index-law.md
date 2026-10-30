# Law review of index output (phase J): responses

Prompt: `INDEX_LAW_PROMPT.md`. Round 1: Claude (`claude-index-law.md`), GPT 6.1 Sol
(`gpt-index-law.md`), Grok 4.7 (`grok-index-law.md`); none accepted. All three: no approved law
is weakened; every command line accepted before gives the same `Cfg`, sink and thread count;
the parser is unambiguous; `index_ok` is `output_ok`'s counterpart; building the index on the
fly with htslib 1.24's own parser is the right choice; the virtual offsets match `bgzf_tell`;
`BadIdx` belongs in the driver, not in the parser; an index failure stops the run with exit 2;
an `-o` that is not a regular file is refused; the eight spellings; a new law rather than a
wider `out_opt`; byte identity with `tabix -p vcf` and `bcftools index` is a fair test of the
trusted part.

| # | finding | by | decision |
|---|---|---|---|
| 1 | `tbx_parse1` writes a shared `static int reported` when INFO/END <= POS: a data race on the compressor threads (it only gates a log line) | GPT (blocker), Claude, Grok (minor) | **Fix:** the race is undefined behaviour in C even when harmless in practice, and it is cheap to remove: the static is reached only for a line whose INFO contains `END=`. The wrapper takes a mutex around `tbx_parse1` for such lines (the same `strstr` test htslib makes), and calls it without a lock otherwise. Time it on a gVCF-like input (END on most lines); say it in the `io64.c` comment. |
| 2 | Sidecar removal: an `-o` symlinked to its own `.csi` is unlinked; one index removed and the other name fails; the indexes are removed before a truncate that can fail; a failure before the open must keep the old indexes | GPT (blocker), Grok | **Fix:** one order, written in the note and the `law machine` comment: (1) open without truncating, `O_WRONLY \| O_NONBLOCK`; (2) `fstat`: a regular file, not an input; (3) `lstat` both index names: refuse (exit 2, nothing changed) if either is a directory, or the same device and inode as the output or an input (a symlink resolved by `stat`, too); (4) create the temporary index file (decision 9); (5) `ftruncate`; (6) unlink both old indexes. A failure in (1)-(5) leaves the old file and both old indexes. |
| 3 | A FIFO `-o` blocks in `open` before it is refused | GPT, Claude | **Fix:** `O_NONBLOCK` (decision 2); ENXIO is "not a regular file". Test a FIFO with no reader, under a timeout. |
| 4 | An index failure is stored in `io64_out.err`, so what is printed before "cannot index" depends on thread timing, and a `-c e` stop after an unindexable line exits 2 with the wrong message | Claude | **Fix:** index errors go to their own flag, never `io64_out.err`. At `out_close(c)`: c != 0, ignore the flag (no index is written; the run is the run without `-W`); c = 0 and the flag set, print "cannot index <path>" after all the machine's messages, write no EOF block, exit 2. |
| 5 | Nothing proves that `-W` leaves the sink and the thread count alone, or that the index belongs to the sink's file | Claude | **Fix:** a law `index_sink`: under the same premises as `index`, `Args.output` and `Args.threads` of the line with `x` equal those without. Compute `Args.index` from `Args.output`'s `Sink` (`Idx{f, q ++ ext(f)}` for a BGZF file `q`, `BadIdx` for stdout or plain text), so the two agree by definition. |
| 6 | "cannot index never happens for a sorted, well-formed output" is false: leading-zero POS (`010` is octal 8 to `strtoll` base 0), `0x`, CSI levels from `##contig` lengths, no length past 2^38, TBI past 2^29 (POS and END) | Claude, Grok | **Fix:** "cannot index exactly when `tabix -p vcf` (TBI) or `bcftools index` (CSI) refuses the same file", then the known causes. Add the tests Claude lists (leading zero under `-c e`, the CSI and TBI limits, a contig length past 2^41). |
| 7 | htslib reads the index name as a URL when it starts with a registered scheme (`file:`, `data:`, with libcurl `http:` ...): the index is not written, or goes over the network | Claude (confirmed) | **Fix:** prefix `./` to a relative path. Tests: `-o file:x.vcf.gz`, `data:`, `http:/x.vcf.gz` (with a directory `http:`) write exactly the local files; `-o chr1:1-1000.vcf.gz` keeps working. |
| 8 | The writer frees the block and its tail right after the write; indexing after that reads freed memory | Grok | **Fix:** index each block, and copy a tail with no LF yet, before the frees, including the last short block at `out_close`. An empty line (kstring NULL) is "cannot index", not a dereference. If `io64_out_drain` already orders this (Claude), say where. |
| 9 | The temporary file is made only after the whole run: a name clash, a name past `NAME_MAX`, or a directory without write permission fails after a full run | Claude | **Fix:** create it at the open (step 4 of decision 2), retry on EEXIST with a counter, remove it on every failure path. |
| 10 | The error order: `BadIdx`, "no BGZF in this build" and "no index in this build" disagree between `main.bend`, `Io.out_set` and the test plan; the plain `bend` binary has neither library | Grok, GPT | **Fix:** (1) `BadIdx` in `main`, before inputs are opened; (2) "no BGZF in this build" for any BGZF output; (3) "no index in this build" only when BGZF works and htslib does not. Test (3) with a libdeflate-only build, named in the plan. |
| 11 | Header-only output: the prototype's empty CSI has `n_lvls` 8, upstream 6 | GPT (confirmed) | **Fix:** upstream's separate empty-index initialization. |
| 12 | `io64_threads_of` treats the new spellings as unknown, so `-W` turns off `--threads` | GPT | **Fix:** recognize all eight there (with the pending-value handling); test each spelling with `--threads`. |
| 13 | The prototype does not check allocations, kstring and hash results; `ss` uninitialized on meta lines; the metadata copy skips `ed_is_big()` | GPT, Grok | **Fix** all; allocation failure is "cannot index". |
| 14 | Lifecycle wording: "a run that does not exit 0 leaves no index" is false for early refusals; "complete exactly when the index is there" holds only on a normal exit; the summary "changes nothing the program writes" is the machine's report, not the process | GPT, Grok | **Fix** the wording (scoped to replacement having begun, normal exit, the machine's report). `docs/LAWS.md` must not say the exit code is unchanged. |
| 15 | A rewrite without `-W` leaves `<out>.csi` beside the new file | Grok | **Not in phase J** (Claude and GPT: do not delete files the user did not name; bcftools does not either; it would change phase H's contract). Document it under `-W` in the usage text and README: htslib warns when the index is older than the file by a second or more, but not within the same second; remove the old index. Recorded as an open lead. |
| 16 | A final line with no LF is pushed at the EOF block's address; `hts_idx_finish` gets the address where the EOF block will be written | Grok | **Document** it in the driver section, so a rewrite does not "correct" it. |
| 17 | The static `libhts.a` pulls in libcurl and libcrypto (4.3 MB) | Claude | **Fix:** build it with `--disable-libcurl --disable-gcs --disable-s3`; add an `nm` check for `tbx_parse1` and `hts_adjust_csi_settings`; a `static_assert` on the `tbx_intv_t` layout (Grok). |
| 18 | Test oracles: `bgzip -t` exits 0 without the EOF block (check the bytes); MALFORMED POS and blank lines stop with exit 1 even under `-c w`; `-c e` and Bend OOM exit codes; differential rule over the whole corpus (refused by tabix or bcftools index exactly when "cannot index", else equal bytes); block-boundary lines (65,279/65,280/65,281 bytes), a header ending at a block end, NUL in a line, stderr across `--threads` 1/16/128, injected save/rename/close failures, region queries at boundaries; `-W -o x.vcf.bgz`, `x.VCF.GZ`, `--write-index tbi` as the VCF path; the failure-order tests of decision 2 | GPT, Claude, Grok | **Fix** all. |
| 19 | Wording: "all of bcftools' one-word forms" (bcftools also takes `==csi` and abbreviations) | Claude | **Fix:** "the eight documented forms". |

## Round 2

Claude (`claude-index-law-r2.md`), GPT (`gpt-index-law-r2.md`), Grok (`grok-index-law-r2.md`): no
blockers; decisions 1-19 carried out; `index_sink` is true and says what decision 5 asks; no
approved law weakened; every old command line keeps its `Cfg`. Grok: ACCEPT. All three: the lock
on any line containing `END=` is right and costs nothing measurable; temporary names `.tmp`,
`.tmp1` ... with `O_EXCL` are fine; no removal of old indexes without `-W`; the `END=` slowness
is its own lead, before gVCF users meet it.

| # | finding | by | decision |
|---|---|---|---|
| 20 | Removing the old indexes after `ftruncate` can fail (sticky directory, `EPERM`): exit 2, an emptied output, both old indexes kept (GPT confirmed by injection) | Claude, GPT | **Fix (GPT's order):** after steps 1-4, rename both old indexes aside to temporary names (`O_EXCL`-style, as decision 9); a failure aborts with nothing changed. Then `ftruncate`; if it fails, rename them back. Then unlink the moved names; a failure there leaves a stray file htslib never reads, not a stale index. Test a failure at each step and on each index name. |
| 21 | "no run leaves the temporary file unless it is killed": Bend's runtime stops with `_exit(1)` (out of memory, a Nat past 2^48), so `atexit` never runs | Claude | **Fix** the wording ("unless it is killed or Bend's runtime stops it"); add the case to the test plan (a stray `.tmp`, no index). |
| 22 | The differential oracle "if either refuses" is wrong: at POS 600,000,000 CSI succeeds (equal to `bcftools index`) and TBI is refused | GPT | **Fix:** compare CSI with `bcftools index` and TBI with `tabix -p vcf` separately; a run that stops in normalization keeps its report and output and writes no index. |
| 23 | The no-curl htslib | all three | **Fix:** install it at `~/.local/opt/htslib-1.24-nocurl`, selected with `PKG_CONFIG_PATH`; `build.sh` refuses a `libhts.a` whose `static_libs` name `-lcurl`, with a message naming the prefix and the three `--disable-*` flags; the build script is tracked (`tools/` or `test/`). |
| 24 | The usage line about old indexes runs past 130 columns and prints on every usage error | Claude (GPT, Grok: keep it) | **Fix:** keep it, cut to one short clause (e.g. "-W also removes FILE's old .csi/.tbi"); the full explanation goes in the README. |

## Round 3

Claude (`claude-index-law-r3.md`), GPT (`gpt-index-law-r3.md`), Grok (`grok-index-law-r3.md`): no
blockers; decisions 20-24 carried out (GPT re-ran the staging, rollback and per-format checks on
a copy). GPT: ACCEPT. Claude and Grok: one should-fix each. All three: keep a failed removal of
the `.old` files silent; the tracked download script is fine (pinned SHA-256, local tarball path).

| # | finding | by | decision |
|---|---|---|---|
| 25 | A failed move back (after `ftruncate` fails, or after step 5 cannot move the second index) leaves `<name>.old` beside the unchanged `-o` file; the law-machine comment, the note and the prototype comment still say steps 1-6 change nothing; the step-5 row is missing from the injection table | Grok | **Fix:** one clause in each place (the index stays as `<name>.old`, the `-o` file unchanged, the message `cannot write <path>` or `cannot write <name>`); add the step-5 move-back row for both formats. The message itself stays as it is (GPT, Grok; Claude would name the `.old` file). |
| 26 | `renameat2(RENAME_NOREPLACE)` is refused by NFS, some FUSE file systems and old kernels, so every `-W` re-run next to an old index fails there | Claude (GPT, Grok: refusing is enough) | **Fix, a narrow fallback:** shared cluster storage is where this tool runs, and NFS supports hard links. On EINVAL, ENOSYS or EOPNOTSUPP from `renameat2`, use `link(name, t)` (never replaces: EEXIST keeps the `.old1`, `.old2` loop) then `unlink(name)`; if that unlink fails, remove `t` and refuse with nothing changed. Where `link` is not supported either, refuse as now (no check-then-rename, which could replace a file). The same for the move back. Test by injecting EINVAL with `fi_shim`. macOS (`renamex_np`) is a later port; phase J builds on Linux. |
| 27 | `tools/build_htslib.sh`: `curl --proto '=https'`; `shasum -a 256` where `sha256sum` is missing | Claude | **Fix.** |

The law review of phase J is closed: the laws (`index`, `index_sink`) and the parser are
accepted by all three; decisions 25-27 are driver text and code, checked in the driver review
after implementation.
