No blockers. One should-fix.

**Should-fix.** A failure in steps 1–6 does not always leave both old indexes where they were. `r2_fi.txt` already shows the double fault: `ftruncate` fails, moving `o.vcf.gz.csi.old` back fails, exit 2, `error: cannot write o.vcf.gz`, the `-o` file unchanged, and `o.vcf.gz.csi.old` left behind (CSI and TBI). `idx_unstage` in `data/tmp/index/proto/io64.c` (lines 1142–1144) ignores that failure. The same function runs when step 5 cannot move the second index aside (`idx_stage`, lines 1149–1151): if the move-back fails, the first index stays as `<name>.old` and the message stays `cannot write` of the name that would not move. That row is not in the injection table.

These sentences still say steps 1–6 change nothing:

- `data/tmp/index/draft/MACHINE.bend`, the law-machine comment, lines 210–212
- `notes/index.md` line 53, the lifecycle bullet at line 1399, and the test-plan line at lines 1572–1573
- the `idx_stage` comment at `proto/io64.c` line 1114 ("nothing changed")

"The files" (lines 1369–1372) already states the `ftruncate` exception and does not state the step-5 one. Add one clause in each of those places: if moving an index back fails, it stays as `<name>.old` beside the unchanged `-o` file, and the message stays `cannot write <path>` (the `-o` file, after `ftruncate`) or `cannot write <name>` (the index step 5 could not move aside). Add one injection row for the step-5 move-back failure, on each format. Leave `idx_unstage` as it is.

Decisions 20–24 are otherwise carried out. The open renames both indexes aside before `ftruncate`, a failed second rename moves the first back, and step 7’s failed unlink stays silent (`r2_fi.txt`, both formats, both names, plus the end-path save, rename, and close rows). The oracle is per format (`r2_oracle.txt`, `oracle fail=0`): at POS 600,000,000 CSI matches `bcftools index` and TBI is refused; a `-c e` stop keeps the run without `-W` and writes no index. Identity is 48/48 (`r2_ident.txt`). T1–T6 still pass, including the symlink, directory, FIFO, and hard-link refusals (`r2_cases.txt`). `law index_sink` is unchanged. `test/out.sh` and `test/threads.sh` still match only the first usage line. The no-curl build check, the tracked `tools/build_htslib.sh`, and the decision-21 wording are in place.

**Questions**

1. The message is enough. `cannot write <path>` is the `ftruncate` failure, the `-o` file is unchanged, and `<name>.old` is not a name htslib reads. Do not add the stranded name to the message. Do record the exception, as in the should-fix, so the contract stops saying both indexes are always restored.
2. Stay silent. Decision 20 already lets the run go on, and a warning would make stderr differ from the run without `-W`. The success rows in `r2_fi.txt` exit 0 with no message and a good index.
3. Refusing at step 5 is enough. `EINVAL` from the first `renameat2` fails before anything is moved, `idx_die` removes the temporary file, and both old indexes stay. A `link` then `unlink` is not one replacement and can leave the index name missing, which is the window decision 20 closed. `renamex_np(..., RENAME_EXCL)` is a later port. Phase J is the Linux `renameat2`.
4. The download is fine in a tracked bootstrap script. The SHA-256 check rejects a different tarball, and `[TARBALL]` remains the offline path.
