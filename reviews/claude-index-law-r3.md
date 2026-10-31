**Round 3 verdict: ACCEPT once one should-fix is made.** The rename-aside step has no fallback for file systems that refuse `RENAME_NOREPLACE`. There are no blockers.

## Checks

**(1) Decisions 20–24 are carried out.**
- **Decision 20, the rename-aside order:** the prototype's `io64_out_open` runs the order the note describes: `idx_open`, then `idx_stage`, then `ftruncate`, then `idx_drop_old`.
  - **Move back:** if the second rename fails, `idx_stage` moves the first index back, removes the temporary file, then exits. If the duplicate descriptor or `ftruncate` fails, the open moves both indexes back and removes the temporary file.
  - **No replacement:** `RENAME_NOREPLACE` means a `.old` name never replaces a file, not even an input.
  - **Step 7:** removing the `.old` files is the only change after the truncate. After a successful rename in the same directory, that unlink practically cannot fail.
  - **Law `machine`'s comment** (`machine.diff`) says all of this, including that a stray `.old` file is harmless.
  - **Testing:** the failure-injection table in `r2_fi.txt` covers each step and each index name, for CSI and TBI.
- **Decision 21:** the wording is fixed in law `machine`'s comment, the prototype comment and "The files". The case is tested: a POS past 2^48 leaves `.tmp` and no index.
- **Decision 22, the per-format oracle:** it is correct.
  - The run without `-W` comes first. If its code is not 0, each `-W` run must be that run exactly, with no index.
  - Otherwise CSI is judged by `bcftools index` and TBI by `tabix -p vcf`, each on its own.
  - The claim "a refusal of CSI alone cannot happen" holds. At `min_shift` 14, CSI's levels always cover at least 2^32, TBI's cover 2^29, and every other refusal (parse errors, order, contig blocks) is the same for both formats.
- **Decision 23:** `tools/build_htslib.sh` checks the tarball's SHA-256. The draft `build.sh` refuses, before running `bend`, any htslib that is not 1.24, has `-lcurl` in its static libraries, or lacks the two functions. `FB_NO_HTSLIB=1` still builds without htslib.
- **Decision 24:** the usage line is cut to 38 columns.

**(2) Nothing new is broken.** The laws, the parser, the examples and the round-2 cases are unchanged; the draft still checks with 19 TODOs and no errors.

The alias checks at step 3 are now stricter than they need to be: renaming and unlinking a link at an index name can no longer harm the file it points to. They are harmless, so they can stay.

## Should fix

1. **There is no fallback when the file system refuses `RENAME_NOREPLACE`.**
   - **Where:** `idx_move` and `idx_aside1` in the prototype's `io64.c`, and step 5 of "The files".
   - **Why:** to my knowledge, Linux's NFS client rejects every rename flag with EINVAL. I didn't test this, since no NFS mount was available. Some FUSE file systems do the same, and older kernels return ENOSYS.
     - `idx_aside1` treats any error other than EEXIST and ENOENT as a failure, so the run stops with "cannot write <name>".
     - So on cluster storage, every `-W` re-run next to an existing old index fails.
   - **Fix:** on EINVAL, ENOSYS or EOPNOTSUPP from `renameat2`, fall back to `link(name, t)` then `unlink(name)`.
     - `link` also never replaces: it fails with EEXIST, so the `.old1`, `.old2` … loop still works.
     - Where hard links are not supported (EPERM or EOPNOTSUPP from `link`, as on vfat or exFAT), fall back to `lstat(t)` returning ENOENT, then a plain `rename`.
     - Use the same fallback for `idx_unstage`'s move back.
     - On macOS, use `renamex_np(..., RENAME_EXCL)` first.
   - **Test:** inject EINVAL from `renameat2` with the existing `fi_shim`. The success row and the step 5 and step 6 rows must still hold.

## Answers to the round-3 questions

1. **The double fault:** name the stranded file, for example `error: cannot write o.vcf.gz (old index left at o.vcf.gz.csi.old)`. It costs one line and tells the user why the index is gone.
2. **A failed unlink at step 7:** keep it silent, as decided. After the rename succeeded in the same directory, the unlink practically cannot fail. A warning would break "stderr as without `-W`" for a harmless leftover.
3. **`renameat2` portability:** refusing is not enough, because NFS is common where this tool will run. Add the fallback in the should-fix item above.
4. **`tools/build_htslib.sh`:** fine as a tracked script. The download is pinned to the release's SHA-256, and a local tarball is accepted.
   - Add `--proto '=https'` to the `curl` call.
   - Use `shasum -a 256` where `sha256sum` is missing (macOS).

I changed nothing in the repository.
