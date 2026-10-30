**ACCEPT.** I found no blocker and nothing that should be fixed. All six decisions in 4f9f68c are carried out correctly, and none of the edge cases I tried broke anything. I built it to `/tmp/fb-review9/fb2` and ran the checks with `/tmp/fb-review9/run2.sh` (outputs in `/tmp/fb-review9/r2`); the repository is unchanged.

**1. CSI refuses files without `##fileformat=VCF`.**
- **How the code does it:** the check runs on the writer thread, in block order, so it collects the first 16 bytes even when they are split across blocks. `idx_finish` refuses any output shorter than 16 bytes.
- **Against htslib:** this matches its own test. htslib also reads past the first block when it looks at the start of the file, and `bcf_index_build3` refuses anything that is not detected as VCF.
- **What the runs gave:**
  - **CSI refused:** with no `##fileformat` line, with a `#` line before it, or with `##fileformat=VCX`, `-W` gives "cannot index o.vcf.gz" and exit 2, as `bcftools index` refuses (exit 255). No index is left, and the output is the plain run's bytes minus the end-of-file block.
  - **TBI on those files:** exit 0, with the same bytes as `tabix -p vcf`.
  - **CSI kept:** a line of exactly `##fileformat=VCF`, and a header-only output, give the same bytes as `bcftools index`.
  - **`-c e` stopping on a REF mismatch:** exit 1, with no index at either name.

**2. Older `<stem>.csi` before a TBI.**
- **Against htslib:** `idx_check_hidden` follows htslib 1.24's search order exactly: `f.csi`, then the stem `.csi` (cut at the last `.` after the first byte), then `f.tbi`, each found with `stat`. The `ix_stem` used for the message cuts the name the same way.
- **What the runs gave:**
  - An `o.vcf.csi` that is a file, a directory, or a symlink to the -o file is refused. The message is "cannot write o.vcf.gz.tbi (htslib would read o.vcf.csi first)", and the file is left alone.
  - `./a.b/o` is refused with "…would read ./a.csi first".
  - `-W` writing CSI is not affected.

**3. Index name that resolves to a directory.**
- A symlink to a directory, or a chain of symlinks ending at one, is refused at either index name before anything is changed.
- A symlink pointing at itself is still accepted. That is correct: htslib cannot read it either.

**4–5. The wording on byte identity and on `.cram` names** in law machine's comment is now accurate.

**6. Tests.** Every case now runs once as CSI and once as TBI, and the new cases are in. `QUICK=1 test/index.sh /tmp/fb-review9/fb2 /tmp/fb-review9/t2` ends in ALL PASS: queries, 50 failure-injection runs, files, builds and usage errors. That mode skips the byte-identity runs, so I checked the new `gen_index.py` inputs for identity by hand (point 1 above).

**Nothing new broken.** Error code 2012 fits the existing ranges in `out_fail`, and `ix_msg` gives each code its own message. The new check happens at step 3, before the temporary file is made, so a refusal changes nothing.
