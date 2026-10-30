1. **Should fix.** `io64.c`, the CSI path in `idx_block` / `idx_finish` (`io64_ix.bad` is set only when `tbx_parse1` refuses a line). The comment on `law machine` (`MACHINE.bend` 268–270) requires `error: cannot index <path>`, exit 2, no end-of-file block and no index, exactly when `bcftools index` refuses that file. `bcftools index` refuses unless the decompressed file begins with the 16 bytes `##fileformat=VCF` (htslib 1.24 `hts.c:687`; `bcf_index_build3` returns −3; `vcfindex.c:335` prints `index: "<path>" is in a format that cannot be usefully indexed` and exits 255). `-f` does not skip that check. The driver never looks at those bytes, so a CSI run that exits 0 still writes the end-of-file block and a `.csi`.

   Input (`/tmp/fb9/p/re9/noff.vcf`), reference `/tmp/fb9/p/ref.fa`:

```
#CHROM	POS	ID	REF	ALT	QUAL	FILTER	INFO
t1	1	.	A	<DEL>	.	.	.
```

   `/tmp/fb9/fb norm -c w -W -Oz -o /tmp/fb9/p/re9/noff.vcf.gz -f /tmp/fb9/p/ref.fa /tmp/fb9/p/re9/noff.vcf` exits 0 and writes a 114-byte `.csi`. The output starts `##framebender_normVersion=0.1.0`. `bcftools index -f` on that file exits 255 with the format message. The same refusal happens for a leading `#` comment before `##fileformat=VCFv4.2` (`/tmp/fb9/p/re9/cfirst.vcf`): `-W` exits 0 and leaves a `.csi`, and `bcftools index -f` exits 255. A file that does start with `##fileformat=VCFv4.2` matches `bcftools index` (112 bytes). `-Wtbi` on `noff.vcf` matches `tabix -p vcf` (103 bytes). `test/gen_index.py` only builds inputs that start with `##fileformat`, so `test/index.sh` does not catch this.

   Fix: for CSI only, if the uncompressed output is shorter than 16 bytes or does not begin with `##fileformat=VCF`, set `io64_ix.bad`. `out_close` then skips the end-of-file block and the save, removes the temporary index, and the driver reports `error: cannot index <path>` with exit 2. Leave TBI unchanged.

## Addendum (after the delayed probe log)

The delayed probe log does not change the report. Of its 38 `FAIL` lines, only `splitcr` CSI is a real miss: that file does not start with `##fileformat=VCF`, `-W` still writes a `.csi`, and `bcftools index` refuses it. That is the same should-fix already listed.

The other lines are the probe itself. The injection checks used `pos0x10.vcf`, which the machine rejects before an index is built, and their comparator drops a space before `|`. The symlink, FASTA-name, cut-BGZF, and late-Nat cases were re-run on a valid one-record VCF and matched the contract.
