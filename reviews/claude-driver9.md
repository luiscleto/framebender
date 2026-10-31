The driver is correct and I found no blocker. Everything wrong is in what law machine's comment promises about other tools, in one stale-index case, and in test coverage. I built it with `./build.sh /tmp/fb-review9/fb` and ran four cases under `/tmp/fb-review9/w` (script: `/tmp/fb-review9/run.sh`); nothing in the repository changed.

**What holds up** (read against htslib 1.24's `tbx_parse1`, `tbx_index`, `bgzf_getline`, `tbx_set_meta`, `hts_idx_save_as`):
- **Where each line is pushed:**
  - a line ending exactly at a block end goes to the next block's address;
  - a line across blocks is carried;
  - CRLF is handled;
  - `#` lines after the header are skipped;
  - contigs get their id in order of first appearance;
  - the end-of-file address is the one tabix uses.
- **The index settings:** the `##contig` length scan, the CSI levels with and without a length, the empty index and the metadata bytes all match htslib.
- **Threads:**
  - the `END=` lock covers the only shared static in `tbx_parse1`;
  - each block is indexed before the writer counts it written, so before the drain and the frees;
  - there are no new waits, so no deadlocks or lost wake-ups.
- **Files:**
  - open steps 1–7 and the move back;
  - the save, rename and take-back at the close;
  - removal of the temporary file at exit.
- **Command line:** the constructor's grammar takes the same branches as `Args.word`.
- **main.bend:** `BadIdx`, the error order and the messages.
- **Build:** the guards in `build.sh`, `tools/build_htslib.sh` and `io64.js`.
- **A run:** a header line of 70 KB holding a `##contig` length, at `--threads` 1 and 128, gives indexes byte-identical to `bcftools index` and `tabix -p vcf`.

**Findings**

1. **should fix: `bcftools index` refuses files that `-W` indexes.**
   - **Where:** `MACHINE.bend:228` and `:269-270` (law machine's comment), and `notes/index.md:526` ("Both reference tools run htslib's `tbx_index` loop").
   - **Why:** `bcftools index` only indexes a file that htslib recognises as VCF, which means the file must start with `##fileformat=VCF`. The machine does not require that line; it only needs a `#CHROM` line.
   - **Input:** a VCF holding `#CHROM…` and `t1 5 . A <DEL> . . SVLEN=-2`, run with `norm -W -o o.vcf.gz`.
   - **Result:** exit 0 and a `.csi` is written. `bcftools index` on a copy says "is in a format that cannot be usefully indexed" (exit 255). `tabix -C -p vcf` gives the same bytes as our `.csi`.
   - **Fix:** use `tabix --csi -p vcf` as the CSI reference in the comment and notes, and say it equals `bcftools index` for files starting with `##fileformat=VCF`. Add that input to `test/gen_index.py`.

2. **minor: `tabix -p vcf` decides by file name.**
   - **Where:** the same comment lines.
   - **Why:** tabix sends any name ending in `.cram` down its CRAM path, even with `-p vcf`.
   - **Input:** `norm -Wtbi -Oz -o x.cram …`.
   - **Result:** exit 0 and `x.cram.tbi` is written. `tabix -p vcf` on a `.cram` copy fails ("bam_index_build failed"). Renamed to `.vcf.gz`, tabix gives the same bytes as ours.
   - **Fix:** word the reference as "the same file under a `.vcf.gz` name".

3. **should fix: an old index named after the stem hides the new `.tbi`.**
   - **Where:** `io64.c:1387` (`idx_check_name`) and step (3) of law machine's comment.
   - **Why:** for `o.vcf.gz`, htslib looks for an index in this order: `o.vcf.gz.csi`, then `o.vcf.csi`, then `o.vcf.gz.tbi`. The driver removes `<path>.csi` for this reason ("htslib reads .csi before .tbi", `MACHINE.bend:211`), but leaves `o.vcf.csi`.
   - **Input:** an `o.vcf.csi` that indexes a different file, then `norm -W=tbi -o o.vcf.gz a.vcf`.
   - **Result:** exit 0. Then `tabix o.vcf.gz t1:1-40` and `bcftools view -r` both read the stale index and fail ("Invalid BGZF header at offset 115"). Naming the new index with `##idx##` gives the right records. With another layout the query could return wrong records silently.
   - **Fix:** with TBI, refuse at step 3 while `<path minus its last extension>.csi` exists, changing nothing ("cannot write <path>.tbi"). At least state this in the comment and the README.

4. **minor: "byte for byte" needs a condition.**
   - **Where:** `MACHINE.bend:228`.
   - **Why:** the index file is itself compressed by htslib. Byte identity holds only when the reference tools' htslib compresses as the linked one does (libdeflate). `notes/index.md:530` says so; the comment does not.
   - **Fix:** add "with an htslib that compresses as the linked one does (libdeflate)".

5. **minor: test gaps** in `test/index.sh` and `test/gen_index.py`. Missing:
   - an output without `##fileformat` (it would have caught 1);
   - a header line longer than a block, with a `##contig` length inside it (it passes by hand: the run above);
   - the -o file hard-linked to an index name (only the symlink is tested);
   - stderr's file at an index name;
   - an existing `<name>.old`, which makes the driver use `.old1`;
   - a stale `<stem>.csi` (3).

   **Fix:** add these cases.

Verdict: ACCEPT the code; fix 1 and 3 before merging (2, 4 and 5 are minor).
