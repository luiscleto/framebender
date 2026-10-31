# Usage

```
framebender norm -f ref.fa [options] in.vcf[.gz]
```

The reference needs an index next to it: `samtools faidx ref.fa` writes `ref.fa.fai`.

The input is plain VCF or bgzip-compressed `.vcf.gz`. A compressed file that is cut short is
refused.

## Options

### `-c e` / `-c w`: what to do with a REF that does not match the reference

- `-c e` (the default) stops at the first record whose REF does not match the reference.
- `-c w` passes such records through unchanged, with a warning.

### `-w N`: how far a record may move left

`N` is in bases. The default is 1000, the same window as `bcftools norm --site-win`.

- A record that moves further stops the run with UNSORTED, naming both lines; re-run with a
  larger `-w`. (bcftools writes such a record out of order and exits successfully.)
- Larger windows hold more records in memory, which slows down files with many samples per line.

### `-m -any`, `-m -both`, `-m -`: split multiallelic records

A record with two or more ALTs becomes one record per ALT, in the input's ALT order, each then
normalized on its own, as with `bcftools norm -m -any`. The three forms do the same (they differ in
bcftools only when joining); the glued `-m-any`, `-m-both` and `-m-` work too. Records with one ALT,
and every run without `-m`, are handled exactly as before.

In each record:

- CHROM, POS, ID, REF, QUAL, FILTER and FORMAT are kept, and the record's ALT is the input's ALT
  alone.
- Genotypes: REF stays 0, the record's ALT becomes 1, another ALT becomes 0 (or `.` with
  `--multi-overlaps .`); separators, phasing and ploidy are kept.
- INFO and sample values with `Number=A`, `R` or `G` keep the values of the record's alleles
  (for G, the genotypes REF/REF, REF/ALT, ALT/ALT; one value pair for a haploid sample). Every other
  value is copied as it is, and a missing `.` stays `.`.

A line that cannot be split safely is not split. It is refused, by the first of these reasons:

- `BAD_CR`: a carriage return inside the line (other than the one of a CR LF ending). That is not
  valid VCF, and a record cut at a CR would read back differently.
- `ALT_DUP`: two equal ALTs.
- `UNDEFINED_TAG`: an INFO or FORMAT value whose tag has no usable `##INFO`/`##FORMAT` line (none,
  or no Number that says which values belong to which ALT). The message names the tag and how to
  add one (`bcftools annotate -h`).
- `BAD_COUNT`: an A/R/G value without the expected number of values (for G: from the copies the
  sample's GT names), a value-less A/R/G entry, more than two copies for a G value, or a sample with
  more values than FORMAT keys.
- `BAD_GT`: a genotype allele that is not `.` or a number from 0 to the number of ALTs (written
  without leading zeros or signs).

As every problem: with `-c e` (the default) the run stops; with `-c w` the line is passed through
unchanged, with a warning ending "not split", so the output can then hold multiallelic records. If
the whole line would stop the run anyway (MALFORMED, UNKNOWN_CHROM, any problem under `-c e`), that
outcome is reported, as without `-m`.

The summary line counts records after splitting.

Splitting loses information; read the records with that in mind:

- A `1/2` genotype becomes `1/0` and `0/1`: each record says the other copy is REF, which was not
  observed. With `--multi-overlaps .` it becomes `1/.` and `./1`, which is true, but no record says
  any more that the sample has no REF copy here.
- Values for the other ALTs are dropped: AD no longer adds up to DP, and PL/GL/GP lose the
  genotypes with two different ALTs (the likeliest one for a `1/2` sample).
- Site-level values with a fixed or unknown Number (DP, AN, a VEP CSQ under `Number=.`), and ID,
  are copied to every record, including parts about the other ALTs.
- Normalization can move the records apart, so joining them again (`bcftools norm -m +any`) does not
  undo the split.

### `--multi-overlaps 0` / `--multi-overlaps .`: other ALTs in genotypes

With `-m`, how a genotype's copy of another ALT is written in a record: `0` (REF, the default, as
bcftools) or `.` (unknown). Without `-m` it changes nothing but the header's command line.

### `--threads N`: how much work runs at once (1 to 128)

`N` pieces of the file are normalized in parallel by at most `N` of Bend's worker threads, with
`N` pieces read ahead and `N` reference reads in flight.

- Without it: 16 pieces, one worker per CPU.
- A larger `N` needs more memory; `--threads 1` uses the least.
- It changes only speed and memory, never the output (law `threads`). The header does not
  record it.

### `-o FILE`: write to a file instead of stdout

A name ending in `.vcf.gz` or `.vcf.bgz` (in any case) gets bgzip-compressed VCF (BGZF, ready for
`tabix`), and one ending in `.vcf` plain VCF, as in bcftools; the name decides over `-O`.

- `-o` refuses to overwrite an input.
- A run that cannot read its inputs leaves an existing file as it was.

### `-O z`, `-Oz`, `-Oz0` to `-Oz9`: compress (`-O v`, `-Ov`: don't)

This also works on stdout, and for an `-o` name the extension does not decide. The default level is 6, as in bcftools and bgzip; `-Oz1` is faster
for a larger file.

- The file is byte for byte what `bgzip` makes of the plain output, at every `--threads`
  (law `output`: these options never change the text).
- A `.vcf.gz` ends with BGZF's end-of-file block only when the run succeeded. So a run that stops
  never leaves a file that looks complete.

### `-W`, `--write-index[=csi|tbi]`: also write the output's index

- `-W` (or `--write-index`) writes `FILE.csi`.
- `-W=tbi` (or `-Wtbi`, `--write-index=tbi`) writes `FILE.tbi` instead.

**What it writes.** The index is what `bcftools index` (CSI) or `tabix -p vcf` (TBI) writes for
the same file under a `.vcf.gz` name. It is built while the file is written, and is byte for byte
the same when their htslib compresses with libdeflate, as framebender's does. It never changes
the output (laws `index` and `index_sink`).

**When it runs.**
- It needs a BGZF `-o` file. Otherwise the run stops with `error: -W needs a BGZF -o file`,
  before anything is read.
- The index is written only when the run succeeds, after the file is complete.

**When it fails.** A file `bcftools index` or `tabix` would refuse ends the run with
`error: cannot index FILE`, and no index is written. This happens for:
- a passed-through POS with a leading zero;
- with `-W=tbi`, a position past 2^29;
- with CSI, an input that does not begin with `##fileformat=VCF`.

**Old index files.** htslib reads `.csi` before `.tbi`, so a stale one would silently answer
region queries for the new file.
- `-W` first removes an old `FILE.csi` and `FILE.tbi`.
- For `out.vcf.gz`, htslib also reads `out.vcf.csi` before `out.vcf.gz.tbi`. `-W=tbi` does not
  remove that file (it may index `out.vcf`), and refuses to run while it exists:
  `error: cannot write out.vcf.gz.tbi (htslib would read out.vcf.csi first)`.
- A run without `-W` leaves an old index as it is. htslib warns about it only when it is a second
  or more older than the file, so framebender warns first: for a BGZF `-o` file, before anything
  is read, one line for each name htslib would read as its index (`out.vcf.gz.csi`,
  `out.vcf.csi`, `out.vcf.gz.tbi`, `out.vcf.tbi`, in that order) that exists:
  `warning: htslib would read out.vcf.csi as the index of out.vcf.gz; remove it or use -W`.
  It touches nothing (`out.vcf.csi` may index `out.vcf`), and the run goes on as without it.
  A directory there is not warned about (htslib cannot read it, and says so); nor is plain output
  or stdout.

## Differences from bcftools norm

The records are the same as bcftools 1.24's, except:

- **Symbolic alleles** such as `<DEL>` are passed through; bcftools realigns them.
- **Problems that stop the run.** Unsorted input, duplicate ALTs, inconsistent INFO/END and empty
  alleles stop the run; bcftools warns or carries on.
- **Unknown chromosomes.** A record framebender does not normalize passes through even on an
  unknown chromosome, where bcftools stops.
- **How normalized records are written.** Alleles are in upper case, and POS has no leading zeros.
  Everything else on a line is kept byte for byte, including sample columns that bcftools pads
  (`1/0:1,1` for `GT:AD:PS` stays as is).
- **The header** gets two added lines with no date, so the output is reproducible. Its command
  line leaves out `--threads`, `-o`, `-O` and `-W`, which do not change the records.
- **Options not supported:** BCF output, and the long forms of `-o`/`-O` and `-m` (see `docs/LAWS.md`).
- **`-m`** differs in these ways (the records are bcftools' wherever the input is well formed):
  - a line it cannot split safely is refused (`BAD_CR`, `ALT_DUP`, `UNDEFINED_TAG`, `BAD_COUNT`,
    `BAD_GT`, above), where bcftools drops undefined tags silently, fills or copies values whose
    count is wrong, reads an allele the record lacks as another ALT, or aborts on a tag without a
    value;
  - a lone `.` for a numeric R sample value stays `.` (bcftools writes `.,.`), and numbers are
    copied as written (bcftools re-prints them, also without `-m`);
  - GT without a `##FORMAT` line is split and kept (bcftools drops it), empty INFO entries are
    kept, and an INFO key given twice is split twice (bcftools keeps the first);
  - G counts follow the sample's GT (one copy, or two), as VCF 4.3 says; bcftools goes by the
    count alone;
  - a line with a carriage return inside is refused (`BAD_CR`); bcftools splits it, and its own
    second run can then read a record differently;
  - not supported: joining (`-m +...`), `-m -snps`, `-m -indels`, `--keep-sum`, and G values of
    more than two copies.
- **`-W`** differs in these ways:
  - it takes only the eight documented forms (no abbreviated `--write`, no `##idx##` in the path);
  - it is refused for stdout or plain output before anything is read, where bcftools leaves a
    header-only file;
  - it writes the index after the end-of-file block, and only on success;
  - it removes old indexes; bcftools saves the index first and leaves stale ones.
- **Old indexes without `-W`** are warned about (see "Old index files"); bcftools says nothing.
