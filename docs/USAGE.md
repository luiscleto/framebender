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
- When the records waiting in the window come to hundreds of MB of text, the run can run out of
  memory or crash: 1000 Genomes chr22 (2,548 samples, about 14 KB per line) under `-c w` crashes
  at `-w 2000000` and above, and works at `-w 1000000`.

### `-m -any`, `-m -both`, `-m -`: split multiallelic records

A record with two or more ALTs becomes one record per ALT, in the input's ALT order, each then
normalized on its own, as with `bcftools norm -m -any`. The three forms do the same (they differ in
bcftools only when joining); the glued `-m-any`, `-m-both` and `-m-` work too. Records with one ALT,
and every run without `-m`, are handled exactly as before.

The split keeps CHROM, POS, ID, REF, QUAL, FILTER and FORMAT, and gives each record one of the
input's ALTs. Each record is then normalized as without `-m`, so its POS, REF, ALT and END can
change: with reference `AAAAAAAA`, `c1 5 . AA A,AAA` gives `c1 1 . AA A` and `c1 1 . A AA`.

In each record:

- Genotypes: REF stays 0, the record's ALT becomes 1, another ALT becomes 0 (or `.` with
  `--multi-overlaps .`); separators, phasing and ploidy are kept.
- INFO and sample values with `Number=A`, `R` or `G` keep the values of the record's alleles.
  For G, these are the values of the genotypes REF/REF, REF/ALT and ALT/ALT. INFO G values are
  always for two copies. A sample's G values are for the copies its GT names: a one-copy sample
  (`GT=2`) has one value per allele and keeps REF's and the ALT's; a sample with no GT counts as
  two copies; a lone `.` GT can have either count. `docs/LAWS.md` has a worked PL example.
- Every other value is copied as it is, and a missing `.` stays `.`.

A line that cannot be split safely is not split. It is refused, by the first of these reasons:

- `BAD_CR`: a carriage return inside the line (other than the one of a CR LF ending). That is not
  valid VCF, and a record cut at a CR would read back differently.
- `ALT_DUP`: two equal ALTs, symbolic ones too (`<*>,<*>`).
- `UNDEFINED_TAG`: an INFO or FORMAT value whose tag has no usable `##INFO`/`##FORMAT` line (none,
  or no Number that says which values belong to which ALT). The message names the tag and how to
  add one (`bcftools annotate -h`).
- `BAD_COUNT`: an A/R/G value without the expected number of values, a value-less A/R/G entry,
  more than two copies for a G value, or a sample with more values than FORMAT keys. With n ALTs,
  the expected number is: A, n; R, n+1; G, (n+1)(n+2)/2 for two copies (INFO, a sample whose GT
  names two, or a sample with no GT) and n+1 for one copy; either, for a lone `.` GT.
- `BAD_GT`: a genotype allele that is not `.` or a number from 0 to the number of ALTs (written
  without leading zeros or signs). This includes VCF 4.4's leading phase mark (`|0|1`).

As every problem: with `-c e` (the default) the run stops; with `-c w` the line is passed through
unchanged, with a warning ending "not split", so the output can then hold multiallelic records.

Which problem is reported:

- If the whole line would stop the run anyway (MALFORMED, UNKNOWN_CHROM, any problem under
  `-c e`), that is reported, as without `-m`. With `-c e`, a line with both an END that does not fit
  and a carriage return inside stops with BAD_END.
- Otherwise, only the reason it is not split. With `-c w`, a line whose REF does not match the
  reference and that has a tag with no header line gets one UNDEFINED_TAG warning, and no
  REF_MISMATCH.
- A line that is split is judged record by record: with `-c w`, a REF that does not match gives
  one REF_MISMATCH warning per record, as in bcftools.

The summary line counts records after splitting.

**Speed and memory.** With `-m`:

- Under `-c w`, a refused line is passed through about as fast as a line that splits. It takes a
  slow path, about 1 s per MB, when it is refused for `BAD_CR` or `ALT_DUP`, or when no line before
  it on its contig has been checked against the reference yet (the first line of each contig, in a
  file where every line is refused). Under `-c e` the run stops at the first refused line.
- Memory grows with the records a split line makes and with the records that wait in the `-w`
  window (each piece's records are held until it is merged). One line with 100,000 samples and 200
  ALTs used 0.70 GB. 3,000 lines in a row with 2,000 samples and 30 ALTs used 1.9 GB (1.1 GB with
  `--threads 1`) and took 2.5 to 3 times as long as bcftools, which used 0.16 GB. More `--threads`
  speeds such files up only a little.
- The time for one line grows with the square of the records it makes when they are large: one
  line with 10,000 samples took 7.5 s with 325 ALTs, 30 s with 650 and 120 s with 1,300 (bcftools:
  6.5 s). With 100,000 samples each record is ten times larger, and so is the time: the line with
  325 ALTs took 75 s and 1.4 GB, against 7.4 s and 0.26 GB with 10,000 samples (bcftools: 5.0 s
  and 0.64 GB, against 0.5 s). Such a run can look like a hang.

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
  is read. htslib tries `out.vcf.gz.csi`, `out.vcf.csi`, `out.vcf.gz.tbi` and `out.vcf.tbi`, in
  that order, and reads the first one that exists. framebender names only that one:
  `warning: htslib would read out.vcf.csi as the index of out.vcf.gz; remove it or use -W`.
  If it is a directory (htslib cannot read it, and says so) or the `-o` file itself (as with
  `-o x.csi`), there is no warning. The warning touches nothing (`out.vcf.csi` may index
  `out.vcf`), and the run goes on as without it, also if the warning cannot be written. Plain
  output and stdout get no warning.

## Speed and memory

Two kinds of record take a slower path than the rest, with or without `-m`:

- A record that needs rewriting (it moves, or loses bases) and has an INFO/END: HG002's 20,739
  scrambled chr22 indels took 3.6–3.8 s with an END on every record, against 0.08 s without
  (bcftools: 0.1 s with or without; [`BENCHMARK.md`](BENCHMARK.md)).
- Under `-c w`, a line whose END is wrong (`BAD_END`), which is passed through with its warning.

`-m` has its own costs (see `-m` above); `--threads` trades memory for speed.

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
    `BAD_GT`, above), where bcftools:
    - copies a tag whose header line has no Number, or one it does not know (such as `LR`),
      whole to every record;
    - drops a tag with no header line, after a warning;
    - aborts on a flag with no header line (framebender copies the flag and splits the line), and
      on an A/R/G tag without a value;
    - fills or copies some values whose count is wrong (and stops on others), and reads an allele
      the record lacks as another ALT;
  - duplicate symbolic ALTs (`A <*>,<*>`) are refused with `-m` (so `-m -c e` stops the run),
    though without `-m` the line is passed through; bcftools writes two `<*>` records;
  - a VCF 4.4 leading phase mark (`|0|1`) is `BAD_GT` with `-m`, and passed through without it;
    bcftools stops ("Couldn't read GT data", exit 255) with or without `-m`;
  - a lone `.` stays `.` in every record: for a numeric A/R/G INFO value bcftools stops instead,
    and for a numeric R sample value it writes `.,.`;
  - numbers are copied as written (bcftools re-prints them, also without `-m`);
  - GT without a `##FORMAT` line is split and kept (bcftools drops it), empty INFO entries are
    kept, and an INFO key given twice is split twice (bcftools keeps the first);
  - a sample's G values must have the count for the copies its GT names, as VCF 4.3 says, and a
    sample with no GT the two-copy count; bcftools goes by the count alone. With two ALTs and no
    GT, `PL=1,2,3` is `BAD_COUNT`, where bcftools writes `PL=1,2` and `PL=1,3`. A lone `.` GT can
    have either count. INFO G values are for two copies in both;
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
