Review of framebender's trusted driver on the git branch `index`, in
`/home/luisc/Work/bend-projects/framebender-index` (read-only: do not modify, create or delete
files in the repository, and do not switch branches; compare with
`git diff $(git merge-base main index) index`).

framebender's program is proven: `PROOF.bend` proves every law of `LAWS.bend` and `MACHINE.bend`.
What the proof does not cover is the trusted part: the driver, `main.bend` and `io64.c` (C
effects), the build, htslib, and Bend's runtime. The comment above `law machine` in
`MACHINE.bend` lists exactly what the driver must do, and now also how it writes the index of a
BGZF `-o` file: the order at the open, the error order, "cannot index" exactly when `tabix -p vcf`
(TBI) or `bcftools index` (CSI) refuses the same file, and what each run leaves.

The change adds `-W` (`--write-index[=csi|tbi]`): the driver builds the CSI or TBI index of the
BGZF output on the fly with htslib 1.24's own code (`tbx_parse1`, `hts_idx_push`,
`hts_idx_save_as`), byte-identical to `bcftools index` and `tabix -p vcf`. The laws (`index`,
`index_sink`) and the design passed three rounds of a three-model review
(`reviews/*-index-law*.md`, decisions 1-27 in `reviews/responses-index-law.md`);
`notes/index.md` has the design ("The driver", "The files") and what was built ("Step 2"). The
previous driver was accepted (`reviews/*-driver8*.md`). The trusted part to review:
1. `io64.c`, the index section and its links into the output section: the open order (open
   without truncating, `fstat`, `lstat` of both index names, the temporary file, the renames
   aside with the `link`/`unlink` fallback, `ftruncate`, removal of the moved names, and the
   move back on failure); the per-block push of each line's virtual offset, the carried tail,
   the `END=` lock around `tbx_parse1`; the separate index error flag read at `out_close`;
   `hts_idx_finish` and the save to the temporary name, the rename into place, the `./` prefix;
   the runtime constructor's grammar for the eight `-W` spellings (it must agree with
   `B.Args.parse` in `types.bend`, which is proven).
2. `main.bend`: `Io.out_index`, the `BadIdx` refusal before any input is opened, the error order
   ("no BGZF in this build", "no index in this build"), the messages.
3. `build.sh` and `tools/build_htslib.sh` (the no-libcurl htslib, the refusals, `FB_NO_HTSLIB`),
   and `io64.js`.
4. `test/index.sh`, `test/gen_index.py`, `test/fi_shim.c`: do they test what the comment on law
   machine promises?

Look for, among others:
- any index that does not match the file written: a line across a block boundary, a line ending
  exactly at a block end, the last line without LF, CRLF, a header longer than a block, an
  empty output, `#` lines after the header, contigs in another order than the header;
- any index left next to a file it does not describe, or an old index deleted when the old file
  is kept: each failure point of the open, a failure during the run (`-c e` stop, a driver
  error, Bend's runtime stopping), a failure in the save, rename or close; symlinks and hard
  links between the output, its index names and the inputs; a directory at an index name;
- data races, deadlocks or lost wake-ups between the compressor threads, the writer and the
  index (`--threads 1` and 128), use of freed buffers, memory not bounded as stated;
- the constructor's grammar disagreeing with `Args.parse` on any command line;
- what a build without htslib, or with a different htslib, does.

You may build and run it on small inputs (`./build.sh /tmp/<dir>/fb`; `bgzip`, `tabix`,
`bcftools` and `samtools` are installed), and you may write test files under `/tmp` only. Do not
run anything on the whole-genome files in `data/`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
