# Development

## Build

```
./build.sh
```

Building needs Bend 2.0.39, clang and libdeflate (headers and library: the `libdeflate` package on
Arch, `libdeflate-dev` on Debian and Ubuntu, `libdeflate` in Homebrew). `build.sh` builds in two
steps: `bend main.bend -o framebender.c` writes the program as C (with the driver's effects from
`io64.c`), then `clang -std=c11 -O3 -DFB_LIBDEFLATE ... -ldeflate` compiles it, as `bend -o` would
plus libdeflate, which reads BGZF (`.vcf.gz`) input. `./build.sh out` writes the binary to `out`.
For `-W` it also links htslib 1.24 statically (`-DFB_HTSLIB`, `libhts.a` and its `static_libs`):
the index writer calls `tbx_parse1` and `hts_adjust_csi_settings`, which `libhts.so` does not
export. It must be htslib 1.24 built without libcurl, GCS and S3, so that the binary pulls in
neither libcurl nor libcrypto and htslib never opens a URL: `tools/build_htslib.sh [PREFIX]
[TARBALL]` builds it (from the 1.24 release, checked by its SHA-256) into
`~/.local/opt/htslib-1.24-nocurl`, which `build.sh` finds through `PKG_CONFIG_PATH` (by default
that prefix's). Before running `bend`, `build.sh` stops with a message naming that script if
`pkg-config` finds no htslib 1.24, if its `static_libs` name `-lcurl`, or if `libhts.a` does not
define the two functions. `FB_NO_HTSLIB=1 ./build.sh out` builds without htslib; that binary
stops on `-W` with `error: no index in this build <path>`.
Between the two, `build.sh` patches Bend's heap in the generated C so that a large block freed on
one thread can be reused by any (`notes/memory.md`); it stops if the generated runtime is not the
one the patch was written for. Bend fixed this upstream after 2.0.39 (bendlang/bend#1856), so on
a later Bend the patch and its check go.

The `lawful-*` packages are imported by name and version (`lawful-bytes@0.1.1.0/...`): Bend
fetches each from BendHub once into `~/.bend/lib` and checks it against the package's hash. To
change a package, edit its own repository, publish a new version (`bend PROOF.bend --publish
lawful-x@0.1.0.1` from its directory) and raise the version here, in every file that imports it
and in the packages that depend on it. The proofs here are then checked against the new version.

`bend main.bend -o framebender` still builds in one step, without libdeflate, htslib or the heap
patch. That binary reads plain VCF only and stops on a `.vcf.gz` with `error: no BGZF in this
build <path>` (and on BGZF output, `-W` included), and uses more memory.

Set `BEND_NO_TELEMETRY=1` to turn off Bend's telemetry (`build.sh` sets it). `--threads N` sets
Bend's worker threads too (`io64.c` puts `--threads N` before `BENDRTS` before `main`); the binary
still reads `BENDRTS="--threads M"` and `+RTS --threads M -RTS`, which win. A build with
`-DFB_NO_RTS_THREADS` leaves the runtime's threads alone.

## Check the proofs

```
./check.sh
```

`check.sh` runs these in order:

1. checks the examples (`examples.bend`);
2. type-checks the driver;
3. checks every proof in `PROOF.bend` with `bend`;
4. checks them again with Bend's Lean-proven kernel (`--verdict`, which needs Lean via elan in
   `~/.elan`).

It prints `ALL PROOFS CHECK` twice when everything holds. A change to the code is acceptable when
`check.sh` passes; a change to the science layer needs a new law review (`refs/REVIEW_PROMPT.md`).

To check one proof file while working, use `test/bcheck.sh file.bend [--check-only|--verdict]`. It
runs at most two checks at once, each capped at 4 GB, with a 64 MB stack. A proof that evaluates a big number, such as
`Nat.pow(2n, 29n)` closed by `{==}`, builds it in unary and can otherwise fill the machine's memory.

## Compare with bcftools

```
test/compare.sh ref.fa in.vcf
```

The script runs both tools with `-c w` and counts the records that differ. Before comparing it
upper-cases REF and ALT, and pads sample columns to the FORMAT length the way htslib does on
output.

- Set `BCFTOOLS` and `FRAMEBENDER` to choose the binaries.
- For large inputs, point `TMPDIR` at a disk with room for both outputs, about twice the input
  size.

Expected results:

| input | differing records |
|---|---|
| `data/hg002.chr22.vcf` | 0 |
| the scrambled file | 0 |
| `test/edge/sorted.vcf` | 1, the `<DEL>` record bcftools realigns |

`test/scramble.py ref.fa in.vcf copies seed > out.vcf` makes a stress test. It rewrites each indel
at random equivalent positions, with random padding and case.

Test data (not committed): UCSC hg38 (`chr22.fa.gz` or the whole `hg38.fa`), and the GIAB HG002
NISTv4.2.1 GRCh38 benchmark VCF.

## Benchmarks

`test/bench.sh ref.fa in.vcf [rounds] [-- options]` times framebender (default and
`--threads 1`) against bcftools (one job, and one job per chromosome through `test/bcfsplit.sh`),
interleaved, writing to a file (by default in `data/tmp/bench`, on disk), and prints wall and CPU
time, peak memory and the md5 of the output's records. Its comment lists the settings
(`CPUS`, `MEMMAX`, `CHECK`, ...). Time one benchmark at a time, before/after runs back to back.
[`BENCHMARK.md`](BENCHMARK.md) has the method and full tables of the README's figures; `NOTES.md`
(Q5) and `notes/fast.md` record earlier measurements and where the time goes.

## Compare with the previous build

`test/same.sh new_binary [old_binary]` runs both binaries on every edge case, chr22, the scrambled
set and the generated inputs (`test/gen_edge.py`, `test/gen_rw.py`, run first from the repository
root), under `-c e`, `-c w` and several `-w`, and reports any difference in stdout, stderr or exit
code. Use it after any change to the implementation, together with the gate.

`test/threads.sh new_binary old_binary` checks law `threads` on these cases: `new_binary` with
`--threads N` (1 to 128, at three positions) against `old_binary` without it, then the usage errors
of `--threads` and the threads a run starts.

`test/par.sh new_binary [old_binary]` does the same on the batch-boundary cases of the parallel
machine (`python3 test/gen_par.py`, then `samtools faidx data/tmp/par/par.fa`): a CHROM change at
a piece boundary, a record moving left across one, unsorted input, `-c e` stopping mid-batch,
files shorter than a batch. Run both on builds with small pieces too: `main.bend` sets the piece
size (3670016 bytes); a test build replaces `3670016ull` in the generated C with 300, 1000 or
70001.

`test/out.sh new_binary [dir]` checks the output options (law `output`) and the BGZF writer:
every output form of `-o` and `-O` against the plain run on the cases above and on
`test/gen_out.py`'s block-cut cases (lines of 65279 to 200000 bytes, CRLF, incompressible
records, headers ending at a block boundary), at every `--threads`, where BGZF output must be byte
for byte `bgzip -l L` of the plain output (htslib 1.24 with libdeflate 1.26); then every level on
chr22, `bgzip -t`, `tabix` and `bcftools view`, failed inputs and writes (a full disk, a file
size limit, a `close` that fails, a non-blocking pipe that fills), `-o` naming an input (by
path, link, `/dev/stdin`, a FIFO), file modes, the usage errors, a round trip through
framebender's own reader, and the threads a run starts. `QUICK=1` skips the identity runs;
`NOLIB=binary` also checks a build without libdeflate (`bend main.bend -o binary`). It exits 0
only when every check passes.

`test/index.sh new_binary [dir]` checks the index option (laws `index` and `index_sink`) and the
index writer. On the cases above, `test/gen_out.py`'s and `test/gen_index.py`'s (index edge
cases: a NUL byte, no `##contig` lengths, lengths past 2^32 and 2^41, 300 contigs out of header
order, `#` body lines, INFO/END, SVLEN and FORMAT/LEN ends, `END=` on every line, and lines
`tabix` refuses: a leading-zero POS, positions past 2^29, 2^32 and 2^38; no `##fileformat`
line, or a `#` line before it, which `bcftools index` refuses; `##contig` lines longer than a
block), it applies the
differential rule per format: the run without `-W` first; if its code is not 0, the `-W` run
must be that run exactly with no index; otherwise CSI is judged by `bcftools index` and TBI by
`tabix -p vcf`, each on its own (refused: "cannot index", exit 2, no end-of-file block, no index;
accepted: the same report and output, and the tool's index bytes). Each case runs with CSI and
with TBI; each `-W` run turns the spelling within its format, its place, `--threads N` and the
`-o` form, and starts with an old index at both names.
Then region queries on chr22, the order at the open and the close by failure injection
(`test/fi_shim.c`, an `LD_PRELOAD` shim: each step, each index name, CSI and TBI, and
`renameat2` without `RENAME_NOREPLACE`), URL-like `-o` paths, FIFOs and devices, index names that
are the `-o` file (symlink, hard link), an input or stderr's file, or a directory (through a
symlink too), an older `<stem>.csi` that htslib reads before the `.tbi`, an existing `<name>.old`,
a driver error and Bend's runtime stopping after the open, file
modes, the builds (`NOHTS=binary` from `FB_NO_HTSLIB=1 ./build.sh`, `PLAIN=binary` from `bend
main.bend -o`, `build.sh`'s refusals; `SKIPBUILD=1` skips the last), the usage errors and the
threads seen. `PIECES="b1 b2 ..."` runs the small cases on the small-piece builds too, `BIG=1`
adds the 1000 Genomes files and the whole genome, `QUICK=1` skips the identity runs.

## Files

| files | role |
|---|---|
| `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend` | science layer: definitions and laws |
| `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend` | implementation contract: the machine law, the FASTA premise, and how bytes encode the spec's text |
| `norm.bend` | the program: pieces judged in parallel in batches of 16 (`lawful-halves`) and spliced in order, falling back to the sequential machine |
| `norm_seq.bend`, `norm_fast.bend`, `norm_line.bend`, `norm_run.bend`, `norm_fix.bend` | the sequential machine on packed bytes (`lawful-*`, from BendHub) |
| `main.bend`, `io64.c`, `io64.js` | the trusted driver: file I/O, the `.fai` reader, the BGZF and index writers |
| `build.sh`, `tools/build_htslib.sh` | the two-step build with libdeflate and htslib; the htslib build it needs |
| `PROOF.bend`, `proof_*.bend` | the proofs; `PROOF.bend` proves every law by importing the rest (`proof_b_*`: the bytes machine, `proof_c_*`: rewritten records, `proof_e_*`: the parallel machine; `proof_f_*`: the command line, laws `threads`, `output`, `index` and `index_sink`; notes in `notes/*proofs*.md`) |
| `examples.bend`, `examples_machine.bend` | concrete cases checked by evaluation; the machine's cases are outside the gate (they pass 4 GB in the checker) |
| `test/` | the bcftools comparison, the scrambler, edge cases, FASTA premise cases |
| `reviews/` | every law and driver review, with the responses |
| `refs/` | the sources the reviewers were given: the VCF 4.3 spec and the `bcftools norm` manual |
| `NOTES.md`, `notes/` | decisions, review history, proof notes, measurements |
| `notes/briefs/` | the briefs given to the agents that wrote the code and the proofs |

## Writing proofs

Read `notes/briefs/PROVING.md` before writing proofs. It covers Bend's proof syntax and the
patterns used here.

`NOTES.md`, "Where proofs got hard", has the lessons learned.
