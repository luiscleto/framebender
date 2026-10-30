# Index output: brief for the index agent (phase J)

Goal: `framebender norm -f ref.fa -o out.vcf.gz -W in.vcf.gz` writes the index next to the
output, as `bcftools norm -W` (`--write-index[=FMT]`) does, so a pipeline needs no separate
`tabix`/`bcftools index` step. The owner chose it as the next feature, with multiallelic splitting
(another agent, phase I, in parallel).

## What exists

- Phase H (`notes/compress.md`, `docs/LAWS.md` "output"): `-o FILE`, `-O v|z|z0..z9`; the driver
  (`io64.c`, trusted) cuts BGZF blocks exactly as bgzip 1.24 does, compresses them on N threads
  with libdeflate and writes them in order; the EOF block only on exit 0; the `-o` file opened
  lazily, refused when it is an input. `law output` (`MACHINE.bend`): these options choose only
  where and how the text is written, never the text; `B.Args.output` (`types.bend`) says where
  and how, and `output_ok` (`proof_f_out.bend`) proves it answers for exactly the command lines
  `Args.parse` accepts.
- htslib 1.24 is installed in `~/.local/opt/htslib-1.24` (headers, `libhts.so`, `libhts.a`,
  pkg-config file); `bcftools`, `tabix` and `bgzip` 1.24 are on the PATH.

## Steps

1. **Design and draft; then stop.** In `notes/index.md`:
   - bcftools 1.24's exact behaviour, by experiment: `-W`, `--write-index`, `--write-index=tbi`
     and `=csi`, the default format, the index's name (`out.vcf.gz.csi`/`.tbi`), what happens
     with `-O v`, with stdout, with `-o -`, and when the run fails; its `min_shift` for CSI;
   - the options to accept, and the exact edits to `types.bend` (`B.Args.parse`,
     `B.Args.output` or a sibling) and `MACHINE.bend`, as a diff; the law should say, as `law
     output` does, that the option never changes the text (extend `out_opt`, or a new law), and
     `output_ok`'s counterpart. Not in the header's command line, as `-o`/`-O`;
   - the driver design. Prefer maintained upstream code over a bespoke index writer: htslib's
     `hts_idx_init`/`hts_idx_push`/`hts_idx_finish`/`hts_idx_save_as` fed with the virtual
     offsets the writer already knows (each record's block address and offset within it), or
     `tbx_index_build3` on the finished file (simpler, but a second pass); measure both on the
     whole genome and pick, saying why. A build without htslib must still build (as without
     libdeflate), and `-W` then fails with a clear error, as BGZF does;
   - when the index is written (only on exit 0, after the EOF block; never a stale index left
     next to a new file: remove or replace an old one), its file handling and errors;
   - tests: the index byte-identical to `bcftools index` (CSI) and `tabix -p vcf` (TBI) of the
     same file, on the edge cases, chr22, the scrambled file, the whole genome and the 1000
     Genomes slice, at several `--threads` and levels; `tabix out.vcf.gz chr22:1-1000000`
     returning the right records; failure cases;
   - a quick prototype timing (scratch only): whole genome `-Oz -W` against
     `bcftools norm -Oz -W --threads 16`.
   Print the draft and stop. The lead runs the three-model review, then sends you the outcome.
2. After the review: implement, prove, check, test, time; report and stop.

## Rules

- Work in your own worktree (`../framebender-index`, branch `index`); `data` there links to the
  main checkout's `data`. Scratch in `data/tmp/index/`; do not write other files under `data/`.
- Fixed until the review: everything except `notes/index.md`. The `lawful-*` packages are fixed
  (imported from BendHub, `lawful-x@0.1.0.0`).
- Approved laws are never weakened or deleted; adding definitions and laws is fine.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once).
- **Timing runs one at a time:** `flock data/tmp/bench.lock ...`, `nice -n 19`, a `timeout`,
  pinned (`taskset -c 0-15`), interleaved, ranges (`test/bench.sh`). Another agent works in
  parallel and takes the same lock. Delete each output file before the next run. Keep at least
  8 GB of RAM free.
- Shell scripts that delete files: write them to a script file with literal paths and run that.
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
