# Compressed output: brief for the compress agent (phase H)

Goal: framebender writes bgzip-compressed VCF (`.vcf.gz`, BGZF) itself, as `bcftools norm -Oz`
does, so the speed comparison matches how the tool is used in pipelines, and the output can be
indexed (`tabix`, `bcftools index`). The owner: "We can do the compressed output next, sounds
useful". Speed first: compression must not take away the lead (whole genome 1.8 s plain today).

## What exists

- Output: the machine produces the output text; the trusted driver writes it to stdout in blocks
  (`Io.write_block` in `io64.c`, called from `main.bend`'s loop). `law machine` (`MACHINE.bend`)
  states that output as `L.run(fasta, vcf, o)`; the driver only writes it.
- Input `.vcf.gz` is read by the driver with libdeflate (`io64.c`: `io64_kind`, the BGZF block
  reader), already a dependency and already trusted. Compression is the mirror image: the
  machine's text stays as it is, and the driver compresses what it writes.
- The command line is parsed by `B.Args.parse` (`types.bend`, science layer) into
  `B.Cfg{B.Opts{strict, w, args}, fasta, vcf}`; `--threads` (phase F, `notes/threads.md`) is the
  precedent for an option that never changes the output: `law threads` in `MACHINE.bend` says a
  command line with `--threads x` launches the same as the one without it, and the driver reads
  N itself (`Io.threads`, the constructor in `io64.c`). `o.args` is printed in the header
  (`##framebender_normCommand`) without `--threads`.
- bcftools 1.24: `-o, --output FILE`, `-O, --output-type u|b|v|z[0-9]` (also glued: `-Oz`,
  `-Oz9`), the output type inferred from `-o`'s extension when `-O` is absent, `--threads` also
  used for compression, `-W, --write-index`. htslib's BGZF: blocks of at most 64 KiB, each a gzip
  member with the `BC` extra field, and a 28-byte empty block at the end.

## Steps

1. **Design and draft the law change; then stop.** Like `--threads`, this changes the science
   layer's parser and the contract, so the lead runs the three-model review on your draft first.
   Propose, in `notes/compress.md`:
   - the options: which of `-O v|z|z0-9` (and glued forms) and `-o FILE` to accept, and why;
     the default (plain to stdout, as today); the default compression level; what happens with
     `-O b|u` (BCF: refused as a usage error, unless you argue otherwise);
   - whether they appear in `##framebender_normCommand` (with `--threads` they do not, so the
     text is the same either way);
   - the exact edits to `types.bend`, `MACHINE.bend` (and `LAWS.bend` if any), as a diff; keep
     them minimal. A law in the style of `law threads`: the options choose only how the text is
     written (compressed or not, where), never the text. Say plainly what stays trusted (the
     compressor, the file writing) and how it is tested instead;
   - the driver design: BGZF blocks compressed in parallel with libdeflate (how many threads,
     following `--threads`), written in order, the end-of-file block; `-o`'s file handling
     (create/truncate, permissions, a failed run's partial file); memory;
   - a plan for tests: decompressing gives byte-for-byte the plain output (`bgzip -dc`), `bgzip
     -t`, `tabix -p vcf` and `bcftools view` accept it, at every `--threads`, on the edge cases,
     chr22, the scrambled file and the whole genome; truncated writes and full disks;
   - what the proofs and examples need, and the expected size of the work;
   - a quick prototype measurement is welcome (scratch only): whole genome to `.vcf.gz` against
     `bcftools norm -Oz --threads 16`, `bcftools norm -Oz` and `bcftools norm | bgzip -@16`, with
     output size, time and peak memory.
   Print the draft and stop.
2. After the review (the lead's message): implement, prove, check, test, time; report and stop.

Out of scope for now, but do not design it out: writing an index (`-W`), BCF output.

## Rules

- Work in your own worktree (`../framebender-gz`, branch `gz`); `data` there links to the main
  checkout's `data`. Scratch in `data/tmp/gz/`; do not write other files under `data/`.
- Fixed until the review: everything except your notes. `../lawful-*` stay fixed.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once).
- **Timing runs one at a time:** `flock data/tmp/bench.lock ...`, `nice -n 19`, a `timeout`,
  pinned (`taskset -c 0-15`), interleaved, ranges (`test/bench.sh` does this; extend a scratch
  copy for more cases). Delete each output file before the next run; `cat` to a file on this
  btrfs disk is a reflink copy, not a write. Keep at least 8 GB of RAM free.
- Shell scripts that delete files: write them to a script file with literal paths and run that
  (`rm` inside `sh -c` or with a variable path needs the owner's approval each time).
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
