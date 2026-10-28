# Beating bcftools on the whole genome: brief for the speed agent (phase D, plan only)

Read first:
- `README.md`, `docs/DEVELOPMENT.md`, `NOTES.md` (the last three sections).
- `../ARCHITECTURE.md`: the planned parallel design (`lawful-halves`, pieces read in parallel).
- `../spike/RESULTS.md`: the measured parallel prototypes (`par`, `par2`, `par3`) and what limited
  them (copies when splitting a block, `Array.new` zero-filling, memory bandwidth).
- `notes/bytes.md`, `notes/rewrite.md`: the current design. `notes/speed.md`: the SIGPROF sampler
  (perf is not installed; no sudo).
- `main.bend`, `io64.c`: the trusted driver.

## Where things stand (whole genome, HG002, 4,048,342 records, 2.8 GB, warm page cache)

| run | framebender | bcftools 1.24 |
|---|---|---|
| output to /dev/null | 5.4-7.0 s | 6.1-6.3 s |
| output to a file | 7.9-8.4 s | 7.9 s |
| `cat` of the input / `cp` of it | 0.06 s / 0.3 s | |

framebender runs one sequential computation. The machine has 32 threads.

## Goal of this phase: a measured plan, no code

1. **Profile** the whole genome (or a large slice of it) on the `main` build. Split the time into
   the driver (reading pieces into blocks, writing output, the reference reads), the machine's
   fast path, the sorting buffer and the output. Find why writing to a file costs 1.5-2.5 s more
   than to /dev/null when `cp` writes the same bytes in 0.3 s.
2. **Options**, each with the expected gain (measured where you can, with scratch prototypes in
   `data/tmp` or `../spike`), what it changes, and what it costs to prove or review:
   - **Driver only** (trusted code; a change needs a three-model driver review, no proofs):
     bigger or fewer reads and writes, `mmap`, writing straight from blocks, the reference reads.
   - **Parallel machine:** pieces judged in parallel, combined in order. Say exactly what changes
     in the contract (`protocol.bend`, `MACHINE.bend`; a contract change needs a three-model
     review), what `lawful-halves` must state, how reference reads work when many pieces need
     them, and how the sorting buffer and `-c e` (stop at the first error) carry across pieces.
   - **`.vcf.gz` input** through libdeflate in the driver (most real VCFs are bgzip-compressed;
     BGZF blocks decompress independently, so this can be parallel too). Measure against
     `bgzip -dc | framebender` and `bcftools norm` on a `.vcf.gz`.
   - Anything else the profile suggests.
3. **Recommend** an order. The aim is a clear, reproducible win over bcftools on real inputs,
   with the laws unchanged and every guarantee kept.

## Rules

- Do not edit tracked files. Scratch work goes in `data/tmp` (ignored) or `../spike`. Write the
  plan in `notes/speed_plan.md` (new file; the lead commits it).
- **Timing.** `nice -n 19` and a `timeout` on every build and run. Set `BEND_NO_TELEMETRY=1`.
  Check `pgrep -af "bend |fb_|bcftools"` before timing; nothing else should be running.
  Interleave and give ranges. Whole-genome outputs go in `data/tmp` (not `/tmp`, which is RAM);
  delete them afterwards.
- **Memory.** Any `bend` check goes through `test/bcheck.sh`. Watch memory when building large
  prototypes; keep at least 8 GB free.
- **Tools.** Use maintained upstream tools and libraries where they exist (libdeflate, htslib's
  bgzip). Install nothing system-wide; anything that needs sudo goes to the lead as a request.
- No commits, pushes or branch switches.

## Report

Print the plan's summary and stop: the profile, the options with gains and costs, the recommended
order, and anything the lead must decide or ask the owner.
