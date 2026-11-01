# Brief: the fair benchmark and a short results section (fb-bench)

The features and the speed work are merged (main at 4adf4a7). The README's "Results against
bcftools norm 1.24" section grew piece by piece and the owner finds it too long and one-sided.
Redo the measurements fairly and rewrite it short. You own the machine's benchmarking: nothing
else will time anything while you run.

## What to measure

framebender's lead is mostly parallelism: bcftools norm normalizes on one thread. People who need
bcftools to go faster split the work, usually one job per chromosome. So compare three ways:

1. **One core each:** framebender `--threads 1` against `bcftools norm`.
2. **All cores:** framebender's default against bcftools split per chromosome, 16 jobs in parallel
   (`bcftools norm -r chrN` on an indexed `.vcf.gz`, then `bcftools concat` or plain
   concatenation in order). Count the whole pipeline (the concat, and say whether the index has
   to be built first and what that costs). Check that the split output is the same records as
   the single run; say so if it isn't.
3. **Memory:** peak resident size for each run above.

Inputs (all under `data/`): HG002 chr22, HG002 whole genome (`.vcf` and `.vcf.gz`), the
scrambled indels (`data/scr.vcf`), the 1000 Genomes chr22 `.vcf.gz` (cohort; per-chromosome
splitting gives nothing on one chromosome, so say so, or split by region if that's a fair and
common practice and you can check the output), compressed output with its index (`-Oz -W`),
and `-m -any` on HG002 whole genome. Also re-measure the known weak cases briefly (rewritten
records with INFO/END, the many-ALT `-m` line) only if the README keeps a sentence about them;
`docs/USAGE.md` already has their figures.

## Rules

- Under `flock data/tmp/bench.lock`, `nice -n 19`, `taskset -c 0-15` (performance cores) for both
  tools, a `timeout`, interleaved, at least 3 rounds; BEND_NO_TELEMETRY=1. Cap memory with
  `systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0` (the machine has 30 GB).
- Write outputs to a file on the SSD (e.g. `data/tmp/bench/`), not `/tmp`, which is tmpfs (RAM)
  here; reviewers found the scrambled file's result depends on it. Make `test/bench.sh`'s
  default and its comment match what the README says.
- Build framebender from main with `./build.sh data/tmp/bench/framebender`.
- Keep any new script in `test/` small and documented like `test/bench.sh` (e.g. the
  per-chromosome bcftools pipeline), so a reader can repeat it.

## The README section

Short and plain, for scientists and Bend people who have never seen the project:
- the setup in two or three lines (machine, versions, how it was run; details to a new
  `docs/BENCHMARK.md`, which may hold the full tables and method);
- one compact table: input, bcftools 1 core, framebender 1 core, bcftools per chromosome on 16,
  framebender 16, with peak memory (in the same table or a second small one);
- where framebender is good and where it isn't, in a few bullets (slower or more memory on X,
  linking USAGE for the weak cases);
- keep the correctness paragraph (same records as bcftools, the intentional differences) to two
  or three sentences.
Remove what no longer earns its place. No marketing words. Numbers are ranges over the rounds.

Work on a branch `bench` in this checkout. Commit; don't push, don't merge. End with a short
report: the tables, what changed in the README, and anything surprising.
