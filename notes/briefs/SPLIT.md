# Splitting multiallelic records: brief for the split agent (phase I)

Goal: `framebender norm -m -any -f ref.fa in.vcf`, as `bcftools norm -m -any -f ref.fa` does:
a record with several ALTs becomes one record per ALT, each then normalized. Pipelines usually
run bcftools norm this way (annotation tools such as VEP expect one ALT per record), so this is
what framebender lacks to replace it in practice. The owner chose it as the next feature.

This changes the science layer (what the output is), so the laws come first and go through the
three-model review before any code. The owner is not a geneticist: every law needs a plain
statement a biologist can check, and the notes must explain the genetics terms they use.

## What exists

- The science layer: `types.bend` (records, fields, `B.Args.parse`), `LAWS.bend` (the normal form
  of one variant, `judge` for one line, `run` for the whole file and its laws), `run.bend`,
  `tan.bend`. `docs/LAWS.md` explains them in plain terms. Today a record with several ALTs is
  normalized as one variant (`same_change` keeps the alternatives in order), as bcftools does
  without `-m`.
- The contract: `MACHINE.bend` (`law machine`: the program writes exactly `run`), with
  `law threads` and `law output` for options that never change the text.
- The implementation (`norm*.bend`, on packed bytes with the `lawful-*` packages from BendHub)
  and its proofs (`proof_*.bend`, `PROOF.bend`). `docs/DEVELOPMENT.md` has the layout and tests.

## Steps

1. **Find out exactly what bcftools 1.24 does, by experiment** (`bcftools norm -m ...` on small
   files you write in `data/tmp/split/`). At least:
   - `-m -any`, `-snps`, `-indels`, `-both` (the default type), and the `+` forms (joining);
   - the order: split, then normalize each new record, then sort; what `-w`/`--site-win` does;
   - FORMAT/GT: what a sample's genotype becomes in each split record (`1/2`, `0/2`, `2/2`,
     phased `1|2`, haploid `2`, missing `.`/`./.`, partly missing), `--multi-overlaps`;
   - INFO and FORMAT fields by header `Number`: `A` (one value per ALT), `R` (one per allele,
     REF included), `G` (one per genotype: diploid and haploid orders), fixed numbers, `.`; a
     tag missing from the header; a field with the wrong number of values; `--keep-sum`;
   - ID, QUAL, FILTER, INFO/END; symbolic and `*` alleles among the ALTs; a duplicate ALT;
     records already biallelic; what gets reported on stderr.
   Write the findings as a table in `notes/split.md`, each with the command that shows it.
2. **Design and draft the laws; then stop.** Propose in `notes/split.md`:
   - the scope: which `-m` forms to accept now (at least `-m -any`, `-m -both`), and whether
     joining (`+`) is in or out now, with the reasons; where framebender should differ from
     bcftools and why (stopping instead of guessing is its usual choice, as for unsorted input);
   - the definitions and laws, as an exact diff to `types.bend`, `LAWS.bend` and `run.bend`,
     minimal and in their style. What a law could say, for the reviewers to weigh: the split
     records together make exactly the input's change, one ALT each, in ALT order; each split
     record then gets the normal form (so `same_change` ... `unique` apply to each); a sample's
     genotype in each record names the same alleles the input genotype did for that ALT, under a
     stated rule; per-allele fields take the values of their allele; without `-m`, the output
     is as today. Say in plain terms what information splitting loses (a `1/2` genotype becomes
     two records that no longer say both ALTs were on one chromosome pair);
   - how `run` changes (one input line may give several items; sorting, `-w`, UNSORTED);
   - `law machine`'s statement stays as it is if `run` absorbs the change; say so or say why not;
   - the plan for the implementation and the proofs, and the expected size of the work;
   - the tests: identical records to bcftools on HG002 and on the 1000 Genomes chr22 slice
     (`data/kg/sub.vcf`), on generated cases covering every row of your table, at every
     `--threads`; speed and memory against `bcftools norm -m -any`, which matters as much as
     correctness.
   Print the draft and stop. The lead runs the review, then sends you the outcome.
3. After the review: implement, prove, check, test, time; report and stop.

## Rules

- Work in your own worktree (`../framebender-split`, branch `split`); `data` there links to the
  main checkout's `data`. Scratch in `data/tmp/split/`; do not write other files under `data/`.
- Fixed until the review: everything except `notes/split.md`. The `lawful-*` packages are fixed
  (imported from BendHub, `lawful-x@0.1.0.0`); if you need a new law in one, say so instead.
- Approved laws are never weakened or deleted; adding definitions and laws is fine.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once).
- **Timing runs one at a time:** `flock data/tmp/bench.lock ...`, `nice -n 19`, a `timeout`,
  pinned (`taskset -c 0-15`), interleaved, ranges (`test/bench.sh`). Another agent works in
  parallel and takes the same lock. Delete each output file before the next run. Keep at least
  8 GB of RAM free.
- Shell scripts that delete files: write them to a script file with literal paths and run that.
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
