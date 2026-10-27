# Making framebender competitive with bcftools: brief for the fast agent

Read `PROVING.md` (layout, Bend proof notes), `notes/speed.md` (what the last speed pass learned)
and `NOTES.md` sections "Where the time goes", "CPU threads and the GPU" and "Raw speed".

## Goal

Make `framebender norm` as fast as possible on real data, ideally comparable to `bcftools norm`,
while every law stays proven (`./check.sh` green: bend and `--verdict`) and the output stays
byte-identical. The laws are now in two layers: the science files (`LAWS.bend`, `types.bend`,
`run.bend`, `tan.bend`) and the implementation contract (`protocol.bend`, `MACHINE.bend`) are
frozen: never edit them. The implementation (`norm.bend`, `norm_line.bend`, and any new code files)
is yours to redesign, and so are the implementation proofs (`proof_machine*.bend`,
`proof_window*.bend`, and new ones). The protocol allows batching: one `P.Ask` may carry any number
of reads, answered together. The program may call science definitions, or use its own faster
versions proven equal to them.

## Numbers (2026-10-27; 32 CPU threads; all single runs, re-measure before relying on them)

- GIAB HG002 chr22 (50,284 records, 35 MB): framebender 14.0 s; bcftools 0.08 s.
- Whole genome (`data/hg002.all.vcf`, 4,048,342 records, 2.8 GB, `data/hg38.fa`): bcftools
  6.5 s to /dev/null (8.8 s writing a file); framebender would take about 19 min at the chr22 rate.
- One pass over the chr22 bytes as `List<U32>` costs 0.15 s; as a Bend String 0.32 s; split into
  lines and fields 4-5 s. Text processing as linked lists of Chars is the cost, not Bend itself.
- Judging lines in parallel halves (`a b = f(x) g(y)`) scaled about 2x on 32 threads; the
  sequential parts (splitting into lines, joining output) limited it. The GPU does not fit (stack
  depth of 1,000-2,000 calls per lane; 10x slower than the CPU on short lines).
- The sorting buffer is about a third of the current time (`-w 1` vs default).

## Ideas (yours to judge)

- Batch: for a piece of the VCF, ask all its lines' reads in one `P.Ask`, then judge all lines in
  parallel (balanced fork-join over the lines), then do the sequential bookkeeping.
- Parse each line once, with as little allocation as possible; write unchanged lines as they came.
- Make the line splitting and the per-line work of a large piece parallel (split the piece at LFs
  into balanced parts).
- Cheaper buffer items (the buffer holds about 140 records as Char lists at the default `-w`).
- The driver (`main.bend`) is the lead's, and its piece size is 64 KB today; ask the lead (in your
  final report, or by stopping) if you need it changed (piece size, parallel conversion).

## Rules

- Output byte-identical: `test/compare.sh data/chr22.fa data/hg002.chr22.vcf` and
  `test/compare.sh data/chr22.fa data/scr.vcf` give 0 differing records,
  `test/compare.sh test/edge/ref.fa test/edge/sorted.vcf` exactly 1 (the `<DEL>` record).
- You are the only one who benchmarks; the lead may run short correctness tests. Time with
  `nice -n 19` and a `timeout`; before/after numbers from back-to-back runs. Run the whole-genome
  file only when chr22 is under about 2 s.
- Build: `timeout 1200 env BEND_NO_TELEMETRY=1 nice -n 19 bend main.bend -o framebender`. The
  driver reads `+RTS --threads N`.
- No git commits (the lead commits). Keep `notes/fast.md`: each change, time before/after, proof
  cost. Stop when the remaining ideas each save less than about 10%, or after about four hours,
  and report.
