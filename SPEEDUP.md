# Making framebender faster without losing the proofs: brief for the speed agent

Read `PROVING.md` first (project layout, Bend proof notes, rules). Every law in `LAWS.bend` is now
proven: `./check.sh` prints ALL PROOFS CHECK twice (bend, then the Lean-backed `--verdict` kernel).
Your job: make the tool faster on real data while `./check.sh` stays green.

## Measurements so far (GIAB HG002 chr22, 50,284 records)

- framebender 22.5 s; bcftools 0.08 s. Build: `timeout 1200 env BEND_NO_TELEMETRY=1 nice -n 19 bend
  main.bend -o framebender`. Time: `time (nice -n 19 ./framebender norm -c w -f data/chr22.fa
  data/hg002.chr22.vcf > /dev/null 2>&1)`.
- Floor: splitting the file into lines and fields once costs about 4 s (text is a list of Chars).
- 50,000 reference reads cost 1.1 s (not the problem).
- The sorting buffer costs about 7 s at the default `-w 100000` (`-w 10`: 20 s total).
- `Rec.stale` searched INFO four times on every record (`&&` evaluates both sides): fixed by the
  lead with a match (29.6 s to 22.5 s). `Bool.pick`, `&&` and `||` are strict: both sides run.
- Each body line is split into fields about four times: `judge_in(NoAns)` (parses, then answers None
  for every in-scope record), `judge_in(Known)`, the machine's `want` and `body_done`. `Info.end_ok`
  splits INFO on ';' and each piece on '=' (`Info.key`) for every record. `run.bend`'s
  `take_ready`/`drop_ready` compute the recursive call eagerly even when the item is not ready.

## Rules

- Never change what a law states, `LAWS.bend`'s laws, `examples.bend`, or the behaviour: output
  must stay byte-identical. Check with `test/compare.sh data/chr22.fa data/hg002.chr22.vcf`,
  `test/compare.sh data/chr22.fa data/scr.vcf` (0 differing records each) and
  `test/compare.sh test/edge/ref.fa test/edge/sorted.vcf` (exactly 1: the `<DEL>` record).
- Code files (`norm.bend`, `norm_line.bend`, `norm_var.bend`, `main.bend`) may change freely.
- Spec files (`types.bend`, `run.bend`, and definitions in `LAWS.bend`) may only get rewrites that
  compute the same function (e.g. a strict `Bool.pick`/`&&` turned into a lazy `match`), and only
  if every proof is re-established. List each such rewrite in your notes with the reason.
- Update the proofs (`proof_*.bend`) as needed; `./check.sh` must end green. Use `nice -n 19` and a
  `timeout` for every check, build and benchmark.
- No git commits (the lead commits). Keep `notes/speed.md`: each change, the time before/after, and
  what it cost in proof work (research data for "what does it cost to change proven code").
- Stop when the remaining ideas would each save less than about 10%, or after about three hours,
  and report.
