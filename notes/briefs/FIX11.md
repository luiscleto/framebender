# Brief: driver review 11's fixes (fb-fix11)

Read `notes/briefs/SPEED_COMMON.md` first (same rules: no law change, the gate, byte-identical
output against main's build, timings under the bench lock). The reports are
`reviews/claude-driver11.md` and `reviews/gpt-driver11.md`; nobody found a law change or an output
difference. Fix these, in this order:

1. **Plain and `-m` cohort files got slower** (both reviewers). fb-rewrite's high stand-in key
   (`plan.first`, 71c4554) makes every task stop at its first write and run again, and its 64 KiB
   first-run buffer (`task.start`/`task.run1`, 3a3c539) adds memory on the second run:
   - `data/kg/sub.vcf -c w`, `--threads 1`: main 0.48-0.50 s / 32 MB, speed 0.59-0.63 s / 46 MB;
     default 0.168 s / 224 MB against 0.188 s / 265 MB (Claude; about 0.6 ms per piece).
   - `data/tmp/split/gen/cohort.vcf -c w -m -any`, `--threads 1`: main 3.57-3.77 s, speed
     5.18-5.24 s; default 1.10-1.18 against 1.24-1.34 s (GPT; restoring the old key alone gave
     3.82-3.85 s).

   Remove the cost while keeping fb-rewrite's gains on sparse and scrambled files (scr 0.06 s,
   scr30 0.20 s). Leads: start from the old key and take the high one only for a task whose merge
   was refused (or only for a sparse piece, where `plan.two` already tells), or let the second run
   reuse the first run's buffer. Profile before choosing.
2. **`NR.want` raises memory on w30k** (Claude): `data/tmp/memory/w30k.vcf -c w -m -any`, main
   820-876 MB, speed 950-1006 MB, at every thread count; time unchanged. Above 64 MiB a buffer
   grown to exactly its size grows again soon and parks a block in each size. Try a growth factor
   above 64 MiB (1.5n, or 2n up to 256 MiB) and keep what is best on w30k, w30, w5 and h200 (h200
   must stay well under main's 953 MB).
3. **Docs**, after 1 and 2, with your own measurements:
   - `docs/USAGE.md` "Speed and memory": a record that is rewritten and carries INFO/END, and a
     BAD_END line under `-c w`, still take the slow path (scr with END on every record: 3.5 s
     against 0.07 s); and under `-m`, one line with very many large records (1,300 ALTs x 100,000
     samples) is quadratic in the sorting buffer and may look like a hang.
   - `README.md`: the scrambled-indels row (now about 0.07 s), and the memory figures
     (`--threads 1` and default for HG002 whole genome, the 1000 Genomes line) re-measured. Keep
     the README's shape and length; a full rewrite of the results comes later.

**Measure** before and after, interleaved with main's build and bcftools: `sub.vcf`, the cohort
with and without `-m` (`--threads 1` and default), HG002 chr22 and whole genome (`--threads 1` and
default, time and peak RSS), scr, scr30, w30k, w30, w5, h200.
