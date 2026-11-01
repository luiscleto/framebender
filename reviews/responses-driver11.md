# Driver review 11: the speed phase (responses)

Prompt: `reviews/DRIVER11_PROMPT.md`, on `speed` at e7b93db. Reports: `claude-driver11.md`,
`gpt-driver11.md`, `grok-driver11.md`.

All three: no law, spec, driver or test file changed; no new TODO, `unsafe` or assumption in the
proof; output byte-identical to main's build on their own inputs (Claude 630 runs, GPT 828, Grok
218 plus chr22, scr, the cohort and w30k); no buffer size can wrap (`NR.want` doubles only below
64 MiB, blocks stop at 2^31 bytes, the half windows are under 8 MiB). The lead ran `check.sh`'s
steps on 46e6d06 (`PROOF.bend` checks with `--check-only` and `--verdict`) and the output suites
against main's build (same 128, par 312, threads 2128, out, index, split 80): all identical.

| # | finding | by | decision |
|---|---|---|---|
| 1 | fb-rewrite's high stand-in key (`plan.first`) makes every task stop at its first write and run again, and the 64 KiB first-run buffer adds a second buffer: cohort `-m -any` at `--threads 1` 3.6 -> 5.2 s, `sub.vcf` 0.48 -> 0.61 s and 32 -> 46 MB, default threads 12-15% slower and about 40 MB more | all three (GPT and Claude bisected it to 71c4554 and 3a3c539) | **Fix** (fb-fix11, `notes/briefs/FIX11.md`): remove the cost, keep scr's and scr30's gains. |
| 2 | `NR.want` grows a buffer to exactly its size above 64 MiB, so a buffer that keeps growing parks a block at each size: w30k 820-876 -> 950-1006 MB, time unchanged | Claude, Grok | **Fix** (fb-fix11): a growth factor above 64 MiB; h200 stays well under main's 953 MB. |
| 3 | USAGE leaves out two slow cases the notes name: a rewritten record with INFO/END and a BAD_END line under `-c w` take the String path (scr with END: 3.5 s against 0.07 s); one `-m` line with very many large records is quadratic in `NR.mid` and can look like a hang | all three | **Fix** (fb-fix11). |
| 4 | README: the scrambled-indels row (0.12-0.13 s; now about 0.07 s, still behind bcftools' 0.05) and the memory figures (fb-rewrite's windows: whole genome 65 MB at `--threads 1`, 340 MB at the default) are out of date | all three | **Fix** (fb-fix11), re-measured after 1 and 2. The full rewrite of the results section comes after the speed phase. |
| 5 | fb-end costs about 4% at `--threads 1` on plain files | Claude | **Accept**, as decided when it was merged (gVCF and END files 7-20x faster); stated in the re-measured figures. |
