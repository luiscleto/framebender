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

## Round 2

Decisions 1-4 carried out by fb-fix11 (`notes/speed.md`, "fb-fix11"), merged in fb05255:
- 1 (0c01467): the stand-in key is a guess from the first line's REF and ALT (POS plus the bases
  trimmed off the left), so a dense piece runs once; a task runs again only when its first record
  moves left of the guess. Both runs reserve their usual room (the 64 KiB first-run buffer is
  gone). Cohort `-m` at `--threads 1` 4.93-5.07 -> 3.52-3.69 s (main 3.67-3.83), `sub.vcf`
  0.75 -> 0.60 s and 49 -> 39 MB (main 0.63-0.66 s, 39 MB); scr and scr30 keep their gains.
- 2 (deb5571): `NR.want` doubles below 256 MiB (was 64 MiB): w30k back to main's 801/849-856 MB;
  h200 700 MB (main 955). Keeping the old rule for the splitter alone (h200 575 MB) needs 150-300
  lines of proof; not done.
- 3, 4 (6b05225): USAGE's "Speed and memory" section (END on a rewritten record, BAD_END under
  `-c w`, one `-m` line with many large records, quadratic: 1,300 ALTs x 10,000 samples 121 s
  against bcftools' 6.5 s) and the README's scrambled row, slower-than-bcftools clause and memory
  figures.

fb-fix11's gate: `check.sh`'s steps pass; same 128, par 312, threads 2128, out, index, split 80
identical to main's build.

Open, outside this review: a generated `-m` file (`data/tmp/fix11/`, ph30) with `-w 100000000`
segfaulted once on main's build and on this one, and ran out a 900 s timeout on a rerun; it
predates the branch.

Round 2 reports: `claude-driver11-r2.md` (ACCEPT, two minor), `gpt-driver11-r2.md`,
`grok-driver11-r2.md`. All three: decisions 1-4 carried out and fix round 1's findings; output
byte-identical to main's (Claude 594 runs, GPT 980, Grok 218 plus the named files).

| # | finding | by | decision |
|---|---|---|---|
| 6 | The stand-in key's guess (`plan.trims`, `plan.ph.*`) decodes the first line's REF and ALT into Strings and redoes REF's length and reversal for every ALT: 100 kb REF x 500 ALTs first in a piece 1.54-1.61 s against main's 0.06 s; 1 MB alleles about 30% slower | GPT, Claude | **Fix** (fb-fix11b, `notes/briefs/FIX11B.md`): no guess (key = POS) when the first line's REF and ALT bytes exceed a small bound (read from the tab offsets, before decoding); REF's values once; stop when the trim reaches zero. Any key is correct, so no statement changes. |
| 7 | README's scrambled-indels row reads as a tie (bcftools 0.07-0.09, framebender 0.08-0.09); interleaved runs give framebender 0.060-0.069 s, bcftools 0.047-0.053 s; the clause no longer says such files are slower | Claude, Grok | **Fix** (fb-fix11b): re-measure interleaved; keep "somewhat slower" for scr and mention scr30, where framebender wins. |
| 8 | USAGE's many-ALT `-m` bullet says memory grows with time at 100,000 samples; measured 257 -> 1384 MB (5.4x) while time grows 10x | Grok | **Fix** (fb-fix11b): state the measured memory. |
