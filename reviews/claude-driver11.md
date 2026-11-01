# Review of `speed` at e7b93db

No blockers: the proof side is clean, and the output was byte-identical to main's in all 630 runs. There are two measured regressions to fix (one in speed, one in memory) and some stale or missing docs.

**1. Laws:** nothing found.
- `git diff main speed` touches none of LAWS, MACHINE, types, run, tan, `docs/LAWS.md`, `PROOF.bend`, `main.bend`, `io64.*`, `check.sh`, `build.sh` or `test/`.
- The counts of TODO, unsafe, assume and admit in `proof_*` and `norm*` are the same as main's (the TODOs are comments).
- The new `law`s in the proof files are lemmas, each with its own proof (for example `want_ge` at `proof_b_run_num.bend:93`).

**2. Same output:** 630 runs of main's build against this one: stdout, stderr and exit code identical in all of them. The inputs:
- **END:** valid END; corner cases (off by one either way, 0, a leading zero, 9 and 10 digits, U32 overflow, `.`, a bare `END`, two END entries, `end=`/`END2`/`XEND`); END first, middle or last in INFO; LF and CRLF; END on scrambled records.
- **gVCF and out of scope:** `<NON_REF>` blocks, `,<NON_REF>`, `*`, `.`, `<DEL>`, breakends, lowercase, N.
- **Refused `-m` lines:** every refusal code; every line refused; a refused first line on each contig.
- **Scrambles and boundaries:** scr with 1, 3 and 30 copies; UNSORTED across a piece boundary.
- **Sparse pieces:** spans of under 2, 2 to 4 and over 4 times `ahead()`; records at and past the contig end.
- **Buffers:** big-line `-m` files whose first split record is over 64 KiB; h200, which crosses 64 MiB; w30k and w5k.
- **Options:** `-c e` and `-c w`, `--threads 1/2/3/16/128`, `-w 1/50/100000/100000000`, and `-m -any/-both/-`.

## Findings

1. **Should fix: plain cohort files got slower and use more memory.**
   - **Where:** `norm.bend`, `plan.first` (the high phantom, commit 71c4554) and `task.start`/`task.run1` (the 64 KiB first-run buffer, commit 3a3c539).
   - **Input:** `data/kg/sub.vcf -c w`. I built the intermediate commits to find which one caused it:

     | | main | cfe6846 | 71c4554 | speed |
     |---|---|---|---|---|
     | `--threads 1` | 0.48–0.50 s / 32 MB | 0.45–0.47 s / 31 MB | 0.61–0.64 s / 33 MB | 0.59–0.63 s / 46 MB |
     | default | 0.168–0.170 s / 224 MB | — | 0.19 s / 219 MB | 0.188–0.190 s / 265 MB |

   - **Reading:** the added time works out to about 0.6 ms for each of the cohort's ~230 pieces. That looks like a fixed cost per task, now that every task runs twice. HG002 chr22 hides it: it has few pieces and costs more per piece.
   - **Fix:** profile the extra per-task cost (my guess is the piece handed back between the two runs, and a fresh buffer for the second run) and remove it. Two possible ways: let the second run reuse the first run's buffer, or start from the old phantom and take the high one only after a refused merge. Then re-measure the cohort and HG002 at `--threads 1`.

2. **Should fix: `NR.want` raises memory on the w30k shape.**
   - **Where:** `norm_run.bend`, `want`/`room.if` (commit ff49b8b).
   - **Input:** `data/tmp/memory/w30k.vcf -c w -m -any` (1,000 lines, 2,000 samples, 30 ALTs).
   - **Measured:** main 820–876 MB, ff49b8b and speed 950–1006 MB, at `--threads 1`, the default and 16. Time is unchanged. h200 does improve (953 → 570 MB).
   - **Likely cause:** above 64 MiB, a buffer grown to exactly its size grows again soon, leaving a block parked in each size it passes through.
   - **Fix:** use a growth factor above 64 MiB (for example 1.5n, or 2n up to 256 MiB), then re-measure w30k, w30 and h200.

3. **Should fix (docs): the README memory figures are out of date.**
   - **Where:** README, the `--threads` memory table (`--threads 1`: 44–48 MB; default: 330 MB) and the 1000 Genomes line (310 MB, and 100 MB with `--threads 1`).
   - **Why:** fb-rewrite's own figures for the whole genome are 65 MB and 340 MB (`notes/speed.md:511-521`, the 8 MiB half windows). Here, scr at `--threads 1` went from 38 to 58 MB and the cohort as in finding 1.
   - **Fix:** re-measure after findings 1 and 2, and update both.

4. **Should fix (docs): END on a rewritten record is a slow case nobody mentions.**
   - **Where:** README's "is still slower than bcftools" clause, and USAGE.
   - **Input:** scr with a valid END on every record: 3.5–3.6 s, against 0.07–0.08 s for scr without END (main: 8.4–8.6 s).
   - **Fix:** say that records that need rewriting and carry INFO/END take the slow path, as do BAD_END lines under `-c w`.

5. **Should fix (docs): `-m` with very many large records per line may never finish.**
   - **Where:** USAGE, the "Speed and memory" note under `-m`.
   - **Input:** the shape in `notes/speed.md:656`: one line with 1,300 ALTs and 100,000 samples (quadratic in `NR.mid`).
   - **Fix:** add one bullet saying this, so a run like that is not taken for a hang.

6. **Minor: README's scrambled-indels row is out of date.**
   - **Where:** README results table, "HG002, 20,739 indels moved…": framebender 0.12–0.13 s.
   - **Measured:** speed 0.069–0.082 s, main 0.109–0.115 s.
   - **Fix:** update the row.

7. **Minor: fb-end costs about 4% at `--threads 1` on plain files.**
   - **Input:** HG002 chr22 at `--threads 1`: main 0.089–0.092 s, speed 0.093–0.096 s.
   - **Fix:** accept it, as `notes/speed.md` explains; fold it into the re-measured README figures.

## Checked and fine
- **Size limits:** `want` never overflows (2n only below 64 MiB), and `depth` caps blocks at 2^31. Each half window is at most 8,323,071 letters, under 8 MiB. The rewrite buffer and the sorting buffer's tail are made at their size. The 64 KiB first-run buffer grows correctly (big1, big3: identical output).
- **Double split under `-m`:** the risk I raised in the plan, each piece's first line being split twice, did not show up. big2 (2 MB lines, one or two per piece) is within about 3% of main.
- **USAGE's `-m` figures hold:** h200 uses 570 MB. Refused lines go through at about the speed of lines that split (all refused: 0.41 s, against main's 37.6 s).
- **The fb-end and fb-refuse speedups are real:** gVCF blocks 0.92 → 0.12 s, HG002 chr22 with END 1.05 → 0.057 s, scr30 0.68 → 0.19 s.

Not run: the whole-genome files, the full `PROOF.bend` check, and a refused line near 2^28 bytes. Both checkouts are clean (`git status`). The builds, generators and logs are in `/tmp/fbrev` (774 MB). `/tmp` hit its per-user quota partway through, so I deleted large outputs from earlier runs, all of them mine.
