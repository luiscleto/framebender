# Round 3 of driver review 11 (`speed` at 813b394): ACCEPT

Decisions 6–8 are carried out, and nothing in 8646585..813b394 should block merging `speed` to main.

**1. Decision 6 is done, and the 1 MB alleles now run as fast as on main.**
- **Code:** `plan.ph.t4` finds the tab after ALT first. The guess runs only when REF, ALT and the tab between them take at most `plan.big()` (4096) bytes; otherwise the stand-in key is POS. REF's reversal and length are computed once (`plan.est.n`), and `plan.trims` stops at a trim of 0. The size test cannot wrap, because the tabs come in order. `proof_e_task_buf.bend` only follows the new code (`PHI`, `OKP`, `ph_b`). The diff adds no TODO, `unsafe`, assume or admit, and changes no law, driver, test or build file.
- **Timings:** 3 rounds, interleaved, under the lock with `nice -n 19` and a timeout, `-c w`, wall seconds. Peak memory is the same on all three builds.

  | input | main | 346768b (round 2) | 813b394 |
  |---|---|---|---|
  | 1 MB deletions, default | 2.68–2.76 | 3.29–3.73 | 2.71–2.93 |
  | same, `--threads 1` | 3.94–4.25 | 4.82–4.94 | 3.96–4.29 |
  | 1 MB insertions, default | 1.76–1.90 | 2.46–2.68 | 1.78–1.95 |
  | same, `--threads 1` | 2.11–2.39 | 3.03–3.20 | 2.10–2.26 |
  | new: about 8,000 deletions with REF+ALT of 4,085–4,100 bytes, which straddle the bound, default | 0.29–0.35 | 0.30–0.35 | 0.30–0.36 |
  | same, `--threads 1` | 1.07–1.11 | 1.06–1.14 | 1.06–1.18 |

  The machine's load was 2.8–4 from other work (a `bend` check and two watch scripts), so the times are a little higher than in round 2. The comparison between builds still holds, because the runs were interleaved.
- **Same output:** 234 of 234 runs are byte-identical to main's build in stdout, stderr and exit code, with no crashes or timeouts. The inputs were the new 4 KiB file, scr, the END scramble, END corner cases with CRLF, a sparse file, a gVCF file, an unsorted scramble and two `-m` files, each with its full option set. Also bigdel, bigins, the 100 kb and 10 kb alleles, scr30, big1, big3, h200 and w30k with the short set.

**2. Decision 7: the README's wording is fair.**
- **To /dev/null:** 5 rounds, interleaved. bcftools took 0.050–0.061 s and framebender 0.065–0.076 s. The README's "0.06 s against 0.05 s" matches, given this run's load.
- **To a file on `/tmp`:** bcftools took 0.056–0.066 s and framebender 0.070–0.077 s. framebender is still slower there, but `/tmp` is in RAM on this machine (tmpfs), so that is not a disk. The rules let me write only under `/tmp`, so I could not repeat fb-fix11b's run to a file on disk (its 0.066–0.087 against 0.064–0.082 s). Everything I measured agrees with "slower when not written to disk".
- **scr30:** to a file, framebender took 0.24–0.28 s and bcftools 0.51–0.58 s; to /dev/null, 0.21–0.24 against 0.46–0.52 s. That matches "0.21 s against 0.51 s".
- **Optional wording nit (minor):** "How it was measured" says only "writing to a file", and `test/bench.sh` writes to `$TMPDIR`, which is `/tmp` by default. Where `/tmp` is in RAM, as here, someone repeating the scrambled row gets the slower figure. Writing "to a file on the SSD" would close that gap.

**3. Decision 8:** the USAGE bullet's new figures (75 s and 1.4 GB, 7.4 s and 0.26 GB; bcftools 5.0 s and 0.64 GB) are the ones in the fb-fix11b timing table. I did not re-run the 100,000-sample line.

**4. Nothing blocks the merge.** The only change to the program is the phantom guess, and the output is correct whatever the stand-in key is. The segfault that fb-fix11b recorded on `sub.vcf -w 100000000` happens on main's build too (I did not reproduce it), so it belongs in its own issue in the trusted part, not on this branch.

Both checkouts are clean. The only untracked file in the worktree is `reviews/gpt-driver11-r3.md`, which another reviewer wrote. My builds, inputs and logs are in `/tmp/fbrev` and take 1.4 GB.
