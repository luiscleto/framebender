# Round 2 of the speed review (346768b): ACCEPT, with two minor items

Decisions 1–4 are carried out and fix what I found in round 1. The output is still byte-identical to main's build on all my inputs, and the new USAGE and README text is true except for one README point.

**Laws:** still no change to the law files, `PROOF.bend`, the driver, `test/`, `check.sh` or `build.sh` (`git diff main 346768b`). This round's commits change `norm.bend` (the phantom guess), `NR.want` and four proof files. None adds a TODO, `unsafe`, assume or admit. The phantom can be any value and the output stays correct, so this round's risks were speed, memory and the docs.

**Same output:** 594 of 594 runs byte-identical (stdout, stderr, exit code), with no timeouts. That is all of round 1's inputs (some regenerated with the same seeds), plus h200, w30k, w5k, and new files whose every line has a large allele: 1 MB deletions, 1 MB insertions, 100 kb and 10 kb.

**Decisions 1 and 2** (wall s / peak MB, main and 346768b interleaved, 3 rounds unless noted):

| input | main | e7b (round 1) | 346768b |
|---|---|---|---|
| `sub.vcf`, `--threads 1` | 0.49–0.52 / 38–42 | 0.58–0.63 / 49–52 | **0.45–0.47 / 38–39** |
| `sub.vcf`, default | 0.156–0.159 / 247 | 0.168–0.175 / 284 | 0.153–0.156 / 238 |
| cohort, `--threads 1` | 0.145–0.159 / 51 | 0.19–0.21 / 51–55 | 0.150–0.159 / 50–51 |
| cohort, default | 0.068–0.070 / 239 | 0.077–0.080 / 280 | 0.069 / 238 |
| cohort `-m -any`, `--threads 1` | 3.44–3.71 / 75 | 4.71–5.13 / 77 | 3.43–3.57 / 75 |
| cohort `-m -any`, default | 1.02–1.07 / 356–362 | 1.16–1.17 / 362 | 0.89–0.90 / 324 |
| w30k `-m -any`, default | 11.8–12.0 / 862–870 | 11.5–11.7 / 986–992 | 11.5–12.4 / **855–857** |
| w30k `-m -any`, `--threads 1` (2 rounds) | 12.1–13.0 / 802 | 12.0–13.0 / 932–936 | 12.0–12.9 / 800 |
| h200 `-m -any` (both thread counts) | 2.27–2.40 / 958 | 2.00–2.12 / 574 | 2.04–2.15 / 702 |
| scr (5 rounds) | 0.104–0.114 / 93 | 0.063–0.069 / 117 | 0.060–0.069 / 115 |
| scr30 | 0.68–0.69 / 250 | 0.19 / 243 | 0.19–0.20 / 243 |
| 1000 Genomes chr22 `.vcf.gz`, default (2 rounds) | 5.78–5.85 / 327–330 | 5.79–5.81 / 414–420 | 5.95 / 316–323 |
| same, `--threads 1` (2 rounds) | 8.6–8.8 / 104 | 9.1–9.5 / 104 | 7.9–8.1 / 105 |

HG002 chr22 at `--threads 1` matches main's within noise (0.091–0.096 s against 0.087–0.095 s).

**Decisions 3 and 4 (docs), checked against measurements:**
- **USAGE, END on rewritten records:** "3.5 s with an END on every record, against 0.08 s without". I measured 3.42–3.69 s and 0.060–0.069 s.
- **USAGE, many-ALT `-m` line:** "7.5 s with 325 ALTs" and "bcftools: 6.5 s". I measured 7.4 s on 346768b and 6.4 s for bcftools on 1,300 ALTs.
- **USAGE, `-m` memory:** h200 at 0.70 GB matches the 702 MB I measured.
- **README:** the 1000 Genomes memory (315 MB, and 105 MB at `--threads 1`) matches my 316–323 and 105 MB. The whole-genome figures (340 MB, and 58–59 MB at `--threads 1`) I could not run, under the rules; the e7b and 346768b `--threads 1` memory on scr and the cohort fits them.
- **README's new clause** ("a file whose rewritten records carry an INFO/END is still slower than bcftools") is true on my END scramble: bcftools takes 0.052–0.060 s there, framebender 3.4–3.7 s.

## Findings

1. **Minor: the phantom guess decodes the first line's REF and ALT into Strings, which costs about 30% when alleles are around 1 MB.**
   - **Where:** `norm.bend`, `plan.ph.if` → `plan.ph.ref`/`plan.ph.t5` (`Q.text`), then `plan.est`/`plan.trim` (`String.reverse`, `plan.pre`). This runs once per piece.
   - **Input:** `chr22` lines that are each a 1 MB deletion or a 1 MB insertion (`/tmp/fbrev/gen/gen_bigref.py`, 40 lines, `-c w`):

     | input | main | e7b | 346768b |
     |---|---|---|---|
     | 1 MB deletions, default | 2.36–2.91 s | 2.33–2.40 s | 2.96–3.09 s |
     | same, `--threads 1` | 3.56–3.99 s | 3.51–3.92 s | 4.31–4.39 s |
     | 1 MB insertions, default | 1.68–1.77 s | 1.73–1.81 s | 2.31–2.42 s |
     | same, `--threads 1` | 2.00–2.06 s | 2.04–2.14 s | 2.52–2.83 s |

     Memory is unchanged. At 100 kb alleles the cost is within 5% of main, and at 10 kb there is none.
   - **Fix:** skip the guess (phantom = POS) when the REF and ALT bytes (`t5 - t3`) exceed a small bound such as 4 KiB. The tab offsets give that size before any decoding, and any phantom is correct, so no proof statement changes.

2. **Minor (docs): the README's scrambled-indels row and clause now read as a tie with bcftools.**
   - **Where:** README, the row "HG002, 20,739 indels moved…", which now reads 0.07–0.09 s for bcftools and 0.08–0.09 s for framebender. The rewritten clause also no longer says that files where nearly every record needs rewriting are slower.
   - **Input:** `data/scr.vcf -c w`, framebender and bcftools interleaved, 5 rounds each: framebender 0.060–0.069 s, bcftools 0.047–0.052 s. framebender is still about 1.3× slower; scr30 is the case where it wins.
   - **Fix:** re-measure that row with the two tools interleaved. Either keep both clauses ("nearly every record rewritten: somewhat slower; with INFO/END on them: much slower") or mention scr30.

Outside this branch: I did not reproduce the segfault on `ph30` with `-w 100000000`. It is a crash in the trusted part and also happens on main's build, so it is worth its own issue.

The worktree and main's checkout are clean (`git status`). My inputs, builds and logs are in `/tmp/fbrev`, which takes 1.3 GB; `/tmp` hit its quota once during this review.
