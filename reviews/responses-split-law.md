# Law review of splitting multiallelics (phase I): responses

Prompt: `SPLIT_LAW_PROMPT.md`. Round 1: Claude (`claude-split-law.md`), GPT 6.1 Sol
(`gpt-split-law.md`), Grok 4.7 (`grok-split-law.md`); none accepted. All three: the parser is
unambiguous and keeps every old `Cfg`; the genotype rule, the G index `k(k+1)/2+j` and the
haploid selection are correct; `law threads`/`output` keep their statements (their proofs gain
the two waiting states); the String path is the right first stage; keep `--multi-overlaps 0` as
the default; keep passing an unsplittable line under `-c w` (subject to 7); add `biallelic_run`.

| # | finding | by | decision |
|---|---|---|---|
| 1 | `split_format_values` is false: `sample_value` gives `Some ""` for a column the line lacks | Claude, GPT | **Fix:** `None` for a missing column (`List.get` on the fields). |
| 2 | No law says which lines split and which are refused: a splitter that never splits satisfies all 13 | all three | **Fix:** a law `split_when`: with `-m`, a non-MALFORMED line with 2+ ALTs is `Pieces` exactly when a readable predicate holds, else `Unsplit{c}` with `c` stated per case; the predicate uses a named `expected_count(num, n, ploidy)`, not `Vals.idx`. |
| 3 | The lone `.` is in the plain statements but in no law; extra values beyond the needed indexes are unconstrained (`IA=1,2,9`); only the first duplicate INFO key is observed; `gt_alleles` reads invalid text as missing, and `Pos.read` accepts `01` | all three | **Fix:** laws state: a lone `.` stays `.`; an A/R/G value has exactly the accepted count and the kept values are exactly those named; every INFO entry occurrence is covered; the output GT text is exactly the input's with each allele replaced (separators kept), and alleles are digits without leading zeros or `.`. |
| 4 | Header values are not trimmed: `Number=A ` or `, Number=A` read as Other (bcftools reads A) | Grok | **Fix:** trim spaces and tabs around each header piece, ID and Number, as htslib does; verify by experiment. |
| 5 | Haploid G is decided by the value count, not by the sample's ploidy | all three | **Fix:** the sample's GT decides: one allele, n+1 values; two alleles, (n+1)(n+2)/2; no GT key or no GT value, diploid only (VCF 4.3 §1.6.2); anything else `BAD_COUNT`. Ploidy above 2 with a G tag: `BAD_COUNT`, documented as a scope limit, not bad data. INFO G stays diploid only. |
| 6 | `split_valid` and `split_change` speak of a `B.Var`, not of the records written; true without `-m` | all three | **Fix:** restate on the text: if the line splits into `Pieces ps`, each piece reads as the variant of ALT i alone, and the records written (each normalized) together make the input's change, in ALT order. |
| 7 | Under `-c w` an unsplittable line passes even when the line would stop today (UNKNOWN_CHROM) | GPT, Grok, Claude | **Fix:** on `Unsplit`, the line first gets the outcome `judge` gives it when that outcome stops the run; only otherwise the split problem applies. |
| 8 | `A C,C` splits into records whose genotypes claim REF on a copy that carries C | Claude | **Fix:** refuse with `ALT_DUP` (as today without `-m`); list it as a difference from bcftools. |
| 9 | A missing or unrecognised `Number` is read as Other and copied: the same guess `UNDEFINED_TAG` refuses | GPT | **Fix:** copy only a fixed count, `.`, `P` and flags; a defined tag whose Number is missing or not understood, in a line to split, is `UNDEFINED_TAG`. |
| 10 | `UNDEFINED_TAG` strictness | all three | **Keep** the refusal (all three). An undefined key with no value (a flag) is copied: it has no values to share (Claude). The VCF reserved-key table (AC/AF A, AD R, PL G) is not used now; noted as a later option. The message names the tag and the fix (add a header line, e.g. `bcftools annotate -h`). |
| 11 | Empty INFO entries (`;;`, a trailing `;`) give `UNDEFINED_TAG` for key `""` | Claude, Grok | **Fix:** an empty entry is kept as it is in every record. |
| 12 | Old law statements not kept visibly | Claude, Grok | **Fix:** keep the old `items(fasta, vcf)`, add `items_without_m` (`split(o)` false: the new `items` is the old); add `biallelic_run` (no line with 2+ ALTs: `-m` changes only the header's command line). |
| 13 | `split_info_kept` says END is copied, but `judge` rewrites it | Grok | **Fix** the plain statement: the split copies the entry; the written END follows the existing END rule. |
| 14 | Speed risk of the String path; `Got.join.go` is quadratic in sample fields | all three | **Fix:** linear output construction; before the machine proofs, time an unproven prototype of the split path on a heavy synthetic cohort (GT:AD:DP:GQ:PL, 3,202 samples, dense multiallelic lines) and on the joined `sub.vcf`, against `bcftools norm -m -any`; the stage-2 decision is made then. |
| 15 | Parallel tasks need the header's `Defs`, parsed once | Grok | **Fix**, in the plan. |
| 16 | Minor: usage text (`-m -`, glued forms); summary comment ("body lines"); window explanation (`no_unsorted` is a sufficient condition); phase loss overstated (PS and order kept); table rows 10, 23 corrected; GT without a FORMAT header line kept (bcftools drops it): add to the table; VCF 4.4 leading phase `|0|1`: test htslib, document; docs: polyploid G, summary counts, one REF_MISMATCH warning per record, a worked PL example for n = 2 with ALT numbers counted from 1 | Claude, GPT, Grok | **Fix** all. |

## Round 2

Claude (`claude-split-law-r2.md`), GPT (`gpt-split-law-r2.md`), Grok (`grok-split-law-r2.md`): no
blockers; all 16 decisions carried out (Claude checked the 18 laws by hand). All three answer the
author's questions the same way: trim spaces only (htslib does not trim tabs; decision 4 is
amended to match the experiment), and keep the exact refusal code in `split_when`.

| # | finding | by | decision |
|---|---|---|---|
| 17 | GT `.` is counted as two copies, so a haploid no-call with n+1 G values is refused (and `.:0,1,2,3,4,5` splits into a one-allele GT beside 3 values) | all three | **Fix:** a GT written with one allele (`.` included) is one copy, `./.` two, and so on (one plus the separators); for a lone `.` accept either count, n+1 (one copy) or (n+1)(n+2)/2 (two copies), which never coincide for n >= 2: many writers use a bare `.` for any no-call (Claude's option; GPT and Grok preferred one copy only). No GT key or no GT value: two copies only. Update `pl_dotgt` and the plain statements. |
| 18 | `written_change`/`split_change` read every `judge` result's text, including outcomes that stop the run: not necessarily records written | GPT | **Fix:** state it for records that are written (connect through `out_items`/`run` or restrict to outcomes that do not stop), and state the ALT correspondence separately from the POS-sorted order. |
| 19 | The String path's cost is the spec's: per record it re-splits every column and looks up every key's Number | Claude | **Fix (plan):** the prototype timing compares the spec as written with a version that looks up each FORMAT key's Number once per line and splits each column once (with a small equality proof if kept). |
| 20 | `A <*>,<*>` is Skipped without `-m` but ALT_DUP with `-m`; the ALT_DUP warning under `-c w` lacks "not split" | Claude | **Fix** the wording and the warning; the refusal stays. |
| 21 | No law says a MALFORMED line with 2+ ALTs is `Whole` | Claude | **Fix:** extend `whole_biallelic` or add `whole_malformed`. |
| 22 | Under `-c w`, a line that cannot be split and has a non-stopping whole-line problem (REF_MISMATCH, BAD_END) reports only the split's code | Claude | **Document** it. |
| 23 | `split_format_values` plain wording ("any other" → two copies, no GT value, or GT `.`) | Claude | **Fix.** |

## Round 3

Claude, GPT and Grok: ACCEPT (decisions 17-23 carried out; nothing new broken).

## The CR change (2026-10-31)

While proving, the author found `twice_run` false under `-m`: a stray CR inside a comma list
(`END=5\r,6`) can end a split record in a bare CR, which reads back as a CRLF ending. The lead
kept `twice_run` whole (narrowing it needs the owner's consent) and chose to refuse such lines;
the owner agreed. Prompt: `SPLIT_CR_PROMPT.md`. Claude (`claude-split-cr.md`), GPT
(`gpt-split-cr.md`), Grok (`grok-split-cr.md`): ACCEPT. All three: `twice_run` holds again for
every input (other bytes round-trip: NUL, vertical tab, empty values; a tab cannot be inside a
value; a second CR before the LF stays in the body and is refused); the order (BAD_CR before
ALT_DUP, decision 7 first) is right; no approved law is weakened; the simple rule is the one to
approve.

| # | finding | by | decision |
|---|---|---|---|
| 24 | Lists of the split refusals leave out BAD_CR (`run`'s comment in LAWS.bend, the `Parts` comment, `notes/split.md`, `docs/LAWS.md`); the summary says refusals are only where bcftools guesses, drops or crashes | Claude, Grok | **Fix:** add BAD_CR everywhere; the summary adds "or where a record would not read back as written". |
| 25 | The plain statement: "a carriage return inside it" covers a CRLF ending, and leaves out that a whole-line outcome that stops the run is reported first | Grok, Claude | **Fix:** "a carriage return anywhere in the line other than the one just before its final LF" (so `\r\r\n` is refused); then: a whole-line outcome that stops the run is reported first, otherwise BAD_CR, then the later reasons. |
| 26 | The "why" in the differences table says too much | Claude | **Fix:** "a CR inside a line is not valid VCF; cutting a value at a CR can leave a record ending in CR, which a second run reads as a CRLF ending." |
| 27 | The comment on `Rec.parts` names BAD_CR after ALT_DUP | Claude | **Fix:** BAD_CR first; re-wrap. |
| 28 | Test the whole body (`B.Text.has_cr(body)`), not its fields | Claude | **Fix:** it matches the plain statement and the machine's byte test, and saves a lemma. |

## The step bound with -m (2026-10-31)

While proving law `machine` under `-m`, the author found that the proof's per-line read allowance
does not cover a split line's records: each record may ask for its own reads, and charging each a
full line's allowance grows with the square of the line, which `bound` does not. Proving the real
(shared-window) cost instead is a large proof with a risk of a dead end. The owner consented to
enlarging the bound with `-m` only, by (VCF length + 1)^2. Prompt: `SPLIT_BOUND_PROMPT.md`.
Claude (`claude-split-bound.md`), GPT (`gpt-split-bound.md`), Grok (`grok-split-bound.md`):
ACCEPT, with the argument in `notes/split.md` corrected. All three: the square covers the charge
for every input; `splits(argv)` agrees with the parser for every accepted spelling of `-m`,
repetitions and usage errors; keep the condition, so runs without `-m` keep exactly the approved
bound; output, messages and exit codes are untouched; `docs/LAWS.md` does not give the formula
and need not change.

| # | finding | by | decision |
|---|---|---|---|
| 29 | "R + 2k + 13 ≤ L" is false: ID, QUAL, FILTER and INFO may be empty, and the last line may have no LF (`c⇥1⇥⇥A⇥C,G⇥⇥⇥` is 13 bytes) | Claude, GPT, Grok | **Fix:** measure lines as the proof does (n = text + 1, Σn ≤ V+1, Σn² ≤ (V+1)²) with R + 2k + 8 ≤ text; 2aR ≤ n²/4 and a ≤ n/2 still hold. |
| 30 | The existing term (V+1)(F+3) is already spent in full (wants (V+1)(FM+2), hand-outs V+1); the draft spends it again | Claude, Grok, GPT | **Fix:** charge the displaced hand-outs to the square too. |
| 31 | The output step uses "a record is at most its line + 22 bytes", which no proof has; `out_len` allows 21(n) per record and counts output twice on a stop | Claude | **Fix:** redo the step with the proof's constants and add the lemma that a split record's text is no longer than its line's. Total extra ≤ (V+1)²/3 + 13(V+1)/12 when the file has a line: about 3× margin, not 3.9×. |
| 32 | The example cannot split: 100 one-base ALTs repeat (ALT_DUP) | GPT | **Fix:** use GPT's (REF of 100 A's, ALTs `A,C,G,T,N,AA,AC,AG,AT,AN`: 2460 against 2363). |
| 33 | `splits` as drafted does not compile (Bend cannot match on a call) | GPT | **Fix:** `splits.of(B.Args.parse(argv))`. |
| 34 | Which lines' records to charge | Claude, Grok | **Proof plan:** charge 1 + k allowances for every candidate line (`-m`, not malformed, 2+ ALTs), split or not; overcharging a refused or passed-through line is harmless. |
| 35 | The comment's sentence: "a line's reads" names the FASTA-sized allowance, which the square does not pay | Grok, Claude | **Fix:** "With -m, plus (VCF length + 1) squared, so that each record of a split line (one per ALT) can be charged a line's allowance." |
| 36 | A smaller term (half the square) also fits | Grok | **Keep the full square:** Claude's corrected total is a third of it, so half would leave a thin margin, for no gain in a proof-only bound. |

The arithmetic is checked by the kernel when the budget proofs close; no second round.
