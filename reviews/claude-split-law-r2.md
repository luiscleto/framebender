# Law review, round 2: splitting multiallelic records

**No blockers. I'd accept once items 1 and 2 are settled.** All 16 decisions are carried out correctly in Appendix A. I checked each of the 18 new laws by hand against the definitions and found none false. The round-1 counterexample is gone: with `sample_column`/`sample_at` a missing column now gives None. I didn't re-run `bend` or `bcftools`, because plan mode blocks the `/tmp` copies they need, and I made no changes to the repository.

## The decisions, checked

- **1:** fixed as decided.
- **2:** `split_when` holds. Three facts make it hold:
  - `split_problem` checks things in the same order as `Rec.parts`: ALT_DUP, then the INFO entries, then each sample in FORMAT order, with the extra-values check last.
  - None of the checks depends on which ALT a record is for, so the first record's refusal is the line's.
  - Once a count fits `expected_count`, every place `Vals.idx` names is in range (for G with two copies, i(i+1)/2+i ≤ (n+1)(n+2)/2−1).
- **3:** done.
  - Each INFO entry falls under exactly one of `split_info_values` or `split_info_kept`, or is refused; each sample value falls under `split_gt`, `split_format_values` or `split_format_kept`, or is refused. Duplicates and the lone `.` are now covered.
  - `gt_view` with `split_phase` fixes the GT text exactly.
- **4:** spaces only, which follows the experiment (htslib does not trim tabs).
- **5–15:** carried out as decided. `split_valid`, `split_normalized` and `split_change` now speak about the records written. The line's END is copied, so the END check comes out the same for each record. `split_change` also holds for a record passed with BAD_END, because its text is unchanged.
- **16:** all of the minor items are done.

## Findings

1. **Should fix: GT `.` counted as two copies** (`B.Gt.ploidy`; your question 2).
   - VCF 4.3 §1.6.2 writes a haploid missing genotype as `.` and a diploid one as `./.`.
   - Haploid no-calls (male chrX, chrY, chrM) can carry n+1 PL values. As drafted they get BAD_COUNT, which stops the run under `-c e`. bcftools splits them, by count.
   - Fix: for GT `.`, accept either count. n+1 means one copy, (n+1)(n+2)/2 means two; for n ≥ 2 the two counts never coincide, so the values kept are never in doubt. Keep "two copies only" when there is no GT value.

2. **Should fix: the spec's cost is the String path's cost** (plan, step 3).
   - The String path calls `B.Rec.parts` itself. For each of the n records, it re-splits every sample column, runs `Tags.find` (a scan of the header's tags) for every value of every sample, and works out each sample's ploidy again. That is about n × samples × keys × tags.
   - The linear `Got.join` does not touch this.
   - Fix: time the prototype both ways: the spec as written, and a version that looks up each FORMAT key's Number once per line and splits each column once. The second needs a small proof that it gives the same records.

3. **Minor: ALT_DUP for out-of-scope duplicates.**
   - The note says `judge` gives the whole line ALT_DUP too, but for `A <*>,<*>` or `A *,*` it gives Skipped. So under `-c e`, `-m` now stops on a line that passes without `-m`.
   - The refusal is right (the genotype problem is the same); fix the wording.
   - Also, under `-c w` the ALT_DUP warning lacks the "not split" ending the differences table promises for every line that cannot be split.

4. **Minor: no law says a MALFORMED line with 2 or more ALTs is `Whole` under `-m`.** `split_when` assumes the line is not MALFORMED, and `whole_biallelic` covers only fewer than two ALTs. Extend `whole_biallelic`, or add a `whole_malformed` law.

5. **Minor: a whole-line problem can go unreported.** Under `-c w`, when a line cannot be split and its whole-line problem does not stop the run (REF_MISMATCH, BAD_END), only the split's code is reported. Document this, or emit both warnings.

6. **Minor: wording of `split_format_values`.** In its plain statement, "any other the three genotype values" should read "two copies, no GT value, or GT `.` (or both counts, per item 1)": more than two copies is refused, not split.

## Answers to the round-2 questions

1. **Trim spaces only?** Yes. That is htslib's behaviour, and a tab leaves the Number unread, which gives UNDEFINED_TAG with a message that names the tag and the fix: a refusal, not a guess. The one place framebender is more lenient (a space before `>`) is documented; keep it.
2. **GT `.` and ploidy:** neither "always two copies" nor "always one". Accept both counts, as in item 1.
3. **Exact code or only the set of codes in `split_when`?** Keep the exact code. The message is part of what `law machine` fixes, so its code should be approved in plain terms too. In the plain statement, list the conditions first, then one sentence: "the message names the first one, reading the line left to right." The extra proof work is small, since `split_problem` follows `Rec.parts` step by step.
