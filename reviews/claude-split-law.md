# Law review: splitting multiallelic records (phase I), `notes/split.md` on branch `split`

Read-only review of the laws and design. I made no changes to the repository. I did not run `bend` or
`bcftools`, because plan mode blocks writing the `/tmp` copies they need. I traced the findings below by
hand against the definitions.

**Verdict: not ready to accept.** There are 2 blockers. The rest is sound: the genotype rule, the G index
formula, the haploid count and the parser are all correct.

## Blockers

1. **`split_format_values` is false as drafted** (Appendix A, `sample_value` and `split_format_values`).
   `sample_value(body, s, k)` reads the column with `B.Rec.field(fs, 9+s)`. For a sample number `s` past
   the last column, that returns `""` instead of None, and `List.get([""], 0)` then gives `Some ""`.
   - Counterexample: the body of `ex_order` (`... AD:GT  1,2,3:1/2`), with `s = 1` (no such sample),
     `k = AD` (Number R) and `i = 0`.
     - Every hypothesis holds: `hv` holds with `v = ""`, `hm` holds because `"" != "."`, and the line splits.
     - The left side is `values_of(Some "") = Some [""]`.
     - The right side is `lifted(NumR, ..., [""]) = None`, because there is no value 1.
   - The same failure happens for any FORMAT whose first key is an A, R or G tag, including lines with
     FORMAT and no samples.
   - Fix: make `sample_value` return None for a column the line does not have (use `List.get` on the
     fields), or add the hypothesis `9+s < length(fields(body))` to every per-sample law.

2. **No law says which lines get split and which get refused** (`split_alts` … `split_format_values`,
   `whole_*`). Every split law assumes `Rec.parts(...) == Pieces{ps}`.
   - So a `Rec.parts` that refused every line, or returned `Whole` for every line, would satisfy all 13 laws.
   - A geneticist cannot tell from the laws which inputs give `UNDEFINED_TAG`, `BAD_COUNT` or `BAD_GT`.
     LAWS.bend's own rule ("the laws fix its result without reading its algorithm") is not met for splitting.
   - Fix: add a law `split_when`. With `-m`, a line that is not MALFORMED and has 2 or more ALTs is
     `Pieces` exactly when a readable predicate holds, and `Unsplit{c}` otherwise. The predicate:
     - every INFO and FORMAT key (other than GT) is defined;
     - every A, R or G value is a lone `.` or has the expected count: n, n+1, (n+1)(n+2)/2, or n+1 for a
       haploid sample;
     - every GT allele is `.` or a number from 0 to n;
     - no sample has more values than FORMAT has keys.

     State `c` for each case too, and write the predicate with a named `expected_count(num, n)`, not with
     `Vals.idx`.

## Should fix

3. **Lone `.` is in the plain statements but in no law.** `split_info_values` and `split_format_values`
   leave it out (`hm`), and `split_info_kept` covers only NumOther. So "a missing value stays missing" is
   not stated for A, R or G tags. Fix: add the case: if the input value is `.`, the record's value is `.`.

4. **`split_valid` and `split_change` speak about `B.Var`, not about the records written.**
   - Both are true for a reason unrelated to `Rec.parts`: they never mention the split text.
   - The plain statement ("so does each of its ALTs… every record written") claims more than the law says.
   - Fix: state them on text. If `judge(fa, body)` is Normalized and the line splits into `Pieces ps`, then:
     - every `judge(fa, p_i)` is Normalized;
     - the variant read from `p_i` is `singles(v)[i]`;
     - so the written records together make `haps(seq, v)`.

5. **Duplicate ALTs (`A C,C`) give false genotypes.**
   - A sample's `1/2` becomes `1/0` and `0/1`, which says REF on a copy that carries C.
   - Today this line is ALT_DUP; with `-m` it would pass silently. That breaks the project's rule: stop
     rather than guess.
   - Fix: refuse the split with `ALT_DUP` (two equal ALTs, ignoring case, as `judge` compares them).
     List it in "Where framebender differs".

6. **`UNDEFINED_TAG` is stricter than it needs to be** (author's question 3).
   - An undefined key with no value (a flag) has no values to share out among the ALTs. Copying it is
     exact, so copy it rather than refuse it.
   - Worth weighing: when the header lacks a reserved key, use its Number from the VCF 4.3 tables
     (sections 1.6.1 and 1.6.2: AC, AF A; AD, ADF, ADR R; PL, GL, GP G). Those Numbers come from the
     spec, not a guess, and they cover the common real case of AC/AF without header lines (bcftools
     drops them, row 18).
   - Otherwise keep the refusal. The message must name the tag and give the fix (add a header line, for
     example with `bcftools annotate -h`).

7. **Haploid G is decided by the count alone** (`Vals.idx`, `lifted`). A sample with GT `0/1` and n+1 PL
   values is split as haploid. That is a guess written as data, though bcftools does the same.
   - Fix: when the sample has GT, require its ploidy to match: 1 allele for n+1 values, 2 for (n+1)(n+2)/2.
     Otherwise `BAD_COUNT`.
   - Say in the plain statement that ploidy comes from GT.

8. **Old statements are not kept visibly.** `sorted`, `grouped_in` and `no_unsorted` now read
   `items(fasta, vcf, o)`. `whole_without_m` sits at the `Rec.parts` level, one step away from what the
   old laws say.
   - Fix: keep the old `items(fasta, vcf)` definition and add a law `items_without_m`: when
     `split(o) = False`, `items(fasta, vcf, o) == items(fasta, vcf)`. Each old law is then literally the
     new one's case without `-m`, so none is weakened.
   - Also add `biallelic_run` (author's question 4: yes). Users with already-split files need exactly that
     guarantee, and the proof is a short induction.
   - docs/LAWS.md: change "body lines" to "records" in `sorted`.

9. **The speed test is too light for the String path** (plan, Tests).
   - The joined `sub.vcf` has GT only and 2,224 split lines.
   - Real joint-called cohorts have 5–15% multiallelic lines, with GT:AD:DP:GQ:PL at about 100 KB per line.
     Those are the lines that would go to the String path.
   - Fix: before the 6–10k lines of machine proofs, time an unproven String-path prototype on a synthetic
     heavy cohort, so the stage-2 decision is made first.

## Minor

10. **Empty INFO entries are refused with a confusing message.** A trailing `;`, `;;` or an empty INFO
    field gives `UNDEFINED_TAG` for the key `""`. Keep empty entries as they are, or give the refusal its
    own message.
11. **Two laws are looser than their plain statements.**
    - `split_gt` reads alleles with `Pos.read`, so it would also accept written alleles like `01`.
    - `split_format_shape` does not rule out extra trailing values.

    Fix: state the GT text exactly (the input with each allele replaced by `Gt.show(rule)`), and add
    equal value counts per sample.
12. **VCF 4.4 leading phase prefix.** `ex_g_lead` refuses GT written with a leading phase mark (`|0|1`)
    as `BAD_GT`. Test whether htslib 1.24 accepts it, and document the result.
13. **`usage()` text is incomplete.** It lists `-m -any|-both`; add `-` (or `-any|-both|-`).
14. **Index wording.** The plain statements must say "ALT number a, counting from 1"; the laws use the
    0-based record index `i` with ALT `1+i`. docs/LAWS.md should include a worked PL example for n = 2:
    - ALT 1 keeps values 1, 2, 3 (0/0, 0/1, 1/1);
    - ALT 2 keeps values 1, 4, 6 (0/0, 0/2, 2/2);
    - a haploid sample keeps REF's and ALT i's values.
15. **Document these behaviours.**
    - Polyploid G gives `BAD_COUNT`.
    - The summary counts records after splitting; bcftools' "total" counts input lines.
    - Under `-c w`, a split line gives one REF_MISMATCH warning per record, each naming the same line.
    - An unsplittable line under `-c w` passes even when its CHROM is unknown.

## Answers to the review questions

- **Q2: genotype and value rules.** They are correct against VCF 4.3 and the bcftools table.
  - The genotype rule matches all 22 rows under both `--multi-overlaps` settings.
  - The G index `k(k+1)/2 + j` and the count `(n+1)(n+2)/2` are the spec's. The record for ALT i keeps
    values 0, i(i+1)/2 and i(i+1)/2+i, and haploid keeps 0 and i.
  - The open issues are items 1, 3 and 7.
- **Q4: parser.** It is unambiguous, and every command line accepted before gives the same `Cfg`, with
  `split = False` and `over0 = True`.
  - Before this change, any word starting with `-m` in an option position was a usage error (`opt` makes
    `ok` false). Values of `-f`, `-o` and the rest are read in their waiting states, never by `Args.word`.
  - The glued `-m` check comes after the exact `-m` match and cannot catch `--threads`, `-o` or `-O*`.
  - `law threads` and `law output` need no change to their statements. `Args.expecting.of` is False in
    `PMulti` and `POver`, so `--threads` or `-o` there is the option's value and is refused by
    `Args.multi` and the `0|.` check.
  - Their proofs need the two new `Args.step` cases, and the glued `-m` branch shown not to change
    `Drv`.
- **Q5: the author's five questions.**
  1. Keep `--multi-overlaps 0` as the default, as in bcftools; the identity tests depend on it. Document
     the REF claim.
  2. Under `-c w`, keep passing an unsplittable line through with a warning, as for every other problem.
     The warning should say "not split", and the docs should say the output can then hold multiallelic
     records.
  3. See item 6.
  4. Yes, add `biallelic_run` (item 8).
  5. The value laws are right to use alleles and genotypes rather than indexes. Phrase them as a
     relabelling: the record's values for 0/0, 0/1 and 1/1 are the input's values for 0/0, 0/i and i/i.
     Add the lone `.` case (item 3) and the ploidy rule (item 7).
- **Q6: plan.** Running split lines through the spec's own `Rec.parts` on the String path is the right
  choice, since it avoids a refinement proof. The 6–10k-line proof estimate is plausible. Most of the
  churn comes from `Opts` gaining two fields; destructuring through the `R.Opts.*` accessors, or one
  nested field, would cut it. The risk is speed (item 9). Add a differential fuzz against bcftools for
  well-formed inputs, with the documented differences mapped.
