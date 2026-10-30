Not ACCEPT. The named laws `sorted`, `grouped_in`, `no_unsorted` and `twice_run` are not weakened: without `-m`, `items` is the old `items`. Three gaps let a law hold while the output is wrong.

1. **Blocker.** `types.bend` `Hdr.value`, `Num.of`. A space before or after a header value is not trimmed. bcftools 1.24 splits both `##INFO=<ID=IA, Number=A, ...>` and `Number=A ` as Number A. This draft reads them as `NumOther` and copies `IA=1,2` onto every record. `split_info_kept` then holds because the tag was classified Other. Trim spaces and tabs on each header piece and on the ID and Number before matching `A`/`R`/`G`.

2. **Blocker.** `LAWS.bend` `split_info_values`, `split_format_values` (`hm`, `lifted`). A lone `.` is excluded by `hm`, and no other law keeps it, so `IA=.` and `AD=.` may be rewritten or refused with every law true. A list longer than Number still satisfies `lifted`, which only reads the indexes it needs: `IA=1,2,9` with two ALTs may drop the `9`. The plain sentences say a missing value stays missing and a wrong count is refused. Require, for a `Pieces` result: a value that is `.` stays `.`; an A/R/G value has exactly the accepted count (A: n, R: n+1, G: the diploid count, or n+1 only in the FORMAT case below), and the kept entries are exactly those `lifted` names. Same clause for a key with no `=`.

3. **Blocker.** `LAWS.bend` `split_format_values`; `types.bend` `Vals.idx` with `hap` true for every FORMAT field. The plain statement says a haploid sample. The rule is "n+1 values", and the sample's GT is not read. VCF 4.3 §1.6.2: with GT, G has that ploidy; without GT, assume diploid. Fresh run of case f6: GT `1/2` and PL `1,2,3` beside a 6-value PL. bcftools writes a diploid GT (`1/0`) with a 2-value PL (`1,2` / `1,3`). This draft does the same. Choose the count from that sample's GT: one allele means n+1, two means (n+1)(n+2)/2, no GT value means diploid only. Any other count is `BAD_COUNT`. Ploidy above 2 stays `BAD_COUNT`: bcftools 1.24 also errors on a 10-value triploid PL. The diploid index `k(k+1)/2+j` matches §1.6.2, and the haploid index is the allele number. Keep those names in the plain statement. `split_info_values` correctly uses the diploid count only (bcftools: INFO `IG=1,2,3` with two ALTs is "expected 6, found 3").

4. **Should fix.** `LAWS.bend` `split_valid`, `split_change`. Both quantify over a `B.Var` only. They are true with or without `-m`, and they do not mention a line or a written record. The plain sentences say each written record is one normalized ALT and that those records make the input's change. State `split_change` on the items of a split line: in ALT order, the haplotype of each normalized piece is the input ALT's haplotype. `split_alts` and `split_site` already give the piece's POS, REF and ALT.

5. **Should fix.** `LAWS.bend` `split_info_kept`, and the plain sentence "copied byte for byte". INFO/END is Number 1, so the law copies it into the piece. `judge` then rewrites END when POS or the REF length changes (row 25). Say the split step copies the entry, and the written END follows the existing END rule.

6. **Should fix.** `types.bend` `Info.split` on `String.split`. A trailing `;` or `;;` yields an empty piece, whose key is `""`, so the line is `UNDEFINED_TAG`. `String.split("", ';')` is `[""]` (`proof_run_text.bend`). bcftools drops the empty piece and splits `IA=1,2;` and `IA=1,2;;DP=4`. Skip empty INFO entries. They carry no value.

7. **Should fix.** `LAWS.bend` `body_in` for `Unsplit`, before `judge`. Under `-c w`, a line that cannot be split is passed through even when its CHROM is not in the reference. Today UNKNOWN_CHROM stops the run under both `-c e` and `-c w` (`docs/LAWS.md`). MALFORMED is already safe (`Rec.parts` returns `Whole`). On `Unsplit` under `-c w`, still stop when `judge` of the original line would stop.

8. **Should fix.** No run-level law. Add `biallelic_run`: on a file whose body lines have fewer than two ALTs, `-m` changes only the command line in the header (same body, messages and exit code). `whole_biallelic` is only `Rec.parts == Whole`.

9. **Should fix.** Proof plan, parallel tasks. `Defs` must be parsed once from the whole header and copied into every task. A task that parses only its own lines misses the header. Do not call stage 1 done until the joined 3,202-sample file has been timed. The String path and the 6,000–10,000-line proof estimate are credible. Inserting `split` and `over0` in `Opts` is arity-checked. The fast path must key off a comma in the ALT field only.

10. **Minor.** Table row 23. A 4-value PL beside a 6-value PL is not "read as diploid". bcftools 1.24 writes `1,2` and `1,3` from `1,2,3,4` (two values, not the three diploid genotypes). Refusing it is right. The table should say what bcftools writes.

11. **Minor.** Differences table. bcftools drops GT when GT has no `##FORMAT` line (`GT:AD` with only AD defined becomes `AD` and a warning). Keeping and rewriting GT is the right difference. Say so in the table.

12. **Minor.** `usage()` and the `Note` comment in `run.bend`. The usage line omits `-m -` and the glued `-m-any`, `-m-both`, `-m-`, which the parser accepts. The summary comment still says "body lines". With `-m` the first count is records after the split (8 in `ex_run`, from 4 lines).

Parser, for question 4. It is unambiguous, and every command line accepted today parses as before, with `split` false and `over0` true. `-m -any`, `-m -both`, `-m -`, and the glued `-m-any`, `-m-both`, `-m-` all set `split`. `+`, `-snps`, `-indels` and `--keep-sum` are usage errors. `--multiallelics` is rejected, as `--output` is. `law threads` and `law output` need nothing new in their statements. `Args.expecting` is false in `PMulti` and `POver`, as it is after `-c`. There, `--threads`, `-o`, `-O` or a glued `-OT` is that option's value, `Args.multi` or the `0`/`.` check fails, and `law usage` applies. The proofs only have to cover those two states and show that `expecting` is unchanged for every other prefix.

Answers to the five questions.

1. Keep the default `--multi-overlaps 0`. `.` is the honest genotype, and `0` is what every current `bcftools norm -m` pipeline writes. The loss is already stated. A different default would make every `1/2` disagree with bcftools.

2. Do not stop under `-c w` only because a line could not be split. `-c w` already means pass the line through and warn. Do stop when the line is also one that stops today (finding 7).

3. Keep `UNDEFINED_TAG`. Copying an undefined tag whole is the harmful guess for a Number A tag whose header line was dropped (`AC`, `AF`). It will stop real headerless files under `-c e`. `-c w` passes them unsplit. `AD=.` must be kept, not expanded to `.,.`, and finding 2 has to say so. An empty INFO slot is not an undefined tag (finding 6).

4. Yes. Add `biallelic_run` (finding 8).

5. The allele and genotype names are the right wording, including `k(k+1)/2+j` next to genotypes `0/0`, `0/i`, `i/i`. A geneticist can check that against §1.6.2. They cannot check `lifted`, and the current sentences omit the lone `.`, the exact count, END, and the fact that "haploid" is a value count rather than the GT. Fix those sentences with findings 2, 3 and 5.
