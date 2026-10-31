**Verdict: ACCEPT, with one should-fix and four minor fixes.**

I did the review read-only, as the prompt requires. I checked the definitions in `draft_cr/` and the outputs already in `data/tmp/split/cr/` by reading them, and did not re-run `bend` or `bcftools`. That `ex_cr.bend` evaluates is the author's claim.

**Q1. Does `twice_run` hold again under `-m`? Yes.**
- The reader changes a byte in only one place: `B.Text.line` (types.bend:222) treats one CR right before an LF as part of the line ending. An LF can never be inside a line.
- So every written line reads back as itself, except one with an LF ending whose text ends in CR. A line written with a CR LF ending always reads back as itself.
- **Lines kept whole or passed as they came:** the reader guarantees that a line ending in CR has a CR LF ending. Passing a line through keeps that. Normalizing does too: it rewrites only POS, REF, ALT and `END=<digits>`, and an END ending in CR is BAD_END, so it is never rewritten.
- **Split records:** each is built from the line's own bytes plus tabs, commas, colons, digits, `.`, `/` and `|`. A line with no CR gives records with no CR, and they read back exactly.
- **The other cases you asked about:**
  - A NUL is not treated specially.
  - A tab inside a value is impossible, since the tab separates fields.
  - An empty value (`AF=,` gives `AF=`) reads back the same.
  - A record cannot be empty, and cannot be taken for a header line (every line after `#CHROM` is a body line).
  - A lone CR at the end of the last field can only come from `…\r\r\n`. That line holds a CR, so it is BAD_CR.
  - A last line with no LF that ends in CR: that CR becomes the line ending.
- No other way remains.

**Q2. Order: correct.**
- `split_problem` (LAWS.bend:1115) and `Rec.parts.if`/`.cr` (types.bend:1735–1749) both check BAD_CR first, before ALT_DUP.
- `unsplit_in` is unchanged, so decision 7 still applies: an outcome that stops the run for the whole line comes first. Under `-c e` the counterexample stops with BAD_END (`cr_run_e_end`), the same as for the other split refusals.

**Q3. No approved law is weakened.**
- The CR test only runs on lines `-m` would split: `-m` on, not MALFORMED, two or more ALTs.
- So `whole_without_m`, `items_without_m`, `whole_biallelic`, `whole_malformed` and `biallelic_run` are unchanged.
- The laws about split records only lose cases.
- The statement of `split_when` is unchanged, but its meaning gains a refusal, so the geneticists must re-approve its plain-language row.

**Q4. Which rule: the simple one.** It is one byte test that does not depend on the header. A stray CR is invalid VCF anyway. The cost is some needless refusals: CR LF files with a CR inside a line, and a CR in a field that is not split. The narrowest rule that would do ("LF ending, and some cut part ends in CR") requires the user to know the header's Numbers.

**Findings**
1. **Should fix: lists of the split refusals that leave out BAD_CR.** As they stand they are false by omission.
   - Where:
     - `draft_cr/LAWS.bend:487`, the rule for `run`: "(ALT_DUP, UNDEFINED_TAG, BAD_COUNT, BAD_GT)".
     - `draft_cr/types.bend:1702-1703`, the comment on `Parts`.
     - `notes/split.md:489-491`. It also says lines are refused only "where bcftools guesses, drops or crashes". BAD_CR is none of those: bcftools splits the line.
     - The list of `-m` codes in `docs/LAWS.md` once it is installed.
   - Fix: add BAD_CR to each list. In the summary, add "or where a record would not read back as written (BAD_CR)".
2. **Minor: plain statement (notes:55).** "A carriage return inside it" is vague at the end of the line.
   - Fix: "a carriage return anywhere in the line other than the one just before its final LF". Note that `…\r\r\n` is refused.
3. **Minor: the "why" in the differences table (notes:64) says too much.** "A record cut there would not read back as written" is true only for LF files, and only when a cut part ends in CR.
   - Fix: "a CR inside a line is not valid VCF; cutting a value at a CR can leave a record ending in CR, which a second run reads as a CR LF line ending."
4. **Minor: the comment on `Rec.parts` (types.bend:1750-1754).** It lists BAD_CR after ALT_DUP with "(checked first)", and its line breaks are uneven.
   - Fix: name BAD_CR first, as `split_problem`'s comment does, and re-wrap the lines.
5. **Minor, optional: test the whole line, not its fields.** Use `B.Text.has_cr(body)` instead of `Text.any_cr(fs)`.
   - It matches the plain statement ("the line holds") and the machine's byte test.
   - It saves a lemma (`any_cr(split(b,'\t')) = has_cr(b)`) in the proof of the byte splitter.
