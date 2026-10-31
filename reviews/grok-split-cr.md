The CR change makes `twice_run` true again under `-m`. One wording fix before the plain sentence is approved.

1. **Should fix.** The plain statement in `notes/split.md` (the `split_when` sentence for `docs/LAWS.md` and the laws table). It says a well-formed line with two or more ALTs is split exactly when it does not hold "a carriage return inside it," and that the message names `BAD_CR` first. A CR LF ending is a carriage return inside the line, and those lines are still split (`Text.any_cr` sees the body only). On `t2.vcf` with `-c e` the run stops with `BAD_END`, because `unsplit_in` still reports a stopping outcome of the whole line before the split code. **Fix:** say a CR in the line's text, apart from a CR LF ending; then say that a whole-line outcome that stops the run is reported first, and otherwise the message names `BAD_CR`, then the first later reason, reading left to right.

2. **Minor.** `draft_cr/types.bend`, the `Parts` comment, and `draft_cr/LAWS.bend`, the comment on `run`. Both still list the split refusals as `ALT_DUP`, `UNDEFINED_TAG`, `BAD_COUNT`, and `BAD_GT`. **Fix:** add `BAD_CR`.

**Questions**

1. Yes, for every input. `Text.lines` changes a body only by taking one trailing CR into a CR LF terminator, or by splitting on LF. A split record is input fields plus digits and ACGTN, so it holds a CR only if a field did. A line to split that has one is now `Unsplit{BAD_CR}` and is passed through, and a line the reader produced reads back as itself. A NUL and a vertical tab at the end of a cut piece round-trip. A single CR before LF is the terminator, and the line still splits. A second CR stays in the body and is `BAD_CR`. An empty INFO piece is kept. A tab is a field break, so it is not inside a value.

2. In the program, yes. `split_problem` and `Rec.parts.cr` try `BAD_CR` before `ALT_DUP` and the later reasons. `unsplit_in` is unchanged: on `t2.vcf` with `-c e` the result is `BAD_END`, and an unknown chromosome with a CR stops with `UNKNOWN_CHROM` under `-c w`. The Bend statement of `split_when` matches. The plain sentence in item 1 does not.

3. No other approved law is weakened. The new test runs only when `-m` is on, the line is not `MALFORMED`, and there are two or more ALTs. Without `-m`, `out_items` is still `items` on a line that contains a CR. With one ALT, a CR in the body, and the same recorded arguments, `-m` and no `-m` give the same report.

4. The simple rule. A CR that ends a non-final piece of a split value in the last field is what makes the next read differ, so either narrower rule would also keep `twice_run`. Both need the header and a second argument about which values are cut. One test on the line's text is the rule to approve.
