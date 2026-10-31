# Responses to driver review 10 (-m, the faster splitter, the old-index warning; 2026-10-31)

Prompt: `DRIVER10_PROMPT.md`, on `split` at 9621667. Reports: `claude-driver10.md` (Claude Opus
5.5), `gpt-driver10.md` (GPT), `grok-driver10.md` (Grok). No blocker. All three: the laws on the
branch are the approved ones (decisions 1-36 and main's `-W`), no approved law is weakened, and
every law is proven (the lead ran `check.sh`: `PROOF.bend` checks with `--check-only` and
`--verdict`). Every finding is in the driver, the tests, the docs, or speed and memory, which the
laws do not state.

## Fixed before the merge

| # | finding | by | decision |
|---|---|---|---|
| 1 | `io64_threads_of` (io64.c) does not know `-m`, its glued forms or `--multi-overlaps`, so with `-m` `--threads` is ignored and the runtime uses its default pool | GPT (confirmed) | **Fix:** mirror `B.Args.parse`'s `-m` and `--multi-overlaps` forms; test the real worker count with them. |
| 2 | `test/split.sh` counts only `<` diff lines, so a record missing from framebender's output passes | GPT | **Fix:** fail on any difference, both ways. |
| 3 | The old-index warning is written with `put`, which exits 2 on a failed write: `2>/dev/full` with an old index keeps the old `-o` file and can turn exit 0 into 2 | GPT, Claude | **Fix:** the warning is best effort; a failed write of it is ignored. |
| 4 | A directory at an earlier index name hides the later ones from htslib (it stops there), but the warning names the later file | Claude | **Fix:** stop at the first name `stat` finds; no warning if it is a directory. |
| 5 | Without `-m`, `B.Defs.line` (`Bool.pick`) parses every header line twice: a 100k-sample header costs 0.46 s against 0.11 s | Claude | **Fix in the machine** (`Cx.line`: match the prefix, with an equality lemma), not in the spec. |
| 6 | USAGE: "CHROM, POS, ... are kept" is false of the written records, which are then normalized | Grok | **Fix:** the split keeps those fields; each record is then normalized as without `-m`. |
| 7 | USAGE and LAWS.md: INFO `Number=G` is the diploid count, not the copies a GT names; sample G follows that sample's GT; no GT key is diploid; a lone `.` accepts either count | Grok | **Fix** both docs and the differences list. |
| 8 | USAGE: bcftools' handling of undefined tags is three cases (no Number or an unknown one: copied; a flag with no header line: bcftools aborts; a tag with no header line: dropped after a warning) | Grok | **Fix:** state them separately. |
| 9 | A VCF 4.4 leading phase (`|0|1`) is `BAD_GT`, not split; bcftools exits 255 (decision 16) | Grok | **Fix:** add the row. |
| 10 | USAGE: under `-c w` a line that cannot be split reports only the split's code, after a stopping whole-line outcome (decision 22); a split line gives one REF_MISMATCH per record; `A <*>,<*>` stops under `-m -c e` but passes without `-m`; a lone `.` for a numeric A/R/G INFO tag stays `.` | Grok, Claude | **Fix:** add to the `-m` section and the differences. |
| 11 | LAWS.md lacks the worked PL example for n = 2 (decision 16; drafted in `notes/split.md`) | Claude | **Fix.** |
| 12 | README's `-m -any` row leaves out that lines it cannot split safely are refused (they stop the run under `-c e`) | Claude | **Fix.** |

## Speed and memory, after the merge (the speed phase)

| # | finding | by | decision |
|---|---|---|---|
| 13 | A line the splitter refuses goes to the String path (`slow.parts`): about 0.15 s per 146 KB cohort line, 100x bcftools; harmless under `-c e` (the run stops), very slow under `-c w` | Claude | **Fix in the speed phase:** the byte splitter returns the refusal code, proven equal to `split_problem`. Until then, USAGE states the cost. |
| 14 | Under `-m`, memory grows with a line's records and with the file (100k samples x 200 ALTs: 994 MB; 2000 samples x 30 ALTs x 3000 lines: 2.5 GB, 3x slower than bcftools); threads help little | Claude | **Fix in the speed phase:** stream a split line's records instead of holding them. Until then, README and USAGE state it. |
