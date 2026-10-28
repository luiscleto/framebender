# Driver review 4 (branch `driver`): responses

Reviewers: Claude (`claude-driver4.md`), GPT 6.1 Sol (`gpt-driver4.md`), Grok 4.7
(`grok-driver4.md`). Prompt: `DRIVER4_PROMPT.md`. GPT and Grok: ACCEPT. Claude: one should-fix,
three minor.

| # | finding | by | verified | response |
|---|---|---|---|---|
| 1 | A `.vcf.gz` cut exactly at a block boundary is accepted: chr22 cut to 40% of its blocks gives exit 0 and 19,422 of 50,284 records | Claude | yes (lead, `fb_d`: exit 0, 19,422 records; bcftools only warns "No BGZF EOF marker") | Fix: require the empty end-of-file block; refuse with `bad BGZF` otherwise. Files from tools that write no marker are refused; `bgzip -dc` first. Grok tested a file with the marker removed and accepted its output as correct; GPT tested cuts inside the first block only. |
| 2 | On CPU builds a full heap stops with Bend's own `bend: out of memory` and exit 1, never the driver's `error: out of memory` (older than this change) | Claude | from the generated C (`err_seen` is false on CPU) | Fix the comments: list the runtime stop (exit 1) |
| 3 | "any other gzip VCF is refused" is really "first two bytes 1f 8b" | Claude | yes (Grok's run too) | Reword the comment; keep the behaviour |
| 4 | `build.sh` ignores `$CC` | Claude | yes | `${CC:-clang}` |

Q4 note: only Claude found finding 1. It is the same kind of bug the author found in its own first
BGZF reader (an early end of the stream that exits 0), in a case none of the tests reached.

Round 2 (Claude, `claude-driver4-round2.md`): ACCEPT. Cuts at all 543 block boundaries of chr22
(602 runs) stop with `bad BGZF`, exit 2, stdout a prefix of the full output; valid files unchanged.
The one cut it cannot detect: a concatenated file cut right after a middle member's end block,
which is a valid BGZF file with fewer members (htslib accepts it too). All three reviewers accept.
