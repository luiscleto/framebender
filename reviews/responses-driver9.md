# Responses to driver review 9 (index output, phase J, 2026-10-30)

Prompt: `DRIVER9_PROMPT.md`. Reports: `claude-driver9.md`, `gpt-driver9.md` (GPT 6.1 Sol),
`grok-driver9.md` (Grok 4.7). No blocker; every finding is in the trusted driver, its comment
or its tests, none in the laws. Claude accepts the code (with 1 and 3 fixed first) and checked,
against htslib 1.24, where each line is pushed, the index settings, the `END=` lock, the order of
indexing before the frees, the open and close steps, the constructor's grammar, `main.bend` and
the build guards; a 70 KB header line with a `##contig` length gives identical indexes at
`--threads` 1 and 128.

| # | finding | by | decision |
|---|---|---|---|
| 1 | CSI: `bcftools index` refuses a file that does not begin with `##fileformat=VCF` (an input without it, or with a `#` comment before it); `-W` indexes it and exits 0 | GPT, Grok, Claude (all confirmed) | **Fix the code (GPT, Grok):** for CSI, if the uncompressed output is shorter than 16 bytes or does not begin with `##fileformat=VCF`, set the index error flag: "cannot index", exit 2, no EOF block, no index, as the comment on law machine already says. TBI unchanged (tabix accepts it). Claude proposed changing the reference to `tabix --csi` instead; the comment's promise is the simpler one for users ("what bcftools index would refuse"), so the code moves, not the promise. Test both inputs. |
| 2 | An older index at a name htslib reads before ours hides the new one: for `o.vcf.gz`, htslib tries `o.vcf.gz.csi`, then `o.vcf.csi`, then `o.vcf.gz.tbi`; `-W=tbi` leaves `o.vcf.csi`, and queries read it (Claude: `tabix` fails; another layout could give wrong records silently) | Claude (confirmed) | **Fix:** find htslib 1.24's full search order (`idx_find_and_load`, `hts_idx_check_local`, both formats); when a name it tries before ours exists, other than the ones the open moves aside, refuse at step 3 with nothing changed and a message naming that file. Do not remove it: it may be the index of another file (`o.vcf`). State it in the comment on law machine and the README. |
| 3 | An index name that is a symlink to a directory passes the `lstat` check; with `-o` through that link, the run exits 0 and replaces the link, leaving the output path unreadable | GPT (confirmed) | **Fix:** also `stat` each index name; refuse a name that resolves to a directory, before anything is moved or truncated. Regression test. |
| 4 | "byte for byte" holds only when the reference tools' htslib compresses as the linked one (libdeflate) | Claude | **Fix** the comment. |
| 5 | `tabix -p vcf` takes the CRAM path for a name ending in `.cram` | Claude | **Fix** the wording: the reference is the same file under a `.vcf.gz` name. |
| 6 | Tests: two successive spellings can both be CSI, so some cases never test TBI; missing cases: no `##fileformat` (1), a `#` line before it, a stale `<stem>.csi` (2), an index name linking to a directory (3), the `-o` file hard-linked to an index name, stderr's file at an index name, an existing `<name>.old` (the `.old1` path), a header line longer than a block with a `##contig` length | GPT, Claude, Grok | **Fix:** choose CSI and TBI explicitly for every case and rotate the spellings within each; add the cases. |

## Round 2

Claude (`claude-driver9-r2.md`), GPT (`gpt-driver9-r2.md`), Grok (`grok-driver9-r2.md`): ACCEPT.
All six decisions carried out (4f9f68c). Claude and Grok re-ran the new cases on their own builds:
the `##fileformat` check across blocks, on a short output and under a `-c e` stop; the stem
`.csi` rule against htslib 1.24's search order; directory links through a chain of symlinks;
block-spanning lines, CRLF, a header longer than a block and `END=` at `--threads` 1 and 128.
