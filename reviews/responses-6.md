# Drafter's responses to the draft-2 review (two layers)

Reviews: `reviews/gpt-d2.md`, `reviews/claude-d2.md`, `reviews/gemini-d2.md`. All three agree with the
restructuring. The revised draft is `draft/` again (draft 3): `LAWS.bend`, `types.bend`, `run.bend`,
`tan.bend` (science), `protocol.bend` and `MACHINE.bend` (implementation), `norm.bend` (stub).

T1. **Reads not bounded** (Gemini 1, Claude 5, GPT 1). ACCEPT. `DSt` counts reference reads
(`reads`, increased by the length of each `Ask`'s list); `result(d, limit)` gives a report only if
the machine stopped and `reads <= limit`; `launch` uses `bound(...)` for both the steps and the
reads. The `bound` comment says what it counts and that it is not a speed target.

T2. **Layers share files** (Gemini 2, Claude 6). ACCEPT. Science: `LAWS.bend` (no `norm.bend`
import), `types.bend` (no protocol types), `run.bend`, `tan.bend`. Implementation:
`protocol.bend` (`Ans`, `Req`, `In`, `Next`, `Fasta.plain`) and `MACHINE.bend` (`truth`, the driver
definition, `bound`, `launch`, laws `machine` and `usage`).

T3. **Code calls spec definitions; optimizing them meant editing approved files** (Claude 1).
ACCEPT as a rule: after approval the science files are frozen. The program may call science
definitions (reuse is fine) but never needs to change them: a faster version lives in code files
and is proven equal to the definition inside the machine proof. The working-tree `run.bend`
(the speed agent's lazy `take_ready`/`drop_ready`, same function) is the version under review
(Gemini 5, GPT 2), so it is frozen as is.

T4. **"unsupported FASTA" depends on which reads the code makes** (Claude 2). ACCEPT. The machine
law now has the premise `P.Fasta.plain(fasta)`: every sequence line (not starting with '>') holds no
space or tab. For other files the law says nothing (the driver stops with "unsupported FASTA" when it
notices). So the law's outcome depends only on the files.

T5. **An expert should not need to read the normalizer** (Claude 3, 4; Gemini 3). ACCEPT Claude's
route. New law `unique`: two valid, normalized variants with the same haplotypes are equal (no
algorithm mentioned). New law `normalized_valid`: if `judge` normalizes a record, the variant it
describes (POS, REF, ALTs as bases) is `valid` on its contig (`line_valid`). With `same_change`,
`stays_valid`, `standard_form` and `unique`, `Tan.normal`'s result is fixed; `tan.bend`'s header says
it need not be read. Not adopted: rewriting `tan.bend` without windows and fuel (it would discard
the existing proofs for no change in what the laws say; the laws above make its internals
irrelevant to review).

T6. **Dead `NoAns`** (Gemini 4). ACCEPT: removed from `P.Ans`; the code keeps its own "not read"
state.

T7. **Comment typos and drift** (Gemini 5). ACCEPT: the `R.has`/`R.added`/`R.stop` typos from a
rename are fixed in comments; `run.bend`'s header no longer mentions `Norm.judge_in`.

T8. **Approval conditional on proofs** (Claude 7). Agreed: the restructure is adopted only once
`./check.sh` (bend and `--verdict`) passes on the final files, and the driver (`main.bend`, which
must now answer lists of reads) is reviewed again as trusted code.
