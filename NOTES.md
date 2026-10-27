# framebender: notes

Running notes for the second law-driven-development trial (see BRIEF.md for the questions to answer).

## Decisions, first draft (2026-10-26; superseded by the revised decisions below)

The user is new to genomics and asked the agent to decide, with the three independent reviewers
checking these decisions along with the laws.

1. Scope: records with exactly one ALT made only of the letters A, C, G, T, N. Everything else
   (multiallelic, symbolic `<...>`, breakends, `*`, `.` missing ALT) passes through byte-identical and
   is counted in a stderr summary. Letters compare case-insensitively (the VCF spec says bases are
   case-insensitive; UCSC references are soft-masked lowercase). Bases the tool takes from the
   reference are written uppercase. N is an ordinary fifth letter, equal only to N.
2. REF disagrees with the reference: record passes through unchanged, warning on stderr.
3. Normal form = Tan et al. 2015 (left-aligned and parsimonious), one anchor base before the event;
   when the event reaches position 1 the anchor is the base after it (VCF spec rule).
4. Plain VCF in and out (`bgzip -dc` in a pipe for .vcf.gz); FASTA + .fai reference. Header copied
   unchanged plus one added `##framebender_normCommand=` line before `#CHROM`, as bcftools does.
5. Target: identical to `bcftools norm -f` on records in scope. On disagreement the laws (Tan et al.)
   win and the difference is written up.
6. (added) Sorted in, sorted out: shifting left can move a record ahead of one already seen, so the
   output is re-sorted as bcftools does.

## Decisions, revised (2026-10-27: agreed with all three reviewers; the user chose multiallelic support)

Full text: `reviews/responses-1.md` .. `responses-4.md`; implemented in `LAWS.bend` and `types.bend`.
1. Scope: REF and every ALT made of letters; ALT letters A/C/G/T/N (either case). Multiallelic records
   are normalized (Tan et al. over all alleles; ALT count and order kept). INFO/END is checked and
   rewritten when POS or len(REF) changes. Out of scope, passed through: any non-letter ALT
   (`<...>` including gVCF `<*>`, `*`, `.`, breakends).
2. Each body line gets the first applicable outcome: MALFORMED (stops), out of scope, UNKNOWN_CHROM
   (stops), BAD_END, NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH (these stop under `-c e`, the default,
   and pass with a warning under `-c w`), normalized.
3. Normal form: Tan et al.'s left-aligned and parsimonious; reference IUPAC codes read as their first
   base (VCF 4.3 §1.6.1); N is a letter equal only to N.
4. Normalized records are written canonically (POS without leading zeros, upper-case alleles); every
   other byte is kept; line endings kept (a missing final LF is added).
5. Output sorted by a buffer with an exact flush rule (window `-w`, default 100000); a CHROM that comes
   back, or a record that cannot be put in order, stops the run with UNSORTED.
6. Header: two lines added before `#CHROM` (`##framebender_normVersion`, `##framebender_normCommand`,
   control characters replaced, no date).
7. Top law: the program is a pure state machine proven equal to a whole-file definition `run`; the
   unproven driver only reads files, answers reference reads through the .fai, writes and exits.
Documented differences from bcftools 1.24: `<DEL>`/`<DUP>` and gVCF records not realigned (bcftools
realigns `<DEL>`/`<DUP>`); unknown contig stops only for in-scope records; stops on unsorted input,
long moves, BAD_END, duplicate ALTs, empty alleles; upper-case output for bases from soft-masked
references and for lower-case input; LF/CRLF kept; no `; Date=`.

## Setup

- htslib, bcftools, samtools 1.24 (upstream release tarballs, 2026-07-09) built from source into
  `~/.local/opt/htslib-1.24`. Arch has no packages for them (only AUR).
- Data (`data/`, not committed): UCSC hg38 `chr22.fa.gz` (soft-masked); GIAB HG002 NISTv4.2.1 GRCh38
  benchmark VCF (VCFv4.2). chr22 has 50,284 records: 42,794 SNVs, 6,913 indels, 577 multiallelic,
  no MNPs, no lowercase alleles.

## Comparison with bcftools norm 1.24 (Q5 and compatibility)

Run as `bcftools norm -c w -f ref.fa` (warn on REF mismatch instead of stopping).

- GIAB HG002 chr22 (50,284 records, already normalized; bcftools realigns 1): identical output apart
  from the added header line and that one record, where the change is the same but bcftools writes
  the bases it copies from a soft-masked (lower-case) reference in lower case:
  `a  aaaagaaagaaagaaaGAAAG` (bcftools) vs `A  AAAAGAAAGAAAGAAAGAAAG` (framebender). The laws say
  changed alleles are written in upper case.
- Scrambled chr22 indels (`test/scramble.py ... 3 1`: each GIAB indel rewritten 3 times at random
  equivalent places with random padding, 20% lower case; 20,739 records, bcftools realigns 20,730):
  POS/REF/ALT identical ignoring case, every other column identical; same order.
- Edge cases (`test/edge/`): identical, except
  - IUPAC codes in the reference: bcftools 1.24 reads them as the alphabetically first base they
    stand for (R = A or G is read as A; `replace_iupac_codes` in vcfnorm.c, whose comment in
    `realign` still says N). framebender reads them as N. A deletion next to an R can therefore stop
    at a different place, and a REF written as N there is a mismatch for bcftools.
  - Out of scope here, normalized by bcftools: symbolic `<DEL>` (bcftools moved `T <DEL>` at 4 to
    `A <DEL>` at 1 on a toy contig; to investigate) and records with INFO/END (bcftools updates END).
  - A CHROM missing from the reference: bcftools stops with an error; framebender passes the record
    through.

Speed, first unoptimized build (whole file read into memory, one window read per record):
chr22 GIAB 11.5 s vs bcftools 0.08 s.

### After the law revision (2026-10-27, machine build: `Norm.step` driven by `main.bend`)

`test/compare.sh ref.fa in.vcf` runs both tools with `-c w` and diffs the records (REF/ALT upper-cased).
- GIAB HG002 chr22 (50,284 records, 577 multiallelic, now in scope): identical records except the
  soft-masked lower-case record above. Header: bcftools also adds `##FILTER=<ID=PASS,...>` (htslib
  re-serialization, as Claude predicted in round 2) and its own two lines.
- Scrambled chr22 indels (20,739): identical ignoring case. framebender changes 5 more records than
  bcftools realigns: lower-case records already in normal form, now written in upper case (R9).
- Edge cases (`test/edge/sorted.vcf`, the edge file sorted): identical except `<DEL>`, which bcftools
  realigns and framebender passes through (documented). The multiallelic record and INFO/END match.
  The unsorted original (`in2.vcf`) stops with UNSORTED in framebender; bcftools writes unsorted output.
- Speed: 31.7 s on GIAB chr22 (bcftools 0.08 s). The first machine build took over 10 minutes: the spec's
  `keyed` chose between the same-CHROM and new-CHROM branches with `Bool.pick`, which evaluates both, so
  every line flushed the whole buffer in the discarded branch. Rewritten as a `match` (same meaning).
  Lesson: spec definitions the code reuses must be lazy where they branch.

## First law review (Q4): who caught what

Three reviewers, same prompt (`refs/REVIEW_PROMPT.md`), same sources, none of the drafter's reasoning.
Reports in `reviews/`. Claude (Agent tool, ~5 min), GPT-6 Astra (codex exec, ~7 min), Gemini 4 Argon
(Antigravity CLI in a Herdr workspace, ~83 min of reasoning, one context compaction). None found a
false law; all three found the same two blockers.

| Finding | Claude | GPT | Gemini |
|---|---|---|---|
| No end-to-end law (CHROM→contig, FASTA parsing, entry construction) | x | x | x |
| `small_moves` forbids right moves, which left trimming makes | x | x | x |
| Chromosome block order and same-position ties unconstrained | x | x | x |
| Moves ≥ w give unsorted output with only a warning | x | x | |
| IUPAC codes must become their first base (VCF §1.6.1) | x | x | x |
| `#` lines can parse as records | x | x | x (also empty CHROM) |
| Command line in header unescaped; empty cmd | x | x | x |
| Header line goes first if there is no `##fileformat` | | | x |
| CRLF unspecified | x | x | x (bare `END\r` not detected) |
| Window laws allow "always None" (no progress/sufficiency) | | x | x |
| Stale CIGAR/HOMSEQ after rewriting | x | x | x |
| Multiallelic out of scope though Tan and bcftools handle them | x | x | x |
| `*` records depending on a moved deletion | | x | |
| INFO/END out of scope | | x | x |
| REF=ALT not in decision 1's wording | | x | x |
| Default REF-mismatch policy: bcftools exits non-zero | | x (asks to pin) | x |
| Decision 3 wording (event at position 1 vs POS 1) | x | x | x |
| N gaps let records slide far | x | | |
| N equal to N treated as a real match | | | x |
| Already-normal lower-case/leading-zero records kept verbatim | x | | x |
| No stderr/exit-status laws | x | x | |
| `shift` comment, 32-bit POS, unused defs | | | x |

Round 2 (reviewers answered the drafter's responses, `reviews/*-r2.md`; Gemini and GPT in their
round-1 sessions, Claude in a new session given only its round-1 summary):
- Gemini and GPT both showed the drafter's proposed window-sufficiency range (R14) was unsatisfiable
  when a record moves right (`(1,ACG,ACT)` on `ACG` vs `TCG`). Claude agreed with the wrong range.
- All three: the outcome classification was not total or disjoint (symbolic vs NON_ACGTN, telomeric
  POS 0, malformed lines); the flush rule must be part of the spec for the exit code to be determined;
  an unterminated last line can be glued to another after sorting; idempotence only holds for the body.
- Gemini made two wrong claims about bcftools (that it flags duplicate ALTs and fixes END on unmoved
  records); running bcftools 1.24 showed neither happens. The suggestions were kept on their merits.
- GPT alone held out on stale CIGAR (documentation does not make the annotation true) and on 32-bit POS.
- Gemini round 2 took 8 min in its existing session (round 1: 83 min).

Rounds 3-5 (`reviews/*-r3.md` .. `*-r5.md`, drafter responses `reviews/responses-1..4.md`):
- Round 3: all three independently found that the drafter's new "MALFORMED flushes the buffer" rule
  made the ordering law false. Fixed by making MALFORMED always stop, which is also what bcftools does
  (checked by running it on blank lines, bad POS, short lines).
- Round 4: GPT and Gemini independently found that the per-outcome window rule ignored the
  classification order (BAD_END etc. need to know the contig exists). Claude found that "a file ending
  in LF" would have had a blank last line, failing every file, and that the step order per line was
  unspecified. Gemini found the ordering law had lost "grouped".
- Round 5 (2026-10-27): all three agree with the plan; no blocker or should-fix left.
- Each round the drafter's own fix for the previous round introduced something the reviewers caught.
  The reviewers converged in 5 rounds, about 4 hours of wall time. Reusing each reviewer's session
  made later rounds fast (Gemini: 83 min in round 1, 2-8 min afterwards).
- Wrong claims by reviewers: Gemini on bcftools duplicate-ALT and END behaviour (round 2); Claude
  accepted the drafter's wrong window range (round 2) and said so in round 3.

Rounds 6-8 (2026-10-27, on the rewritten `LAWS.bend`/`types.bend`; `reviews/*-r6.md` .. `gpt-r8.md`,
responses `reviews/responses-5.md`):
- No reviewer found a false law in the rewrite. Found: FASTA whitespace wider than agreed (`Char.is_space`
  includes VT/FF; GPT, Gemini), empty/repeated contig names kept (GPT, Gemini), EOF could be given
  twice by the driver definition (Gemini), the trusted driver doing the IUPAC conversion (Claude), the
  command line outside the laws (GPT, Claude), a confusing UNSORTED message (all three), and the
  reference-read contract stated more loosely than `truth` (GPT, round 7).
- Declined, and accepted by all three: a trace law for streaming and a law forcing window doubling
  (performance, measured by benchmarks, not output).
- All three agree with the 15 laws (round 7 for Claude and Gemini, round 8 for GPT). The owner
  delegated approval; the laws are marked approved on that basis.

## Outside the laws (performance)

When bytes leave the process, peak memory, and how fast reference windows grow do not change any
output and are not specified by the laws; benchmarks measure them.

Where the time goes (2026-10-27): a Bend program that only reads GIAB chr22 in 64 KB pieces, splits
it into lines (`B.Text.lines`) and fields (`B.Rec.fields`), joins them back and writes them to
/dev/null takes 5.0 s. Text is a linked list of Chars, so every pass over the 20 MB file costs
seconds; the tool splits each line's fields several times (`judge_in` twice per line, the machine's
`want`/`body_done`, `R.body_line`). Planned after the proofs: split each line once and pass the
fields along (a code change to re-prove, or prove equal to the old code as minebender's
`proof_speed.bend` did). bcftools' 0.08 s is out of reach with list-based text.

## Proofs (2026-10-27): all 15 laws proven, `bend` and `--verdict` (Lean-backed kernel)

`./check.sh`: examples, the driver builds, `bend PROOF.bend --check-only` and `--verdict` print
ALL PROOFS CHECK. About 16,000 lines of proof in `proof_*.bend`, written by four Claude agents in
parallel (Herdr workspaces `prove-var`, `prove-window`, `prove-run`, `prove-machine`), one per area,
briefed by `PROVING.md`; the lead wrote `usage` and wired `PROOF.bend`. Wall time: window 17 min,
machine 45 min, var 53 min, run 1 h 27 min (all in parallel, about 1.5 h in total). The spec files
(`LAWS.bend`, `types.bend`, `run.bend`, `examples.bend`) are unchanged since the proofs started;
each restated law was checked to be identical to the approved one.

Per-area notes: `notes/proof_var.md`, `proof_window.md`, `proof_run.md`, `proof_machine.md`.

### Where proofs got hard (Q3)

- Rewrite direction (`%e : G` needs `e : {new == old}`) was the most frequent error in every area
  (the run agent counted about 60 failed checks). Lemmas are naturally stated "complex == simple",
  so simplifying a goal needs `Equal.sym`; rewriting a hypothesis needs `{(%e : G; h) : G[old]}`.
- Affinity: function-typed hypotheses are usable once, so another area's laws could not be passed
  down as hypotheses where they are needed per line (window laws in the machine proof, var laws in
  `twice_run`); those proofs waited for the laws and called them. Every equation used twice needs `+`.
- Language restrictions shaped the proofs: no match after a let, matches in binder order, no
  destructuring of computed pairs, no mutual recursion (eliminators take the induction hypothesis as
  a function argument), recursive defs do not unfold on variables (identical code and spec helpers,
  e.g. `V.inits` and `L.inits`, each needed an equality lemma), no `_` for erased arguments.
- Missing Base facts: `String.eq` sound (down to `Word.cmp` over 32 bits, proven twice, by the
  window and run agents independently), decimal print/read round trip, split/join round trip.
- Size: `twice_run` was the largest (about 7,900 lines with the other run laws), mostly text facts
  (canonical POS/REF/ALT reread the same, END rewrite consistent, a rebuilt record ends in CR only
  if the original did). The normal form's uniqueness (Tan et al.) took the var agent 53 minutes,
  by case analysis on list cuts rather than index arithmetic; the lead's closed-form analysis
  (P, Q, D in `PROVING.md`) was not needed.
- The out/notes "frame": the machine clears a line's output after handing it on, the spec keeps
  accumulating; relating them needed a frame lemma through every function of `run.bend`.

### What proving found (Q2-adjacent)

- Code change forced by a law: windows for a line far past its contig's end grew too slowly to stay
  within `L.bound` (about POS reads instead of clen + 2). The machine agent made `resolve` jump to
  the contig's start once the answer shows the contig is shorter than the window (output unchanged).
- Spec gap that never matters: for an empty REF past the contig end the code's REF check and the
  spec's disagree; unreachable because an empty REF is MALFORMED, but the proof carries that fact
  through five levels.
- Slack in the laws: `no_unsorted`'s hypothesis `1 <= w` is never used; `twice_run` holds even for
  `w = 0`.

### CPU threads and the GPU (2026-10-27, RTX 4080 Laptop 12 GB, CUDA 13.4, 32 CPU threads)

Benchmark: judge every body line of GIAB chr22 (`judge_in` with no reference answer: split into
fields, MALFORMED and scope checks) in parallel halves (`a b = par(..) par(..)`), outside the tool.
- With output text (4 MB pieces): 1 thread 5.2 s, 4 threads 3.3 s, 32 threads 2.7 s. Splitting the
  text into lines and joining the output stay sequential, so about 2x.
- Counting only (no output text): 1 thread 3.3 s, 32 threads 1.6 s.
- GPU (`par!`): every full-size run fails with "memory fault (machine stack overflow?)". Bend walks
  lists recursively and a GPU lane's stack holds between 1,000 and 2,000 nested calls (summing a
  list of 1,000 Nats works, 2,000 fails); GIAB lines are up to 985 characters, and splitting one
  into fields recurses once per character.
- Short lines (INFO replaced by `.`, at most about 60 characters): GPU 1.0 s, CPU 1 thread 0.22 s,
  32 threads 0.11 s, same results. The GPU is about 10x slower than the CPU on this branchy
  linked-list work, as the Bend guide predicts ("divergent work ... stays faster on the CPU").
Caveat: the speed agent was benchmarking at the same time (noticed by the user), so the multi-thread
numbers may be pessimistic; re-time before relying on them.
Conclusion: CPU threads can help (about 2x on the per-line work); the GPU does not fit text in
linked lists. Using either in the tool needs the machine to judge many lines at once, which the
current machine law's one-request-at-a-time protocol does not allow.

Raw speed (single thread, overlapping with the speed agent's runs, so approximate): one pass over
the 35 MB GIAB chr22 file read as bytes, counting LFs: 0.15 s; converting the bytes to a Bend
String first and then counting: 0.32 s. So Bend itself is not slow: the 22 s come from building
Strings, splitting/joining fields and re-parsing each line several times. A single-pass
implementation over the text could plausibly get within a few times of bcftools.

## Two-layer restructure (2026-10-27, owner's request; branch `two-layer`)

Science layer (`LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`: no code mentioned, frozen once
approved) and implementation layer (`protocol.bend`, `MACHINE.bend`: the program writes exactly what
`run` says). Reviews: `reviews/DRAFT2_PROMPT.md`, `*-d2.md`, `responses-6.md`, `*-d3.md`.
- Draft 2: all three agree with the restructure. Found: reads unbounded with batched requests
  (Gemini, Claude, GPT), layers sharing files (Gemini, Claude), code calling spec definitions so
  speedups had edited approved files (Claude), "unsupported FASTA" outcome depending on which reads
  the code makes (Claude), an expert having to read the normalizer (Claude, Gemini), dead `NoAns`
  and comment typos from a rename (Gemini).
- Draft 3: GPT and Claude approve. Gemini's quota ran out mid-round ("resets in 152h"), so Grok 4.7
  (xAI, a fourth model family) stands in for this confirmation round, with the full context; Gemini
  returns for later rounds once its quota resets.
