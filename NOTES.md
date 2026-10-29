# framebender: notes

Running notes for the second law-driven-development trial (see `notes/briefs/BRIEF.md` for the questions to answer).

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
briefed by `notes/briefs/PROVING.md`; the lead wrote `usage` and wired `PROOF.bend`. Wall time: window 17 min,
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
  (P, Q, D in `notes/briefs/PROVING.md`) was not needed.
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

## Driver review (2026-10-27; GPT 6.1 Sol, Claude, Grok 4.7; `reviews/*-driver.md`, `driver-r2-r4.md`)

The trusted driver (`main.bend`) had real bugs no law could catch, all found by the reviewers:
- reads at file offsets of 4 GiB or more wrapped (`U32.from_nat`), and short reads were accepted
  (all three);
- a contig with no letters, or missing from the `.fai`, was answered "unknown" (Claude, Grok);
- non-ASCII command-line arguments were mangled (`IO.args` decodes Unicode; GPT, by running it);
- reopening `/dev/stdout` fails when stdout is a socket (GPT, by running it);
- a CR inside a sequence line shifts `.fai` offsets (Grok).
Fixes: a 70-line C effect file (`io64.c`: a full read at a 64-bit offset, raw writes to fds 1/2;
justified because Base has neither), byte arguments and paths, a strict `.fai` parser, a check of
every byte read against the `.fai` line layout, and one error line per driver failure.
The FASTA premise of law `machine` (`P.Fasta.plain`) went through four rounds until it says exactly
which files samtools faidx 1.24 indexes and serves as the spec reads them (preamble, line lengths,
control bytes, header names, NUL, last header without sequence...); `test/plain_cases.bend` holds the
23 cases checked against samtools. Lesson: the reviewers ran samtools and the binary themselves;
the most useful findings came from testing, not reading.

## Speed so far and the whole genome (Q5; 2026-10-27)

GIAB HG002 chr22 (50,284 records), framebender `-c w` to /dev/null, 32 threads, idle machine:
31.7 s (first machine build) → 22.5 (lazy `Rec.stale`) → 14.0 (speed agent: parse once) → 13.2 →
10.5 (fast agent pass 1: no shared state, unchanged records written as they came) → 9.3 (driver:
VCF read and written as Strings by C effects) → 4.7 s (fast agent pass 2: buffer functions that do
not share the buffer, proven equal to `run.bend`'s; each record judged once; INFO scanned in place).
bcftools: 0.08 s. Every step kept `./check.sh` green and the output byte-identical (`notes/speed.md`,
`notes/fast.md` record each change, its time and its proof cost).

Whole genome (`data/hg002.all.vcf`: GIAB HG002 v4.2.1 benchmark calls, 4,048,342 records, 2.8 GB;
`data/hg38.fa`), one run each, idle machine:

| tool | time |
|---|---|
| bcftools 1.24, to /dev/null | 6.7 s |
| bcftools 1.24, to a file | 7.4 s |
| framebender, to a file | 595 s (147 µs per record; chr22: 94 µs) |

Records: identical (0 differing of 4,048,342; 18 realigned by both). The only difference is
formatting: 25,816 chr6 records list `GT:AD:PS` but give two values (`1/0:1,1`); htslib writes the
missing value (`1/0:1,1:.`), framebender keeps the bytes. `test/compare.sh` now pads sample columns
the same way before comparing. Its two temporary copies need about 6 GB, so set `TMPDIR` to a disk,
not the RAM-backed /tmp (the first whole-genome compare ran /tmp out of space).

Where chr22's 4.7 s goes (fast agent's profile): splitting into lines ~15%, copying output ~15%,
scanning INFO ~15%, checking for CR ~8%, driver I/O per step ~15%; shared state no longer shows.
Every remaining cost is a pass over text stored as a linked list of Chars.

### Pass 3: parallelism and long runs (fast agent; `notes/fast.md`)

- Shipped (proven): a queue counter in the machine state, so the fuel no longer walks the queue on
  every step. Neutral at 64 KB pieces; needed by any large-piece or batched design. Whole genome
  rerun: 586 s, records identical to bcftools (`compare.sh` 0 differing).
- Parallelism, prototypes without proofs (chr22, output identical): one batched Ask per piece and
  judging in a balanced fork-join went from 3.7-3.9 s on 1 thread to 2.7-2.9 s on 4 and 2.5-3.0 s on
  32. Scaling stops at about 4 threads; the rest is sequential: splitting a linked list into lines
  (~12%), copying unchanged text to the output (25%), driver I/O per step (~15%). A proven version
  (lines that keep their LF, batched reads) was estimated at 4-6 hours of proof work for under 2x on
  chr22, so the speed work stops here.
- Why the whole genome costs more per record: the cost grows with the number of records one run has
  handled (62 µs per record at 50k, 86 at 160k, 116 at 319k on chr1), with flat memory (about 217 MB)
  and an unchanged profile: heap locality degrades as the runtime's free lists recycle scattered
  nodes. Not the reference, line lengths or positions. 4 MB pieces were faster on chr22 (3.2 s) but
  far slower on the whole genome (1,747 s). A fix belongs in Bend's allocator.

Conclusion (Q5): framebender is about 60x slower than bcftools on chr22 and about 80x on the whole
genome. The cost is Bend 2's text representation and allocator, not the laws. The laws held through
every rewrite: seven implementation changes took chr22 from 31.7 s to 4.5 s, each proven, with
byte-identical output.

## Q1 and Q2 (2026-10-27)

Q1, what the owner read beyond `LAWS.bend`: nothing so far, and not `LAWS.bend` either. The owner
has no bioinformatics background and delegated the expert reading to three reviewers from
different model families (Claude, GPT, Gemini; Grok stood in for Gemini once). Trust rests on the
reviews, on the proofs checked by `--verdict`, and on bcftools giving the same records. The lead's
walkthrough of the main laws comes at the end; a human bioinformatician's review is still to come.

Q2, laws that passed while behaviour was wrong: none found inside the laws. The comparisons with
bcftools differ only where a decision says they should (README, "Differences"). Every real bug came
from outside the laws, in the trusted driver (`main.bend`, `io64.c`), and the driver reviewers found
them all (see "Driver review"): file offsets past 4 GiB wrapped, short reads were accepted,
non-ASCII arguments were mangled, contigs that are empty or missing from the `.fai` were answered
"unknown". The law `machine` was proven throughout, because it assumes the reference arrives
correctly. The gap was in what the laws cover, not in what they say. The FASTA premise
`P.Fasta.plain` now states exactly which files the driver reads as the spec does.

## Packed bytes (2026-10-27/28; branch `bytes`, merged into `main`)

The String machine could not get much below 4.5 s on chr22 (see "Speed so far"). The rewrite runs
on bytes packed four to a `U32`, through four packages written for it, each with its own laws,
proofs and three-model review (`../lawful-words`, `-arrays`, `-bytes`, `-fields`; cross-project
notes in `../NOTES.md`). The science layer did not change.

- **Contract** (`bytes_enc.bend`, `protocol.bend`, `MACHINE.bend`): input pieces and reference
  answers are bytes, and decoding them gives the text the spec reads. Accepted by Claude, GPT and
  Grok after three rounds (`reviews/responses-contract-1.md`).
- **Phase A, the code** (`notes/bytes.md`): byte-identical to the String build on every test.
- **Phase B, the proofs** (`notes/bytes_proofs*.md`): a coordinating agent and six area agents.
  `PROOF.bend` checks with `bend` and `--verdict`; the 15 laws are unchanged.

Q2 (laws that passed while behaviour was wrong): proving `lawful-bytes`' word-at-a-time search
found a real bug that every test and the whole-genome comparison had missed (`../NOTES.md`).

Q3 (where proofs got hard), new here:
- Big numbers. Bend's `Nat` is unary and the checker compares terms by evaluating them, so a
  constant such as 2^31 inside a definition cannot be proven about. Bounds are stated on 32-bit
  words instead (`le31`), in the contract and the code.
- Memory. One scratch proof closed `2^28 <= 2^29` by computation and grew to 22 GB. Checks now run
  under a 4 GB cap (`test/bcheck.sh`).
- The proofs needed code changes (C1, C5-C7 and others in `notes/bytes_proofs.md`), each from a
  counterexample an agent found to an over-strong lemma. None changed the output.

Q4 (what the reviewers caught): in the contract, all three found that the machine law quantified
over text no byte buffer can carry (characters of 256 or more, pieces over 2^31 bytes); GPT alone
found that a long enough command line broke the step bound.

Q5 (speed), interleaved runs on 2026-10-28, wall clock, output to a file:

| input | bcftools 1.24 | String build | bytes build |
|---|---|---|---|
| chr22 (50,284 records) | 0.124-0.135 s | 4.5-5.1 s | 0.119-0.162 s |
| whole genome (4,048,342) | 8.55-8.59 s | ~590 s | 9.14-9.69 s |
| `data/scr.vcf` (20,739 rewritten) | 0.076-0.091 s | 7.3 s | 5.21-5.33 s |

`test/compare.sh` on this build: 0 differing records on chr22, `scr.vcf` and the whole genome.
The rewritten records still go through a `String` slow path, which is why `scr.vcf` lags.

## Rewritten records on bytes (2026-10-28; branch `rewrite`, merged into `main`)

The bytes build still sent every record that normalization changes through the old String code:
5.2 s on `data/scr.vcf` against bcftools' 0.08 s. A profile (gprof) put two-thirds of that in
reference counting of shared Strings, mostly from splitting INFO up to six times per record. The
rewrite agent added a bytes path (`norm_fix.bend`, plan and notes in `notes/rewrite*.md`), proven
equal to the String path's result, with two sub-agents for the normalizer and the line tests.
About 13,800 lines of proofs; no law, contract or driver change.

| input | bcftools 1.24 | before | after |
|---|---|---|---|
| `scr.vcf` (20,739, nearly all rewritten) | 0.075-0.094 s | 5.24-5.38 s | 0.137-0.169 s |
| chr22 | median 0.125 s | median 0.147 s | median 0.144 s |
| whole genome | 8.40-8.55 s | median 9.19 s | median 7.95 s (6.97-10.17) |

The whole genome's rounds vary by about 3 s for both builds (the disk), so the two are the same
within noise. Checks: bcftools 0 differing records on chr22, scr, a second scramble and the whole
genome; `test/same.sh`, 128 runs identical to the previous build, also with a build of tiny limits.

## Faster driver and `.vcf.gz` (2026-10-28; branch `driver`, merged into `main`)

The speed agent profiled the whole genome (`notes/speed_plan.md`): the driver took 1.6 s, 1.3 s
of it reading the FASTA, and the machine about 3.9 s. Trusted code only, no proofs
(`notes/speed_driver.md`): a fast path for whole FASTA lines, the next VCF piece read ahead by a
helper thread, and BGZF read through libdeflate (`build.sh` links it).

Whole genome, to a file, both tools pinned to the performance cores (`taskset -c 0-15`; unpinned
runs vary by about 3 s on this hybrid CPU):

| input | bcftools 1.24 | before | after |
|---|---|---|---|
| plain VCF | 7.69-7.90 s | 5.38-5.54 s | 4.84-4.99 s |
| `.vcf.gz` | 7.91-8.08 s | 6.15-6.57 s (`bgzip -dc \|`) | 4.83-5.15 s |

Unpinned, to a file: 5.75-6.38 s (5.37-6.57 s on `.vcf.gz`) against bcftools' 7.75-8.04 s.
Before pinning, the earlier tables in this file compared unpinned runs.

Driver review 4 (`reviews/*-driver4*.md`, Q4): GPT and Grok accepted. Claude alone found that a
`.vcf.gz` cut at a block boundary was read as complete (19,422 of chr22's 50,284 records, exit 0);
it now has to end with BGZF's empty end block. GPT had cut files only inside the first block;
Grok had removed the end block from a complete file and accepted the result. The author had
found and fixed a similar early end of its own (an empty block mid-stream read as the end) before
the review.

## The parallel machine (2026-10-28; phase E, branches `parallel` and `driver2`, merged into `main`)

The machine now reads VCF pieces in batches of 16, runs each piece on its own from a guessed
start, and splices the results in order when a check (`merge.ok`) shows the guess cannot have
changed anything; otherwise that piece runs sequentially, as before. A new package,
`../lawful-halves` (a parallel map over a balanced tree, 12 laws, reviewed by the three models in
two rounds), carries the parallelism. Notes: `notes/parallel.md` (the design and why `merge.ok`
is enough), `notes/parallel_proofs*.md` (the proofs, area by area), `notes/speed_driver2.md`
(the driver).

**Proof.** `MACHINE.bend` and every other contract file are unchanged; `PROOF.bend` proves
`law machine` and `law usage` with the parallel machine (`norm.bend`, which runs the old
machine, now `norm_seq.bend`, unchanged). About 19,400 new lines in 64 `proof_e_*.bend` files,
by seven Claude agents in their own Herdr workspaces; `--check-only` and `--verdict` both pass.

**Q2/Q3: the proof found a hole the tests did not.** The merge statement was false as `merge.ok`
stood: a task whose last item was still the phantom (a placeholder for the record before the
piece) under a different CHROM would have been spliced with that record named under the wrong
CHROM (`notes/cex/proof_e_merge_cex.bend`). Real runs cannot reach it (a new CHROM resets the
last item), and all 312 boundary tests and the whole genome passed without the fix; `merge.ok`
now tests it. The other code changes the proofs asked for are bounds (pieces of at least 256
bytes, a first CHROM under 2^28 bytes, pieces under 1 GiB) and three more checks in `merge.ok`;
none changes an output.

**Q3: what was hard** (from the area notes):
- Bend's rewrite `%e : P` direction caused most failed checks in every area.
- No mutual recursion and no def calling one below it: induction hypotheses go to helpers as
  lambdas; the boundary-line loop became four generated levels.
- Computed pairs cannot be destructured, only parameters: hence continuation defs and lemmas
  that take the pair as an argument.
- Linearity: a proof of a Type-valued invariant can be used once, so invariants are copied
  structurally (`inv_dup`); the Lean kernel counts a linear variable named inside `Equal.cong`
  as a second use where `bend` does not.
- Big closed numbers (`2^30`) overflow the checker's stack; bounds stay on abstract words.
- The largest proof files overflowed `bend`'s 16 MB stack at random; `test/bcheck.sh` now gives
  it 64 MB, and caps memory through the cgroup in both modes.

**Driver review 5** (`reviews/*-driver5.md`, Q4). The driver answers a batch's reference reads
on up to 32 threads, collected in order, and reads up to 16 VCF pieces ahead. All three
reviewers accepted; Claude noted three minor points, none needing a change
(`reviews/responses-driver5.md`). This round the reviewers ran far more than they read: GPT 49
targeted checks, Grok the error-order and pipe cases on the real binaries, Claude 264
comparisons per piece size on damaged inputs plus ThreadSanitizer, AddressSanitizer and
injected thread and allocation failures. No defect found.

**Q5.** Whole genome, to a file, interleaved, three rounds (output file deleted outside the
timing; pinned with `taskset -c 0-15`):

| input | bcftools 1.24 | sequential (before) | parallel machine | + parallel driver |
|---|---|---|---|---|
| plain VCF, pinned | 7.83-7.91 s | 4.86-4.94 s | 2.39-2.49 s | 1.83-1.87 s |
| `.vcf.gz`, pinned | 7.90-8.00 s | 4.88-4.93 s | 2.72-2.74 s | 1.82-1.84 s |
| plain VCF, unpinned | 7.96-8.12 s | | | 2.16-2.32 s |
| `.vcf.gz`, unpinned | 8.03-8.09 s | | | 2.08-2.19 s |

chr22: 0.06 s pinned (0.09 s unpinned) against bcftools' 0.11-0.12 s (0.13-0.14 s). The 20,739
moved indels (`data/scr.vcf`), where nearly every record is rewritten: 0.12-0.13 s against
0.07-0.08 s, so rewriting a record is still slower than in bcftools. Peak memory on the whole
genome: 670 MB against bcftools' 11 MB (the sequential machine used 141 MB). One timing pitfall:
reusing one output file adds the cost of truncating the previous 2.8 GB output to the next run
(chr22 measured 0.3 s that way).

## `--threads` and memory (2026-10-29; phase F, branches `threads` and `memory`, merged into `main`)

The owner: the configuration matters for different hardware, and 60 times bcftools' memory is a
lot, though speed comes first. Two Claude agents worked in parallel in their own git worktrees
and Herdr workspaces. Notes: `notes/threads.md`, `notes/memory.md`.

**`--threads N`** (1 to 128, anywhere an option is expected, not recorded in the header). New
`law threads` in `MACHINE.bend`: adding `--threads N` changes nothing the program writes. It went
through a three-model law review in two rounds (`reviews/*-threads-law*.md`), and the proof
follows from `law machine` (`proof_f_args.bend`, `proof_f_threads.bend`). The driver sizes its
read-ahead, the reference reads in flight and the batches by N, and a C constructor sets Bend's
worker threads to at most N (`BENDRTS`); at small N it removes the idle workers' memory (109 MB
against 366-402 MB at N = 1, before the memory work).

**Q3: a law already said enough.** The design put the batch size in the machine's state, which
meant about 200 changed references in 10,000 lines of wrapper proofs. Instead the driver closes
each batch by sending an empty piece after every N pieces: `law machine` already holds for every
way the VCF is cut, empty pieces included, so no machine proof changed (only `kmax()` went from
16 to 128).

**Memory.** Measured first, then four changes: a patch to Bend 2.0.39's allocator in `build.sh`
(large freed blocks went to a per-thread slot the main thread, which allocates them, never
reused; about 85 MB), reference-read buffers of 128 KiB in fixed per-slot buffers instead of
1 MiB from `malloc`, reference windows of at most 4 MiB instead of 32 MiB blocks, and the task
running on the piece itself instead of a copy. The last needed a new fact from the phase B
simulation (each advance keeps the sequential machine's input buffer, `S.Kept`) and about 800
proof lines. A draft upstream report on the allocator, with a 20-line repro, is in
`notes/memory.md` (not posted).

**Q2/Q4: what the reviews caught** (driver reviews 6 and 7; `reviews/*-driver6.md`,
`*-driver7.md`). The laws held throughout; both defects were in trusted code:
- The read buffer had first moved to the thread's stack. Under a small `ulimit -s` (64 or 128
  KiB) the run crashed, and Claude showed that below the guard page it could write into another
  thread's stack: wrong letters with exit code 0. All three reviewers found it; GPT and Grok
  reproduced it. Fixed with the per-slot buffers.
- `build.sh`'s check that the generated runtime is the one the patch was written for accepted
  some others (GPT built one with a changed `CAP_WORDS` that passed and broke the patch's
  one-block argument). Fixed by pinning every constant the argument uses.
- Grok: the constructor's number reading clamped at 1000, so a `-w` of 2^48 or more looked valid
  to it (harmless: the run stops anyway). Fixed.
GPT ran its tests from a scratch directory this time (`--sandbox workspace-write` there, the
repository outside it), which removed nearly all of its permission prompts.

**Q5.** Whole genome, `-c w`, to a file, pinned, three rounds, identical output at every setting:

| | time | peak RSS |
|---|---|---|
| bcftools 1.24 | 8.01-8.15 s | 11-12 MB |
| phase E | 1.83-1.87 s | 600-670 MB |
| now, default | 1.83-1.85 s | 344-351 MB |
| `--threads 8` | 2.07-2.08 s | 203-206 MB |
| `--threads 4` | 2.66-2.67 s | 129-131 MB |
| `--threads 1` | 6.09-6.11 s | 44 MB |

What is left of the gap to bcftools' 11 MB is the design: bcftools streams one record at a time
on one thread, while framebender holds a 3.5 MB piece, a reference window of up to 4 MiB and an
output buffer per piece in flight (about 20 MB each). Smaller pieces trade memory for time
(1.6 MiB pieces: about 230 MB for 5-10% more time); not pursued, as under 1 GB is ordinary for
the pipelines that run `bcftools norm`.
