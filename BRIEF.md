# framebender — project brief

Handed over from the minebender session (2026-10-26). Read this whole file first.

## Why this exists

The second trial of Bend 2's "law-driven development", after minebender (`../minebender`, a
Minesweeper with a proven no-guess assist, live at https://cleto.dev/minebender/). The human approves
precise laws, the agent writes the code and proves them, and the proof checker is the gate.

This time the target is a real bioinformatics tool, picked because it is (a) slow in the common
tools, (b) known to give different answers in different tools, and (c) defined by short written
rules. The pitch: **"every output record is provably the same DNA change, in the standard form, and
it runs as fast as bcftools."** The user wants something that gets attention; real use by labs would
be a bonus.

**The user is not familiar with genomics.** Explain domain terms plainly, with small examples, every
time they come up.

Questions to answer by the end (keep notes in `NOTES.md` as you go):
1. How much did the user have to read beyond `LAWS.bend` to trust the result?
2. Did any law pass while behaviour was wrong? Each such case is a gap in the spec. Record it.
3. Where did proofs get hard, and what was done about it?
4. What did the independent reviewer catch that the drafter missed?
5. How does the speed compare with `bcftools norm` on real data?

## The domain, in brief

- A **VCF** file lists DNA variants, one per line: chromosome, position (1-based), ID, `REF` (the
  reference bases at that position), `ALT` (what this sample has instead), then quality, filter,
  info and per-sample columns. Spec: https://samtools.github.io/hts-specs/VCFv4.3.pdf (v4.4 also
  exists; check which one real files use).
- The **reference genome** is a FASTA file (GRCh38 is about 3 GB). A `.fai` index (made by
  `samtools faidx`) says where each chromosome's bases start in the file, so you can jump to any
  position.
- **Normalization:** the same change can be written several ways. Deleting one `A` from `GAAAAT`
  can be recorded at any of the `A`s, and extra shared bases can be tacked onto both alleles. Tan,
  Abecasis and Kang, "Unified representation of genetic variants", Bioinformatics 2015
  (https://pmc.ncbi.nlm.nih.gov/articles/PMC4481842) defines **normalized = left-aligned and
  parsimonious**, gives an algorithm, and gives a necessary and sufficient condition for an entry to
  be normalized. It also notes that "left alignment" had never been precisely defined despite wide
  use. This paper is the spec for milestone 1. VCF does not allow empty alleles, so indels keep one
  shared "anchor" base in front.
- **Incumbents:** `bcftools norm -f ref.fa` (C, htslib) and `vt normalize`. There are user reports of
  them disagreeing on edge cases (https://biostars.org/p/9506881,
  https://help.galaxyproject.org/t/bcftools-norm-realignment/2519). They are anecdotal, but they
  show where to look when testing.

## Plan

**Milestone 1: a proven normalizer.** A native command-line tool,
`framebender norm -f ref.fa in.vcf > out.vcf`, checked record by record against `bcftools norm` on
real data, and benchmarked against it.

**Milestone 2 (later, only if milestone 1 goes well): variant consequences.** Label each variant
with what it does to a gene (missense, frameshift, stop gained, synonymous…), using Sequence
Ontology definitions, starting with coding changes on one standard transcript set (MANE Select).
Motivation: McCarthy et al., Genome Medicine 2014
(https://www.ncbi.nlm.nih.gov/pmc/articles/PMC4062061/) found ANNOVAR and VEP agreed on only about
65% of loss-of-function variants (about 87% of exonic variants overall) across 80 million variants.
Much of that comes from transcript choice and definitions, not bugs, so the claim has to be
"definitions written down as laws, provably followed", not "VEP is wrong". On speed, an old
benchmark (VEP v82, 4.5M sites) gave VEP 6 h 35 min against 101 s for `bcftools csq`
(https://www.biorxiv.org/highwire/filestream/30771/field_highwire_adjunct_files/0/090811-1.pdf).
The speed bar is bcftools csq, not VEP.

## Design decisions: PROPOSED, confirm with the user before writing laws

1. **Scope of milestone 1:** biallelic records (one `ALT`) with plain base alleles (`A C G T N`,
   any case?). Everything else is passed through unchanged and counted in a summary on stderr:
   multiallelic records, symbolic alleles like `<DEL>`, breakends, `*`. (bcftools can split
   multiallelic records with `-m`; leave that for later.)
2. **`REF` doesn't match the reference:** keep the record unchanged and warn. bcftools stops with an
   error by default and can be told to warn (`-c`). The law would say mismatched records come out
   untouched.
3. **Normal form per Tan et al.:** shifted left as far as the reference allows, no shared bases
   beyond the single anchor base, never moved before position 1.
4. **Input and output:** uncompressed VCF in and out, so `.vcf.gz` goes through `bgzip -dc` (the
   maintained upstream tool) in a pipe. Reference: uncompressed FASTA plus its `.fai`. Header lines
   are copied through unchanged. Should the tool add a header line saying it ran, as bcftools does?
5. **Compatibility target:** on records in scope, output identical to `bcftools norm -f`. Every
   difference is investigated and written up, either as our bug or as a documented, law-backed
   disagreement.

## Laws to draft (plain English + Bend, for review)

Definitions the user will own: the reference as a lookup, what a variant "does" (apply it to the
reference sequence), left-aligned, parsimonious, normalized.

- **Same change:** applying the normalized variant to the reference gives exactly the same sequence
  as applying the original.
- **Standard form:** the output is left-aligned and parsimonious.
- **Running it twice changes nothing.**
- **One form per change:** two variants that make the same sequence normalize to the same record.
  This is the law that makes comparisons across tools and samples safe.
- **Out of scope is untouched:** records outside decision 1, and REF mismatches (decision 2), come
  out byte-identical.
- **Parsing:** for every line in scope, printing what was parsed gives back the same line, so
  columns the tool doesn't touch are never altered.

Proof strategy, as in minebender: state the spec in the simplest, most obviously correct form (for
example, "same change" by actually building both sequences over a window), then prove the fast code
equal to it.

## Independent review (the user asked for this)

Before implementing any law, send the draft laws (English and Bend) to **three independent
reviewers from different model families**, as the user asked:

| Reviewer | How to run it (verified 2026-10-26, non-interactive, read-only) |
|---|---|
| Claude (fresh agent) | Agent tool, `subagent_type: general-purpose` |
| Gemini 4 Argon | `agy -p "<prompt>" --model gemini-4-argon-high --mode plan` |
| GPT-6 Astra | `codex exec -m gpt-6-astra -s read-only --skip-git-repo-check "<prompt>"` |

Run the CLIs from this directory, so they can read `LAWS.bend`. The user also offered Herdr for
running them in visible panes (`herdr --skill` explains it). Give each reviewer the **same** prompt
and **only** these sources: `LAWS.bend`, the VCF spec, the Tan et al. paper and the `bcftools norm`
manual (https://samtools.github.io/bcftools/bcftools.html#norm). Give none of the drafter's
reasoning, so no reading is anchored on yours. Ask whether each law means what its English says,
matches the spec, and misses cases (position 1, N bases, lowercase, long repeats, chromosome ends).

Then merge the three reports: note which findings came from more than one reviewer, check each
finding yourself (reviewers can be wrong), and show the user, one law at a time, the law, the
findings with who raised them, and your response to each. Then ask for approval. Record in
`NOTES.md` which reviewer caught what (Q4). A human bioinformatician may review the final set later,
if the user finds one.

## Bend facts (verified on this machine)

- Bend 2.0.39 (`bend`, in `~/.local/bin`). **Read `bend guide` before writing any Bend.**
  `bend base` prints the standard library (it includes files: `File.open`, `File.open_bytes`, …).
- Convention: `LAWS.bend` (user-owned) states laws as open claims; `PROOF.bend` proves each with a
  def of the same name. `bend PROOF.bend --check-only` must print `ALL PROOFS CHECK`;
  `--verdict` re-checks with the Lean-proven BendTT kernel (needs Lean v4.34.0, already installed
  with elan in `~/.elan`; put `~/.elan/bin` on PATH). Copy `../minebender/check.sh` as a start.
- **Native builds work:** `bend f.bend -o f` built and ran a test program through clang 23.1.3
  (glibc 2.44). `-o f.c` emits the C source. `./f +RTS --threads N` sets CPU threads (this machine
  has 32). A normal call already runs in parallel on CPU when the work splits; `f!(x)` goes to the
  GPU (RTX 4080 laptop; CUDA not checked). Parallel calls want balanced work: split the records
  into equal chunks.
- Set `BEND_NO_TELEMETRY=1` in scripts.
- **Lessons from minebender:** read `../minebender/NOTES.md`, sections "Where proofs got hard (Q3)"
  and "Bend lessons", before the first proof. Short version:
  - `+x` marks a reusable value; everything else is used at most once (a pattern variable needs it
    too: `case 1n+(+p):`).
  - `match` only works on parameters and pattern variables, in binder order: computed values need a
    helper def.
  - Rewrites: `%e : P` with `e : {new == old}`, where P is the goal with `_` at the old term.
  - No mutual recursion: pass induction hypotheses as closures. Function-typed hypotheses are
    usable once, so "for every X" invariants become Bool checks plus a read-back lemma.
  - A law's `for x` without `+` can't be reused in its proof: forward each `L.law` to a restated
    lemma with `for +x`.
  - Annotate bare constructors in lets: `{T.Pos{x, y} : T.Pos}`.
  - Index arithmetic was the slowest kind of proof, and positions and shifting along repeats will
    need it. Keep the arithmetic in small, separate lemmas.
- Benchmarks: run under `nice -n 19` with a `timeout`. An unbounded benchmark in minebender maxed
  the user's laptop fan.

## Tools and data

- Not installed yet: `bcftools`, `samtools`, `bgzip`/`tabix` (htslib). They're needed for testing
  and comparison. Find a maintained install route (the distro is Arch-based Omarchy; mise is used
  for tools). Commands needing sudo go to the user one at a time.
- Test data, public: Genome in a Bottle (GIAB) truth sets for HG002, and the GRCh38 reference. For
  development, use one chromosome (e.g. chr20 or chr22) to keep downloads small.

## User working preferences

- Prefers maintained upstream tools over custom code; justify anything bespoke.
- No `curl | bash` without inspecting the content first. Commands needing sudo: hand them over one at
  a time, explained, as a single line.
- Ask before creating the GitHub repo or pushing. minebender lives at github.com/luiscleto/minebender
  (MIT); the user will probably want the same here.
- Laws are reviewed one at a time, each with its plain-English statement and its Bend. Once approved,
  never weaken or delete one without explicit consent.

## Suggested first steps

1. Read `bend guide`, then the minebender notes named above.
2. Restate the five design decisions to the user and get them confirmed (explain the genomics
   terms).
3. `git init`, copy and adapt `check.sh`, install bcftools/samtools, fetch chr22 test data.
4. Draft the definitions and the first laws, send them to the independent reviewer, then present
   draft + review to the user, one law at a time.
