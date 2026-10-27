# Drafter's responses to the first review (round 1)

Three reviewers (Claude, GPT, Gemini) reviewed `LAWS.bend`, `types.bend` and the 7 design decisions.
Their reports are `reviews/claude.md`, `reviews/gpt.md`, `reviews/gemini.md`. Below, each finding is
merged with the others that make the same point, followed by the drafter's response and what will change.
The laws have NOT been revised yet: this document is what the revision will do. The goal of this round
is agreement on the responses before the laws are rewritten.

Facts about bcftools 1.24 below were read from its source (`vcfnorm.c`: `realign`, `realign_left`,
`replace_iupac_codes`, `has_non_acgtn`), not only from the manual.

Response codes: ACCEPT (fix as suggested), ACCEPT-MOD (fix, differently from the suggestion), DOCUMENT
(behaviour kept, written down as a limitation), REJECT (no change, with reasons).

## Scope change (decided by the project owner)

S1. **Multiallelic records are now in scope** (raised by all three). A record is in scope when REF and
every ALT are explicit sequences of A/C/G/T/N (any case). `Var` becomes `{pos, ref, alts: List<seq>}`
(at least one ALT). Definitions generalize allele-wise: `apply(seq, v, i)` is the haplotype of ALT i;
`same(v, w)` means same POS-independent haplotype for every ALT index i (ALT order is kept, since
genotypes refer to ALT indices); `parsimonious` and `left_aligned` quantify over all alleles at once, as
in Tan et al. (their Algorithm 1 and normalization condition are stated for any number of alleles), and
as `realign_left` in bcftools does (trim the right end while it is identical in all alleles, pad left
when an allele becomes empty, then trim the left while identical in all alleles and all have length >= 2).

S2. **INFO/END is now handled for explicit-allele records** (GPT 14, Gemini 7): when a record is
rewritten and INFO has an integer END, END is set to `newPOS + len(newREF) - 1`, as bcftools does.
All other INFO bytes are kept.

S3. Still out of scope, passed through byte-identical and counted on stderr: symbolic alleles (`<...>`,
including `<DEL>`/`<DUP>`, which bcftools does realign), breakends, any `*` allele (bcftools also leaves
records with `*` untouched: ERR_SPANNING_DELETION), missing ALT `.`, header lines. DOCUMENT the
`<DEL>`/`<DUP>` difference from bcftools.

## Blockers

R1. **End-to-end law** (Claude 1, GPT 1+2, Gemini 3). ACCEPT-MOD. The tool becomes a pure state
machine `Norm.step(state, event) -> (state, actions)`: events are "next chunk of VCF bytes",
"end of input" and "here are the reference bytes you asked for"; actions are "read reference bytes
[a,b) of contig c", "write these stdout bytes", "write this stderr line", "exit with code k". The
unproven IO driver only executes actions faithfully. A spec function
`run(fasta: bytes, vcf: bytes, opts) -> (stdout, stderr, exit)` is defined directly over the whole files
(FASTA parsing: contig name = text after `>` up to the first whitespace; sequence = all following
lines up to the next `>`, CR/LF removed, letters mapped by R6). The top law: for any FASTA and VCF,
driving `Norm.step` with truthful answers to its requests yields exactly `run(fasta, vcf, opts)`.
Premise: the `.fai` agrees with the FASTA (the driver reads the reference through it); that premise is
stated in the law, not hidden. Entries (CHROM, input POS, output POS) are computed inside the proven
core from the line itself, never supplied by the caller. Termination/progress of the window retries is
part of this law (the machine must reach `exit`).

R2. **`small_moves` forbids right moves** (Claude 2, GPT 3, Gemini 1). ACCEPT. Right moves (left
trimming) are allowed; only left moves are bounded (see R4). The order guarantee is not a single
file-wide hypothesis anymore (see R3).

## Order

R3. **Chromosome block order and ties** (Claude 3, GPT 5, Gemini 6). ACCEPT. Law: if the run
succeeds, the body records are exactly the stable sort by output POS within each maximal run of equal
CHROM, runs kept in input order. Equal output POS keep input order (bcftools inserts stably too).

R4. **Records moving left by >= w** (Claude 8, GPT 4). ACCEPT-MOD. Instead of a warning: the run stops
with a non-zero exit and a stderr message naming the record when a record would have to be written
before one already written. `w` defaults to 100000 and is settable with `-w`. Law (with R3): success
implies sorted output; and if the input is sorted by POS within each CHROM run and no record moves left
by w or more, the run does not stop for this reason. Normalization itself is never bounded by w.

## Reference letters

R5. **IUPAC codes in the reference** (Claude 5, GPT 6, Gemini 4.1). ACCEPT. Reference letters are
uppercased, then R,M,W,D,H,V -> A; Y,S,B -> C; K -> G; A/C/G/T/N kept (VCF 4.3 §1.6.1; same as bcftools
`replace_iupac_codes`). Any other character in the reference sequence -> N (bcftools keeps it as a raw
character that matches nothing; DOCUMENT).

R6. **N equals N** (Gemini 4.2; Claude 6 on long slides through N runs). DOCUMENT, do not change.
Normalization is defined on the sequence of symbols, as in Tan et al. and in bcftools, where N is a
literal letter. Refusing to shift across N would make the normal form depend on more than the
haplotype string and diverge from bcftools on every assembly gap. Long slides through N runs are
caught by R4 if they break ordering. The README will say that N is compared as a letter, not as a
wildcard.

## Lines and records

R7. **Header-like lines parse** (Claude 9, GPT 13, Gemini 2). ACCEPT. The header is every line up to
and including the first line starting with `#CHROM`; every later line is a body line. A body line
starting with `#` is never a record (passed through, counted). Empty CHROM is treated as an unknown
contig (R12). POS must be >= 1 to be in scope.

R8. **CRLF** (Claude 12, GPT 11, Gemini 5). ACCEPT. Input is split on LF; a CR immediately before
the LF belongs to the line terminator, not to the last field, so `END\r` is seen as `END`. Untouched
lines are written byte-identical including their terminator; a rewritten line keeps its own terminator;
the added header lines use the terminator of the `#CHROM` line; a final line with no terminator is
written with none. (bcftools always writes LF; DOCUMENT.)

R9. **Canonical text for already-normal records** (Claude 7, Gemini 11.1). ACCEPT. Every in-scope
record that passes the reference check has POS written as a decimal without leading zeros and REF/ALTs
in uppercase, whether or not it moved. So the same change always comes out as the same POS/REF/ALT
bytes, and a second run changes nothing. A record whose POS/REF/ALT text is already canonical and normal
is byte-identical. VCF 4.3 allows this ("tools processing VCF files are not required to preserve case").
Difference from bcftools: bcftools keeps lower-case alleles of records it does not move (DOCUMENT).
Bases taken from a soft-masked (lower-case) reference are written upper case (bcftools writes them lower
case; DOCUMENT).

R10. **Stale representation-dependent INFO** (GPT 8, Claude 10, Gemini 11.2): CIGAR, HOMSEQ, etc.
DOCUMENT. bcftools does not update them either; recomputing CIGAR is a different tool's job. Genotype
fields are allele-indexed and ALT order is kept, so they stay correct. The README will list this.

R11. **`*` records that depend on a moved deletion** (GPT 14). DOCUMENT. Normalization is record-local,
as in bcftools.

## Diagnostics and failure policy

R12. **Outcomes, stderr and exit status** (GPT 9, Claude 15, Gemini 8). ACCEPT-MOD, and the default
changes to match bcftools. Every body line is classified into exactly one outcome:
- normalized (kept or rewritten);
- out of scope (R7, S3): passed through byte-identical;
- problem: REF disagrees with the reference (including REF running past the contig end), a REF or ALT
  with letters outside ACGTN (e.g. IUPAC in the VCF), an ALT equal to REF (case-insensitive), POS 0,
  CHROM not in the reference.

Option `-c e` (default, as bcftools): the first problem stops the run with exit code 1 and a stderr
message naming the line; stdout is then a prefix of what a successful run would write. Option `-c w`:
each problem line is passed through byte-identical with one stderr line (`REF_MISMATCH`, `NON_ACGTN`,
`ALT_DUP`, `UNKNOWN_CHROM`, with CHROM and POS, bcftools-style). Exception: CHROM not in the reference
always stops the run (bcftools stops too). On success, exit 0 and a stderr summary with the count of
each outcome. All of this is inside `run` (R1), so it is proven. bcftools modes `x` and `s` are not
offered (DOCUMENT).

R13. **REF = ALT missing from decision 1** (GPT 9, Gemini 7.3). ACCEPT, as the `ALT_DUP` problem in
R12 (bcftools: ERR_DUP_ALLELE, an error under `-c e`).

## Windows

R14. **Window laws allow "always None"** (GPT 10, Gemini 9). ACCEPT. Add a sufficiency law: if the
window covers every reference base the record's normalization reads (from one base before its final
POS to the end of its REF), the windowed result is `Some`. With R1, this gives progress of the retries:
each retry at least doubles the window, which eventually covers the whole contig.

## Header

R15. **Command line in the header** (Claude 11, GPT 12, Gemini 10.2). ACCEPT. Two lines are added:
`##framebender_normVersion=<version>` and `##framebender_normCommand=norm <args>`, where each byte
below 0x20 or 0x7F in the arguments is replaced by a space. The value is never empty and never starts
with `<`. No date, so output is deterministic (bcftools adds `; Date=...`; DOCUMENT).

R16. **Header line position** (Gemini 10.1). ACCEPT. The lines are inserted immediately before the
`#CHROM` line, wherever it is. A file with no `#CHROM` line is an error (exit 1).

## Wording and minor

R17. **Decision 3 wording** (Claude, GPT 7, Gemini 12.4). ACCEPT. "An event that begins at the first
base of the contig takes the base after it as its padding base; otherwise the padding base is the one
before the event." Tan et al.'s definitions are quoted verbatim in the law comments.

R18. **`shift` comment** (Gemini 12.1). ACCEPT: qualify it to `1 <= k < pos` on a valid variant.

R19. **POS above 2^31-1** (Gemini 12.2). REJECT. bcftools reads 64-bit positions; a POS beyond the
contig is already a problem (R12). No extra rule needed.

R20. **Unused definitions in types.bend** (Gemini 12.3). ACCEPT: the file comment will be corrected;
`Base.of_fasta` becomes part of R1's FASTA law.

R21. **bcftools comparison pinned** (GPT 15, Claude 14). ACCEPT. Compatibility claims are against
bcftools 1.24 `norm -f` (and `-c w` for the warn mode), measured on a differential corpus kept in
`test/` (GIAB chr22, scrambled records, edge cases), with the documented differences above listed in
one place. Comparison is on exact bytes, with each documented difference named.
