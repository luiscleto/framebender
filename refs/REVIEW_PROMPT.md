You are reviewing a draft specification for a VCF variant normalizer, a command-line tool used as
`framebender norm -f ref.fa in.vcf > out.vcf`. The specification is written as laws in the Bend
language. A human who is not a genomics expert will approve the laws one at a time; after that, the
implementation must be proven to satisfy every law by a proof checker. The laws are therefore the only
guarantee: a law that is wrong, too weak, or misses a case means wrong output could pass the checker.

Read these files in the current directory (read-only; do not modify anything):
- `LAWS.bend`: the definitions and the 16 laws (the main object of review).
- `types.bend`: types and text parsing used by the laws; part of the spec.
- `refs/VCFv4.3.txt`: the VCF 4.3 specification.
- `refs/tan2015.txt`: Tan, Abecasis and Kang, "Unified representation of genetic variants",
  Bioinformatics 2015 (defines normalized = left-aligned + parsimonious).
- `refs/bcftools-norm.txt`: the `bcftools norm` manual section.
Use only these sources. Functions named `Norm.*` are the implementation the laws constrain: judge the
laws, not the implementation.

Bend notes: `law name:` followed by `for x: T` lines is a claim for every x; `for h: {a == b : T}` is a
hypothesis; `{a == b : T}` is equality; `+x` only marks a variable as reusable; `&&` and `||` are
boolean; `match` is pattern matching; `Nat.sub` is truncated subtraction (never below 0); lists are
0-based, VCF positions are 1-based.

Proposed design decisions (review these too):
1. In scope: records whose REF and ALT are each one or more of the letters A, C, G, T, N (any case),
   so exactly one ALT; POS a number >= 1; at least 8 tab-separated fields; no END key in INFO.
   Everything else (multiallelic, symbolic `<...>`, breakends, `*`, missing ALT `.`, header lines)
   passes through byte-identical and is counted on stderr.
2. REF not matching the reference (compared case-insensitively; reference letters other than A, C, G,
   T, in either case, are read as N): the record passes through unchanged, with a warning on stderr.
3. Normal form: Tan et al.'s left-aligned and parsimonious; at position 1 the shared base comes after
   the event, as the VCF spec says.
4. Plain-text VCF in and out (compressed files go through `bgzip -dc`). The header is copied, with one
   `##framebender_normCommand=` line added just before `#CHROM`.
5. Compatibility target: output identical to `bcftools norm -f ref.fa` on in-scope records; where
   bcftools and the laws disagree, the laws win and the difference is documented.
6. Output order: records are buffered and sorted by their new position within each CHROM; the output
   is guaranteed sorted only when no record moves left by 100000 bases or more (such records are
   reported on stderr).
7. A record already normalized comes out byte-identical (even in lower case); a changed record has
   POS, REF and ALT rewritten (alleles in upper case) and every other byte kept.

For each definition and law, answer:
(a) Does the Bend mean exactly what its English comment says?
(b) Does it match the sources (Tan et al.'s definitions; the VCF spec)?
(c) Gaps: could an implementation satisfy every law and still produce wrong or surprising output?
    Consider at least: position 1 and the start of a chromosome, the end of a chromosome, N in the
    reference or in alleles, lower-case (soft-masked) reference and lower-case alleles, IUPAC codes,
    long repeats, REF mismatch, multiallelic/symbolic/`*`/breakend records, INFO/END, header lines,
    line endings (CRLF), sorting, and the windowed reading of the reference.
(d) Is any law false, so that no implementation could satisfy it? Give a concrete counterexample.
Then review the 7 design decisions: is any of them wrong or risky for real use, and where would the
result differ from `bcftools norm -f`?

Report a numbered list of findings. For each: the name of the law, definition or decision; severity
(blocker / should fix / minor); the problem; a concrete example where possible (contig sequence,
VCF line); a suggested fix. Be concrete and brief. If something is correct, you do not need to say so.
