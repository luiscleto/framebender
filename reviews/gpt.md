I found no law that makes the 16 laws jointly unsatisfiable. The main defects are missing guarantees and differences between the comments, decisions, and formal claims. Examples below use `(POS, REF, ALT)`; `\t` denotes a tab.

1. **`in_scope`; reference selection — blocker.**  
   Its comment says “the contig named in its CHROM field,” but `Rec.parse` discards CHROM and nothing connects `seq` to the named reference. With `chr1=CAAA`, `chr2=CGAA`, record `chr2\t3\t.\tAA\tA\t.\t.\t.` should normalize to `(2,GA,G)`. Supplying chr1 instead produces `(1,CA,C)`, while every component law can still hold. FASTA decoding, including excluding headers and line separators, is also unconstrained.  
   **Fix:** specify and prove reference loading and CHROM lookup, including missing-contig errors, and connect them to the line laws.

2. **`Entry`, `kept_all`, `in_order`; command execution — blocker.**  
   Nothing requires an entry’s CHROM or positions to agree with its text, or requires one entry per input record. A caller can assign every entry `inpos=outpos=0`; the buffer can then satisfy its laws while output text is unsorted. `kept_all` preserves only the entries supplied to it.  
   **Fix:** add a command-level law connecting input records, normalization, truthful entry construction, buffering, header handling, and emitted bytes.

3. **`small_moves`, `in_order`; decision 6 — blocker.**  
   `small_moves` requires **no rightward movement**, whereas `in_order`’s comment and decision 6 mention only excessive leftward movement. Normalization can move right through prefix trimming. On `ACG`, sorted input `(1,ACG,ACT)`, `(2,C,T)` normalizes to positions `3,2`. No record moves left, but the sorting law’s hypothesis fails, permitting unsorted output.  
   **Fix:** allow rightward moves in the promised sorting condition and prove the buffer handles them.

4. **Decision 6; long repeats — should fix.**  
   The proposed warning-only policy permits output that violates VCF’s required position order. On a contig of 100002 A bases, `(100001,AA,A)` normalizes to `(1,AA,A)`, moving exactly 100000 bases. If a position-2 SNP has already been emitted, the output can become `2,1`. The bound must not limit normalization itself: `standard_form` still requires the full shift.  
   **Fix:** use a sorting fallback or fail explicitly when sorted output cannot be delivered. State the sorted-input prerequisite and the exact `>=100000` threshold.

5. **`kept_all`, `in_order`; decisions 5–6 — should fix.**  
   These laws permit arbitrary reordering of entire chromosome blocks and records tied at the same output position. Reversing chromosome-block order still satisfies `grouped` and `out_ascending`. Reversing tied records can also change the file again on a second run; `line_twice` does not prevent that.  
   **Fix:** preserve chromosome-block order and define a tie-breaker, preferably original record order, unless a different compatibility rule is explicitly chosen.

6. **`Base.of_fasta`; decision 2 — blocker.**  
   Mapping every non-ACGT reference letter to N conflicts with the supplied [VCF §1.6.1](/home/luisc/Work/framebender/refs/VCFv4.3.txt:364): disallowed IUPAC ambiguity codes must become their alphabetically first concrete base, such as `R→A`, `Y→C`. On reference `R`, a VCF record `(1,A,C)` is consistent with that rule but becomes a mismatch here. Collapsing distinct ambiguity codes also creates artificial N repeats through which normalization can shift.  
   **Fix:** implement the specified IUPAC conversion or explicitly reject such references and document the deviation. Separately state that the present equality treats N as a literal symbol, not a wildcard or proof of biological base identity.

7. **Decision 3; chromosome-start padding — should fix.**  
   “At position 1 the shared base comes after the event” confuses the record’s POS with the event’s location. On `AC`, `(1,A,AT)` inserts after the first base and correctly uses preceding padding; it is already normalized under these laws. `(1,AC,C)` deletes the first base and uses following padding. A blanket suffix-padding rule would conflict with `normal_unchanged`.  
   **Fix:** say “events beginning at the contig start require following padding.” Include explicit start/end examples; an insertion after the final base, such as `(2,C,CT)` on `AC`, requires no reference base beyond the contig.

8. **`rewritten`, `Rec.rebuild`; decision 7 — blocker.**  
   Preserving every other field can force incorrect annotations. On `AC`,  
   `chr1\t1\t.\tAC\tAT\t.\t.\tCIGAR=2M`  
   normalizes to `(2,C,T)`, but the required unchanged CIGAR still describes a two-base alignment. VCF defines CIGAR relative to the actual REF/ALT alleles. Excluding END alone does not solve annotation dependencies.  
   **Fix:** define which representation-dependent annotations are recomputed, removed, or cause exclusion. Preserve allele-indexed genotype fields where their interpretation remains unchanged.

9. **`untouched`, `in_scope`, `valid`; decisions 1–2 and 6 — should fix.**  
   No law constrains stderr, counts, warnings, or exit status. A completely silent implementation satisfies every law. Classification also differs from decision 1: `REF=ALT`, including `A/a`, meets its stated syntax but is excluded by `valid`. REF overruns at the chromosome end are likewise folded into the same Boolean rejection.  
   **Fix:** define explicit outcomes and diagnostic events for unsupported syntax, identical alleles, REF mismatch, out-of-range coordinates, missing contigs, and excessive shifts; prove the command reports them.

10. **`window`, `window_whole` — should fix.**  
    The safety law is useful, but “so the tool’s retries … end” is not established. An implementation may return `None` for every proper window and answer only for the whole chromosome. A caller may repeatedly request the same window or stop enlarging at a fixed cap, especially in long repeats. Both window laws still hold.  
    **Fix:** prove the retry procedure makes progress, obtains truthful offsets and contig lengths, and eventually supplies a sufficient window or reports an explicit failure. Distinguish reaching a window boundary from reaching the chromosome end.

11. **`Rec.fields`, `Rec.rebuild`, `header`; decisions 4 and 7 — should fix.**  
    The specification never defines whether a line string includes its terminator or how file bytes become these strings. Consequently, “byte-identical” does not guarantee preserving CRLF, trailing spaces in INFO values, or the final newline. VCF explicitly requires LF and CRLF support. This is a missing guarantee, not evidence that `Rec.rebuild` necessarily corrupts CRLF.  
    **Fix:** specify line bodies and terminators separately and prove serialization preserves untouched bytes, including the terminator of rewritten records.

12. **`header`; decision 4 — should fix.**  
    `cmd` is an unrestricted string inserted verbatim. A filename containing a newline can therefore make one command-history entry emit multiple physical lines and invalidate an otherwise valid header. Empty values and values starting with `<` also have special restrictions under VCF §1.4.  
    **Fix:** define a valid command encoding, escaping embedded control characters, and prove that exactly one well-formed metadata line is inserted before `#CHROM`.

13. **`Rec.parse`; header-exclusion comment — minor.**  
    “Header lines (`#...`) never parse” is not enforced. For example, `#note\t1\t.\tAC\tAT\t.\t.\t.` parses and, on `AC`, is rewritten. This is not a valid ordinary VCF header, but it disproves the unconditional comment and the promised handling of every header-like line.  
    **Fix:** classify headers explicitly using file context, or narrow the promise to valid VCF headers.

14. **Decision 1; partial normalization and `*` records — should fix.**  
    Passing multiallelic, symbolic, breakend, `*`, and END-bearing records through is a scope choice, but the result is not necessarily a fully normalized or internally consistent call set. On `GAAAT`, deletion `(3,AA,A)` becomes `(1,GA,G)`; a separate position-4 `A→*` record is preserved although the normalized deletion no longer spans position 4. Ordinary explicit alleles carrying END are also excluded, although VCF permits them.  
    **Fix:** document the record-local guarantee and unsupported cross-record relationships; define a policy for dependent `*` records. Clearly distinguish this subset from bcftools’ broader normalization capabilities.

15. **Decision 5; bcftools compatibility — should fix.**  
    “Identical to `bcftools norm -f`” is not established by these laws or the supplied manual. The manual lists mismatch modes `e/w/x/s`, but this excerpt does not identify the default; warning/pass-through should be compared against an explicitly selected mode. It also does not specify exact case preservation, N/IUPAC handling, leading-zero preservation, or tie ordering. The 100000-base window cannot be inferred from its `--site-win` description.  
    **Fix:** pin the bcftools version and options, distinguish semantic from byte compatibility, and specify concrete comparison cases and intentional exceptions. Do not claim undocumented behavior as a confirmed match or difference.
