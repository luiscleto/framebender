# Gemini 4 Argon review (Antigravity CLI 1.4.7, plan mode, high; ~83 min of reasoning)

Copied from the Herdr terminal (workspace gemini-review); line wrapping is the terminal's.

  1. small_moves, in_order, and Design Decision 6 — Severity: blocker
      • Problem:
          1. small_moves requires Nat.is_le(outpos(e), inpos(e)) ("and none
          moved right"), which is not mentioned in in_order's comment or
          Decision 6, and fails on valid VCF variants: trimming shared
          leading bases via drop_first moves POS right (outpos > inpos).
          2. Because hm: {small_moves(w, es) == True{}} is a single file-wide
          hypothesis over all es, if even one record in the entire VCF trims
          a leading base (outpos > inpos) or shifts left by >= w bases (e.g.,
          across a >= 100 kb tandem repeat or N-gap), small_moves(w, es)
          becomes False{} and in_order holds vacuously—imposing zero sorting
          or grouped guarantees anywhere in the file.
      • Example: Contig ACGT; input lines chr1    1    .    AC    AG    .
PASS    . (normalizes
      to POS=2, REF=C, ALT=G, so inpos=1, outpos=2) and chr1    1    .    A
T    .    PASS    ..
      Here small_moves(100000n, es) == False{}, so Norm.Buf.run could
      scramble record order and interleave chromosomes across the whole file
      and still pass the proof checker.
      • Suggested fix: Remove Nat.is_le(outpos(e), inpos(e)) from small_moves
      (a min-heap that flushes buffered entry b only when outpos(b) + w <=
      inpos(cur) sorts arbitrarily large right-moves whenever left-moves are
      < w, since outpos(b) + w <= inpos(cur) <= inpos(c) < outpos(c) + w
      implies outpos(b) < outpos(c)). Make grouped preservation an
      unconditional law (grouped(es) ==> grouped(Norm.Buf.run(w, es))), and
      scope small_moves per-CHROM rather than globally across the whole file.
  2. Rec.parse, untouched, rewritten, and Design Decision 1 — Severity:
  blocker
      • Problem: Rec.parse's comment states Header lines ("#...") never
      parse: their second field is not a number, or they have no second field,
      and untouched states header lines come out byte-identical. Both claims
      are false: Rec.parse never inspects field 0 (CHROM), so any #... or ##.
      .. line with 8+ tab-separated fields matching POS/REF/ALT/INFO (as well
      as data lines with empty CHROM = "", forbidden by
      VCFv4.3.txt` §1.6.1 & §7.2) parses as Some{v}. When v is valid and
      unnormalized, rewritten forces Norm.line to rewrite that #... line
      rather than leaving it untouched.
      • Example: Contig AC; commented-out record #chr1    1    .    AC    AG
.    PASS    . (or
      ##note=x    1    .    AC    AG    .    .    ., or empty-CHROM     1    .
AC    AG    .    PASS    .).
      Rec.parse returns Some{Var{1n, [A{}, C{}], [A{}, G{}]}}, and rewritten
      rewrites it to #chr1    2    .    C    G    .    PASS    ..
      • Suggested fix: Conjoin Bool.not(String.starts_with(line, "#")) &&
      Bool.not(String.eq(Rec.field(fs, 0n), "")) into Rec.parse (and require
      pos >= 1n there too so POS = 0 is rejected as out-of-scope per Decision
      1 rather than in valid).
  3. Unconstrained end-to-end pipeline (LAWS.bend:10-14, Entry,
  Base.of_fasta) — Severity: blocker
      • Problem: LAWS.bend:10-11 constrains Norm.var, Norm.line, Norm.line_in,
      Norm.header, and Norm.Buf.run only as isolated units. No law specifies
      FASTA parsing (Base.of_fasta is never referenced in LAWS.bend), contig
      lookup (or missing contigs), header/body partitioning, w = 100000n, or
      how Entry is built from line and Norm.line(seq, line). In particular,
      Rec.parse returns None{} on all out-of-scope records (multiallelics,
      <DEL>, *, INFO/END): if unverified driver code defaults inpos = 0,
      outpos = 0 when Rec.parse is None{} instead of reading POS
      independently, all out-of-scope records sort to the start of each
      chromosome while satisfying every law. Similarly, feeding FASTA \n/\r
      characters to Base.of_fasta inserts N{} bases at every FASTA line break,
      and failing to trim FASTA header text after whitespace (>chr1 LN:1000)
      fails to match CHROM = "chr1".
      • Example: Input lines chr1    100    .    A    G    .    PASS    . and
chr1    200    .    AT    A,ATT    .
      PASS    .. Constructing Entry{"chr1", 0n, 0n, line2} when
Rec.parse(line2)
      == None{} emits POS=200 before POS=100 while passing all 16 laws.
      • Suggested fix: Add spec definitions and an end-to-end law covering
      FASTA record parsing (contig name up to first whitespace; stripping
      \r/\n/whitespace before Base.of_fasta), Entry construction (chrom =
      field 0, inpos and outpos parsed via Pos.read regardless of Rec.parse,
      text = Norm.line(seq, line)), missing-contig behavior, and w = 100000n.
  4. Base.of_fasta, Base.is_eq, and Design Decision 2 (IUPAC codes and N
  equality) — Severity: should fix
      • Problem:
          1. VCFv4.3 mismatch: VCFv4.3.txt` §1.6.1 requires IUPAC ambiguity
          codes in the reference to be converted to their alphabetically
          first concrete base (e.g., R -> A, Y -> C), whereas Base.of_fasta
          and Decision 2 convert all non-ACGT letters to N{}. A spec-
          compliant VCF record with REF=A at an R reference site is falsely
          treated as a REF mismatch, and left-aligning onto R writes N into
          REF/ALT instead of A.
          2. N treated as identical to N: Base.is_eq returns True{} for N{}
          == N{}, treating unknown bases (and disjoint IUPAC codes like R =
          A/G and Y = C/T) as known-identical nucleotides in shift and
          parsimonious, which can alter the variant's biological meaning.
      • Example: FASTA contig CRG (R at pos 2, read as CNG).
          • Compliant SNP chr1    2    .    A    G    .    PASS    . fails
valid (N != A) and is
          skipped with a warning.
          • Insertion chr1    3    .    G    NG    .    PASS    . (N inserted
after R: haplotype
          CRNG) normalizes to chr1    1    .    C    CN    .    PASS    . (N
moved before R:
          haplotype CNRG).
      • Suggested fix: Map standard IUPAC ambiguity codes in Base.of_fasta
      per VCFv4.3.txt` §1.6.1 (R,W,M,D,H,V -> A; Y,S,B -> C; K -> G; others -
      > N), and either disallow N == N matches during shifting/trimming or
      explicitly document N == N if intentionally matching bcftools norm -f.
  5. CRLF (\r\n) line endings (Rec.has_end, Norm.header, Design Decisions 1,
  4, and 7) — Severity: should fix
      • Problem: VCFv4.3.txt` §1 & §1.2 requires supporting both \n and \r\n
      line separators, but CRLF handling is missing:
          1. If lines are split on \n keeping trailing \r (to preserve input
          bytes per Decisions 1 & 7), then on an 8-column VCF line ending in
          a bare END\r key in INFO, Rec.is_end_key checks String.eq("END\r",
          "END") == False{} and fails to exclude the record; and Norm.header
          inserts "##framebender_normCommand=" ++ cmd with no \r, producing
          mixed LF/CRLF newlines.
          2. If \r is stripped on input and \n emitted on output, CRLF inputs
          are not preserved byte-identically as stated in Decisions 1 and 7.
      • Example: Contig ACA; 8-column CRLF line chr1    2    .    CA    A    .
PASS
      IMPRECISE;END\r has Rec.has_end("IMPRECISE;END\r") == False{} and gets
      rewritten instead of passed through.
      • Suggested fix: Strip optional trailing \r when splitting input lines
      (and either emit \n consistently like bcftools norm, updating Decisions
      1 & 7 to mean byte-identical within each line excluding line terminator,
      or re-attach the input's newline style consistently including on the
      added header line).
  6. in_order and kept_all (chromosome permutation and same-POS tie-breaking)
  — Severity: should fix
      • Problem:
          1. grouped only requires each CHROM to appear in a single
          contiguous run; it does not require Norm.Buf.run(w, es) to keep
          chromosomes in the same order as es. Reversing or permuting
          chromosomes satisfies both kept_all and in_order, violating
          ##contig ordering and bcftools norm -f compatibility.
          2. out_ascending uses Nat.is_le, leaving tie-breaking at equal
          outpos unspecified (an implementation may reverse already-
          normalized records at the same POS).
      • Example: Input [Entry{"chr1", 10n, 10n, l1}, Entry{"chr2", 5n, 5n,
      l2}] output as [Entry{"chr2", 5n, 5n, l2}, Entry{"chr1", 10n, 10n, l1}]
      satisfies both kept_all and in_order.
      • Suggested fix: Add a law that the list of distinct CHROM runs in
      Norm.Buf.run(w, es) equals that of es whenever grouped(es) == True{},
      and require stable tie-breaking (preserving input order when outpos(a)
      == outpos(b), matching bcftools norm -S pos).
  7. Design Decision 1 vs bcftools norm -f and tan2015.txt:43-70
  (multiallelic records, INFO/END, and REF == ALT) — Severity: should fix
      • Problem:
          1. Multiallelics: Both tan2015.txt:43-70 (where 37.2% of
          multiallelic indels and 65.8% of complex multiallelics in 1000
          Genomes needed normalization, Table 1) and bcftools norm -f
          normalize multiallelic sequence-resolved records directly. Skipping
          all multiallelics (including ,* spanning-deletion records standard
          in joint-called VCFs) leaves polymorphic repeats unnormalized
          alongside normalized biallelic records in the same file.
          2. INFO/END on precise deletions: VCFv4.3.txt` §3 & §5.3 and
          bcftools +fill-tags permit INFO/END on sequence-resolved variants;
          bcftools norm -f normalizes them and updates END, whereas Decision
          1 skips them.
          3. REF == ALT omitted from Decision 1: Decision 1's scope criteria
          include REF == ALT records (e.g., REF=A, ALT=A or REF=a, ALT=A),
          whereas valid excludes B.Bases.eq(ref, alt) so untouched passes
          them through.
      • Example: Contig ACAAA; chr1    3    .    CAA    CA,CAAA    .    PASS
. and chr1    3    .    CAA
      CA    .    PASS    END=5 are both normalized by bcftools norm -f to
POS=1, but
      passed through unchanged by framebender. And chr1    2    .    a    A
.    PASS    .
      matches Decision 1's prose but has in_scope == False{}.
      • Suggested fix: Either support multiallelic normalization (Tan et al.
      Algorithm 1 applies directly to >= 2 alleles) or document prominently
      under Decision 5 that inputs with multiallelics must be pre-split
      (bcftools norm -m-), document the INFO/END divergence from bcftools
      norm -f, and add REF != ALT (case-insensitive) to Decision 1.
  8. Design Decision 2 vs bcftools norm -f (silent exit 0 on REF mismatch) —
  Severity: should fix
      • Problem: Plain bcftools norm -f ref.fa defaults to -c e (exit
      immediately with non-zero status on REF mismatch;
      bcftools-norm.txt:36-40), whereas Decision 2 acts like bcftools norm -c
      w -f ref.fa (passing bad sites through unchanged with a stderr warning).
      In automated pipelines, supplying the wrong reference build (e.g.,
      GRCh37 VCF with GRCh38 FASTA) will exit 0 and silently emit an
      unnormalized VCF.
      • Example: Contig TTTT; input chr1    2    .    CA    C    .    PASS
.. bcftools norm -f
      aborts with an error; framebender outputs the unnormalized line and
      succeeds.
      • Suggested fix: Fail with non-zero exit by default on REF mismatch
      (matching bcftools norm -f, with -c w to opt into warn-and-keep), or
      document this prominently under Decision 5.
  9. window and window_whole (degenerate windowing allowed) — Severity:
  should fix
      • Problem: window proves soundness when Norm.line_in returns Some{r},
      while window_whole requires Some{...} only when given the entire
      chromosome (Win{0n, seq, len(seq)}). An implementation returning None{}
      on every proper sub-window satisfies all laws while forcing whole-
      chromosome loading (~249 Mb as a Bend List) on every contig.
      • Example: On a 249 Mb chr1, Norm.line_in(Win{900n, slice(seq, 900n,
      200n), 248956422n}, "chr1\t1000\t.\tA\tG\t.\tPASS\t.") == None{}
      satisfies both window and window_whole.
      • Suggested fix: Add a sufficiency law requiring Norm.line_in to return
      Some{Norm.line(seq, line)} whenever Rec.parse(line) == None{} (or pos -
      1 + len(ref) > clen), and whenever [off, off + len(bases)) covers [Nat.
      sub(outpos, 2n), pos - 1 + len(ref)).
  10. header, lead, after, and Design Decision 4 — Severity: minor
      • Problem:
          1. header's comment says the command line is added "just before the
          #CHROM line", but lead stops at the first non-"##" line: on hs =
          Nil{} it emits a 1-line headerless output, and if hs has no leading
          ##fileformat= line, "##framebender_normCommand=..." becomes line 1,
          violating VCFv4.3.txt` §1.4.1 (##fileformat must be line 1).
          2. Universal quantification for cmd: String allows cmd = "", cmd
          starting with '<', or cmd containing \r/\n, producing malformed
          meta lines under VCFv4.3.txt` §1.2 & §1.4. (Also note bcftools norm
          adds ##bcftools_normVersion=... and appends ; Date=... unless --no-
          version is passed.)
      • Example: Norm.header("",
      ["#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO"]) produces
      "##framebender_normCommand=" on line 1 (empty value and before any
      ##fileformat).
      • Suggested fix: Prefix the fixed command name inside Norm.header (e.g.,
      "##framebender_normCommand=framebender norm " ++ sanitize(cmd)
      stripping \r/\n, guaranteeing non-empty and not starting with '<'), and
      split specifically before #CHROM when present.
  11. kept_normal, rewritten, Rec.rebuild, and Design Decision 7
  (case/leading-zero divergence and stale INFO tags) — Severity: minor
      • Problem:
          1. Keeping already-normalized lines byte-identical (kept_normal)
          while uppercasing alleles and rewriting POS via Nat.show on changed
          lines (rewritten) breaks canonical uniqueness at the text level
          (two equivalent input records can emerge with 01/ac/a vs 1/AC/A)
          and differs from bcftools norm -f, which canonicalizes POS and
          allele case uniformly.
          2. Preserving INFO verbatim leaves alignment-specific annotations
          such as INFO/CIGAR (VCFv4.3.txt` §1.6.1) or HOMSEQ stale when
          alleles are trimmed or shifted.
      • Example: Contig ACA; chr1    01    .    ac    a    .    PASS    . stays
01    .    ac    a, while
      equivalent chr1    2    .    ca    a    .    PASS    . becomes 1    .
AC    A. On AC, chr1    1    .    AC
      ￺AG    .    PASS    CIGAR=2M rewrites to chr1    2    .    C    G    .
PASS    CIGAR=2M (CIGAR=2M
      no longer matches 1-bp C>G).
      • Suggested fix: Document both differences relative to bcftools norm -f
      (and warn users that INFO/CIGAR/HOMSEQ are not recomputed), or
      canonicalize POS/REF/ALT case and leading zeros on all in-scope records.
  12. shift, Pos.read, types.bend:5, and Design Decision 3 (minor comment and
  spec inaccuracies) — Severity: minor
      • Problem:
          1. shift's comment claims v moved k bases to the left, both alleles
          ￹keeping their lengths, which fails when k >= pos (Nat.sub(pos, k)
          clamps to 0n) or when v extends past seq (harmless as called inside
          left_aligned on valid variants, where 1 <= k < pos, but inaccurate
          as a standalone spec comment).
          2. Pos.read accepts arbitrary-precision Nat (including "0" and >=
          ￹2^31), whereas VCFv4.3.txt` §1.3 & §7.2 defines VCF integers as
          signed 32-bit.
          3. types.bend:5 states LAWS.bend uses every definition here, but
          Var.eq and Base.of_fasta are unused in LAWS.bend.
          4. Decision 3 says "at position 1 the shared base comes after the
          event", which holds only when the indel event itself is before/at
          position 1; an indel at position 2 anchored at POS = 1 has its
          shared padding base before the event.
      • Example: shift([A{}, C{}], Var{1n, [A{}], [C{}]}, 2n) yields Var{0n,
      ￹[A{}], [C{}]} (shifted by 1, not 2, to invalid pos = 0n); on TAAA,
       Var{3n, [A{}, A{}], [A{}]} normalizes to Var{1n, [T{}, A{}], [T{}]} at
       POS = 1 with padding T before the deleted A.
       • Suggested fix: Qualify shift's comment (for 1 <= k < pos on a valid
       ￹variant), note 32-bit POS limits in Pos.read, remove unused Var.eq (and
        connect Base.of_fasta in a FASTA law), and rephrase Decision 3 to match
        VCFv4.3.txt` §1.6.1 ("when the event occurs at position 1, the shared
        base comes after the event").


