# Claude, round 6 (rewritten laws)

● I found no false law and no blocker in the rewritten laws. There is one
  should-fix item, on the trust boundary of the machine law, plus four minor
  points.

  What I checked:
  - Classification: judge applies the agreed order and the END rule.
  - Ordering: run follows the per-line step order and the flush rule.
  - Text: line endings, FASTA parsing, the added header lines, message events
    and exit codes.
  - Window laws: the per-outcome window answers.
  - Multiallelic: the variant definitions.

  I re-checked by hand that sorted, grouped_in, no_unsorted, twice_run and
  window_enough can be proven. run calls Norm.var, which is safe:
  normal_unchanged and one_form together fix Norm.var on every valid variant, so
  run is a well-defined function. I confirmed in the Bend base library that
  Char.is_alpha is ASCII-only, as [A-Za-z]+ requires, and that String.split
  keeps empty pieces.

  1. machine law and the answer type B.Ans: should fix. A known-contig answer
     carries bases that have already been converted, so the unproven driver does
     the conversion of reference letters to bases. That covers upper-casing,
     IUPAC codes to their first base (R5), and any other character to N. In
     round 1 we agreed the driver would only return reference bytes. The law
     assumes truthful answers, and "truthful" is defined through Fasta.parse, so
     nothing proves the driver applies that conversion.
     - Example: reference >c / CRG and the record c 2 . A G. The spec reads R as
       A, so the record is NORMALIZED. A driver that reads R as N (the round-1
       behaviour) returns [C,N,G], and the proven machine then reports
       REF_MISMATCH. Every law still holds.
     - Fix:
       - A known-contig answer carries the contig's raw sequence bytes. The
         driver only drops the line terminators, following the .fai layout.
       - "Truthful" is defined over a Fasta.raw that keeps those bytes.
       - The machine applies Base.of_fasta itself.

       The trusted part is then just "copy bytes at the .fai offsets".
  2. UNSORTED event (emit.ready): minor. When the line that comes out of order
     is the arriving line itself, both locations name the same line. Example
     run_unsorted_note gives Some{At{5,c,4}} twice. The useful second line is
     the last one written, line 3 (c 2). Fix: keep the location of the last
     written item next to last, and report it as "before" that line. This
     adjusts P2, so treat it as a suggestion.
  3. Trusted driver: minor. The laws and the driver comment do not say what
     happens on a usage error (Args.parse returns None, e.g. -w 0) or when the
     FASTA, .fai or VCF cannot be read. R21 compares exit codes, so this needs
     fixing: name the exit code and the stderr text in the driver comment.
  4. main.bend: minor (expected while Norm.step is a stub). It still uses the
     old interface (B.Win, Norm.entry, B.Entry), which no longer exists. It has
     to be rewritten as the driver of Norm.step, as described under item 1.
  5. Comment on B.Note in types.bend: minor wording. "and cause the line whose
     arrival made it come out" is garbled. It should read: "at is the line that
     would come out of order; cause is the line whose arrival caused the flush
     (none at the end of input)."

  Nothing the plan agreed on is missing from the laws, apart from the
  usage-error behaviour in item 3.

