# Claude, round 4

  Round 4: Claude

  Verdicts

  M1 (MALFORMED always stops): AGREE. This removes the counterexample all three
  of us gave, and the "no UNSORTED" law holds again. Your [run] check covered
  only blank lines and a non-numeric POS. The corpus should also check how
  bcftools handles lines with fewer than 8 fields and an empty allele in the ALT
  list (A,,G), and document any difference.

  M2 (ordering state): AGREE. I re-checked the proof with this state. A flush
  writes b only when key(b) + w ≤ inpos(current). Any later line d on sorted
  input then has key(d) > inpos(d) − w ≥ key(b). So d can never sort before b. A
  change of CHROM resets the last key written.

  M3 (FASTA parsing): AGREE. Keeping the first of two contigs with the same name
  agrees with how samtools faidx builds the .fai. Any remaining mismatch is
  covered by the R1 premise that the .fai agrees with the FASTA.

  M4 (end-of-file repair): DISAGREE (should fix). It does not say whether a file
  that ends with LF has an empty "last line" after that LF. With M1, that line
  would be MALFORMED.
  - Example: ##fileformat=VCFv4.3\n#CHROM…INFO\nchr1\t1\t.\tA\tG\t.\t.\t.\n.
    Splitting on LF gives an empty last piece. Read naively, M4 gives it an LF,
    M1 makes the resulting blank line MALFORMED, and every well-formed file
    exits 1.
    - This is the natural reading if run is written with String.split(vcf,
      '\n'), which is how types.bend already splits fields.
  - Change that would make me agree: "A line ends just after each LF. If the
    input does not end with LF, the remaining bytes form the last line and get
    the repair. An empty remainder is not a line, so a 0-byte input has no lines
    and stops on the missing #CHROM."

  M5 (stdout and stderr on a stop): AGREE. One gap in it is N1 below.

  M6 (annotations): AGREE. Narrowing the guarantee to copied bytes plus
  preserved ALT indices is true. Triggering the event only on a real change of
  representation answers my round-3 N5 and GPT's point 18.

  M7 (integer range): AGREE. A record is NORMALIZED only if its REF matches the
  reference, so the output POS and END are at most the contig length. Larger
  values come out only for contigs longer than 2^31 − 1, so there is no
  unbounded output to put a limit on (this answers GPT 17).

  M8 (wording): AGREE.

  M9 (windows per outcome): AGREE.

  M10 (bcftools differences to document): AGREE.

  New problems

  N1 (should fix): the order of steps for each body line is not fixed, so stdout
  on a stop is not determined. M2 flushes the whole buffer when the CHROM
  changes. M1 and R12 stop on a problem line, but neither says whether the
  CHROM-change flush happens before the stop.
  - Example: -c e, w = 100000.
    a. chr1 100 . A G . . . is buffered and not yet written.
    b. chr2 5 . A C . . . arrives, and chr2 has G at position 5, so it is
       REF_MISMATCH.
    c. If the run flushes for the CHROM change first, the chr1 record is in
       stdout. If it classifies first, it is not.

    R1 requires stdout to be exact, so run cannot be written until this is
    chosen.
  - Fix: state the order of steps for every body line:
    a. Classify the line.
    b. If the outcome stops the run (MALFORMED, UNKNOWN_CHROM, or a problem
       under -c e), stop with no flush.
    c. Otherwise, handle a change of CHROM: flush the buffer, and stop with
       UNSORTED if this CHROM's run already ended.
    d. Insert the line and apply the flush rule.

    With this order, what -c e writes before stopping does not depend on whether
    the bad line changes CHROM. It also agrees with M2, which flushes before
    the repeated-CHROM UNSORTED stop.

  I found no blockers.

