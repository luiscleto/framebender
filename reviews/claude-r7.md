# Claude, round 7

● Round 7: Claude

  I agree with all ten items, and I found no new blocker or should-fix problem.
  Where the response says a file changed, I checked it, and the change matches
  the response.

  Verdicts

  Q1 (FASTA whitespace): AGREE.
  - Fasta.ws matches exactly space, tab and CR, and is used for both names and
    sequence lines.
  - fasta_vt shows that VT is kept and read as N.
  - If a header ever contains VT or FF, the .fai premise covers the difference
    from samtools faidx.

  Q2 (empty and repeated contig names): AGREE.
  - Fasta.keep adds a name to the seen set only when it keeps that contig.
  - fasta_two covers both cases: a header > with an empty name, and a second
    >c1.

  Q3 (end of file given once): AGREE. A machine that asks for more after the end
  of file gets no further input from dstep.more. drive then runs out of steps,
  result is None, and the machine law fails, which is what we want.

  Q4 (letter conversion moved into the machine): AGREE. This resolves my round-6
  item 1.
  - Known now carries the raw letters; truthful and covers work over those raw
    letters.
  - judge, and judge_in in norm.bend, apply Bases.of_fasta themselves.
  - The trusted driver now only copies bytes.

  Q5 (command line and usage errors): AGREE.
  - machine now ties Norm.start(argv) to the paths opened and to run(fasta, vcf,
    o), with o taken from Args.parse.
  - The usage law covers command lines that Args.parse rejects.
  - The driver comment fixes exit code 2 and the message for usage errors and
    for files that cannot be read.

  Q6 (UNSORTED message): AGREE.
  - flush now carries the last item written, and prev is that item's location.
  - prev is None when a CHROM comes back after another one.
  - run_unsorted_note now names line 5, before line 3.

  Q7 (comment fixes): AGREE. The enough comment now mentions the input POS.
  is_unknown for UNKNOWN_CHROM is stricter than before and can still be
  satisfied.

  Q8 (streaming not covered by a law): AGREE with the rejection.
  - machine fixes every byte, message and exit code.
  - When bytes leave the process, and how much is held in memory, cannot change
    those results.
  - Benchmarks are the right check for it, and it should be recorded in NOTES.md
    as outside the laws.

  Q9 (window doubling not enforced): AGREE with the rejection. It only affects
  speed. window_enough and bound already guarantee correct results and that the
  run ends.

  Q10 (main.bend still on the old interface): AGREE. It is a known follow-up.

  New problems

  None at blocker or should-fix level. One wording point for the trust-boundary
  comment on machine: "the .fai must agree with the FASTA file" could say
  exactly what it promises. For each contig, the .fai length is len(Contig.raw),
  and the bytes the driver reads through the .fai are the matching slice of
  Contig.raw.

