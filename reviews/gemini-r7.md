# Gemini, round 7

  ### Verdicts on Q1–Q10 (responses-5.md)

  • Q1: AGREE — Verified in Fasta.ws, Fasta.name.go, Fasta.strip, and
  fasta_vt: only space, tab, and CR (after LF splitting) are treated as FASTA
  whitespace, while other bytes stay in raw and map to N via Bases.of_fasta.
  • Q2: AGREE — Verified in Fasta.keep, Fasta.parse, and fasta_two: empty and
  duplicate contig names are dropped with their sequence blocks, so Fasta.
  ￺find(fa, "") is None{} andtruthh returns Unknown{}.
  • Q3: AGREE — Verified in DSt and dstep.more: B.Eof{} is delivered at most
  once, and requesting B.More{} afterward stalls with done = None{} and fails
  machine.
  • Q4: AGREE — Verified in Contig, Ans, judge.contig, known.ok, truth.of,
  and judge_in.ans: Known carries raw FASTA sequence letters and IUPAC/case
  conversion happens inside the proven code.
  • Q5: AGREE — Verified in usage, Norm.start, launch, machine, and
  usage` (law): valid argv fixes both opened file paths and Opts, invalid
  argv yields Norm.Usage{}, and exit-2 usage/read errors are documented at
  the trust boundary.
  • Q6: AGREE — Verified in Note, Note.render, Flush, flush, and
  run_unsorted_note: tracking the last written Item and reporting prev with
  "\tbefore\t" (and None{} on a repeated CHROM) gives an unambiguous message
  on every UNSORTED stop.
  • Q7: AGREE — Verified in LAWS.bend:18 (grouped_in), is_unknown, enough,
  and bound: all three comments and the UNKNOWN_CHROM predicate now match
  their definitions.
  • Q8: AGREE — machine already fixes all observable outputs (opened paths,
  stdout, stderr, exit code, and single-EOF termination); streaming latency
  and peak memory are operational properties appropriately left to benchmarks
  and NOTES.md.
  • Q9: AGREE — window, window_enough, and bound guarantee correctness and
  termination; window growth rate is a performance property rather than a
  safety law.
  • Q10: AGREE — Updating main.bend after the 15 laws and Norm.step are
  finalized matches the intended workflow.
  ──────
  ### New Problems in the Updated Laws

  None — I found no new blocker or should-fix problems in the updated
  LAWS.bend and types.bend; all 15 laws are jointly satisfiable and match the
  agreed specification.

