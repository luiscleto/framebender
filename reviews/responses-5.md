# Drafter's responses, round 6 (review of the rewritten laws)

Round-6 answers: `reviews/claude-r6.md`, `reviews/gpt-r6.md`, `reviews/gemini-r6.md`. None found a false
law. The files are updated (`LAWS.bend` now has 15 laws; all type-check; `examples.bend` passes).

Q1. **FASTA whitespace** (GPT 1, Gemini 2.2). ACCEPT. `Fasta.ws` is exactly space, tab, CR, used for
both names and sequence lines; any other byte (VT, FF, '*') is kept as a letter and reads as N.

Q2. **Empty and repeated contig names** (GPT 2, Gemini 2.1). ACCEPT. `Fasta.parse` drops a header with an
empty name or a name already seen, with its lines (`Fasta.keep`), so `Fasta.find(fa, "")` is None and
`truth` answers Unknown.

Q3. **End of file given once** (Gemini 1). ACCEPT. `DSt` has `eof`; asking for more after the end of
the file gets nothing, so such a machine never stops and fails `machine`.

Q4. **The driver converted reference letters** (Claude 1). ACCEPT. A `Known` answer now carries the
contig's letters as written (`raw`, a String); `Contig` holds the raw letters; the machine (and `judge`)
apply `B.Bases.of_fasta`. The trusted driver only copies bytes at the .fai offsets, without line breaks.

Q5. **Command line and usage errors** (GPT 5, Claude 3). ACCEPT. `Norm.start` now takes the command line;
law `machine` quantifies over argv with `B.Args.parse(argv) == Some{Cfg{o, ref, vcf}}` and concludes that
the program opens exactly those two paths and produces `run(fasta, vcf, o)`. New law `usage`: a command
line `B.Args.parse` rejects gives `Norm.Usage{}`. The trust boundary comment on `machine` names what
remains trusted: reading files, answering reads through the .fai, writing, exiting, printing `B.usage`
with exit 2 on `Usage`, and "error: cannot read <path>" with exit 2 when a file cannot be read.

Q6. **UNSORTED message** (Claude 2, Gemini 3, and the garbled comment Claude 5). ACCEPT Claude's version
(amends P2): `Stop{Unsorted, at, prev}`: `at` is the line that would come out of order, `prev` the line
already written that it would have to come before (the run keeps the last item written, not just its
key); `prev` is None when a CHROM comes back after another one. Rendered as `... before ...`.

Q7. **`enough` comments** (Gemini 4). ACCEPT: the comment now includes the input POS; UNKNOWN_CHROM
requires the Unknown answer (`is_unknown`). **Law list comment** (Gemini 5): fixed (`grouped_in`).
**`bound` comment** (GPT 4, second half): reworded to say exactly what the formula counts.

Q8. **Streaming: the machine law compares only the final report** (GPT 3). REJECT, with reasons. Every
observable result (stdout bytes, stderr messages, exit code, the files opened) is fixed by `machine`.
Immediate header output and stopping reads at the first fatal record do not change those results;
they are memory and latency properties, like the doubling of windows (Q9). The agreed responses
(M5, P4) defined *what* is written on a stop, not *when* bytes leave the process, and a trace law would
be a large proof for a property the benchmarks measure directly (peak memory, time to first byte).
The code will stream, and NOTES.md will record this as outside the laws.

Q9. **Window doubling not enforced** (GPT 4). REJECT for the same reason: R14/P1 agreed on what a
sufficient window is (`window_enough`) and that retries end (`bound` in `machine`); the growth rule is
how fast they end, a performance property. A machine that grows windows by one base is correct and slow,
and the benchmark against bcftools would show it.

Q10. **main.bend still uses the old interface** (Claude 4). Known: the driver is rewritten with
`Norm.step` once these laws are approved.
