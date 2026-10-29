# Responses to the compressed-output law review (phase H, 2026-10-29)

Prompt: `COMPRESS_LAW_PROMPT.md`. Reports: `claude-compress-law.md`, `gpt-compress-law.md` (GPT 6.1
Sol), `grok-compress-law.md` (Grok 4.7). All three accept law `output` and the grammar with no
blocker: the grammar is deterministic, every command line accepted before keeps the same `Cfg`
(`Opts.args` included), and the law cannot hold for an unrelated reason. The decisions below go
to the compress agent for step 2; the driver gets its own review after implementation.

## Decisions

1. **The end-of-file block is written only when the exit code is 0** (Claude; GPT and Grok
   preferred sealing on any machine finish). A `-c e` or UNSORTED stop leaves a file without the
   end-of-file block, as bcftools does (it exits without `bgzf_close`), so a stopped run's file
   is never taken for a complete one. GPT found that `bgzip -t` 1.24 returns 0 on a file missing
   only that block (it warns), so the tests check the last 28 bytes directly. Law machine's
   comment: "a BGZF file is complete exactly when the run succeeded"; decompressed, it is the
   output bytes written so far.
2. **After a write error nothing more reaches the file** (Grok, Claude, GPT): stop at the first
   failed write, write no end-of-file block, exit 2. Short writes are retried until the whole
   block is written. Driver errors mid-run stop the compressor and writer threads (or `_exit`)
   without the end-of-file block.
3. **The level is sticky, as in bcftools** (Grok, measured on bcftools 1.24): the last explicit
   digit counts; `-Oz` and `-Ov` change only the type; 6 only if no digit was given. Examples:
   `-Oz0 -Oz` is level 0, `-Oz9 -Ov -o x.vcf.gz` is BGZF level 9. Verify on bcftools before
   writing the examples.
4. **The output file is opened lazily** (Claude): at the first `out_write` (or at `out_close`
   for an empty output), after the first VCF piece was read, so an input that fails to open or
   is not BGZF never empties an existing `-o` file. Test: the old file is unchanged after each
   input error.
5. **The input check uses the open descriptors** (all three): `fstat` of the VCF, FASTA and
   `.fai` descriptors against `fstat` of the output, before `ftruncate`; also refuse an output
   that is the same file as stderr (GPT; `-o x.vcf.gz 2> x.vcf.gz`).
6. **Bounded writer queue with backpressure** (GPT, Claude): `out_write` waits while more than a
   stated number of blocks (about 2 x N) wait to be written; a buffer is owned until written.
   Test: a stalled pipe reader and incompressible data, with peak RSS.
7. **Copy the carried tail before freeing its block** (Grok): the tail of a window carried into
   the next call lives in the Bend block that `out_write` frees; copy it out first, and at
   `out_close` queue it, wait, free, then write the end-of-file block.
8. **Prove `output_ok`** (all three): `Args.output` is `Some` exactly when `Args.parse` is; a
   `None` after `Begin` is an internal error (exit 2), never a fallback to plain stdout.
9. **Tests, corrected** (Grok, Claude): when `Sink.z` is false the file equals the plain stdout
   (the level is unused); when true it equals `plain | bgzip -l L` at every `--threads`,
   including `-Ov -o x.vcf.gz` and the sticky levels. Add: one incompressible window (the stored
   fallback, against bgzip); generated lines of 65279/65280/65281 bytes, a header ending at a
   window boundary, CRLF, a header longer than a window; a round trip through framebender's own
   reader; the writer once under ThreadSanitizer and ASan; full-disk and failed-write cases check
   the file too (no end-of-file block), not only the exit code.
10. **Comments** (GPT, Claude, Grok): law `output`'s comment says it covers the machine's report,
    apart from the driver's own errors for the `-o` file, and (as law `threads` does) that a
    compressed run can run out of heap where the plain one does not. `type Sink`: "level: unused
    when z is False" (Claude). docs/LAWS.md gets Claude's sentence: for any accepted command line,
    removing every `--threads`, `-o` and `-O` gives the same text, messages and exit code.
11. **Examples** (GPT): missing `-O` value, refused `-oFILE`, invalid-first repeated `-o`, repeated
    `-O` with levels, `-o` as a bare input path versus `./-o`.
12. **Notes accuracy** (Claude): the count of new examples (27 `def`s, not 31); "Not taken from
    bcftools" also lists `-Ou`/`-Ob` with a `.vcf` path, a bare level `-O5`, and a repeated `-o`
    with an invalid earlier value; check bcftools' handling of `-Oz9 -o x.vcf` and `-Ov5` or drop
    "as in bcftools".

Kept as drafted, all three agreeing: the extension wins over `-O`; `-o` and `-O` stay out of the
header; default level 6, with `-Oz1` in the README; `-o` refuses an input.

## Who caught what (Q4)

- Claude only: lazy open (an input error emptied the old file); EOF only on success; the notes'
  inaccuracies.
- Grok only: the sticky level (measured on bcftools); the carried tail read after its block is
  freed; the test oracle wrong for plain `-o` outputs; the heap sentence.
- GPT only: `bgzip -t` returning 0 without the end-of-file block (tested); stderr and `-o` on the
  same file.
- Two or three: the bounded queue (GPT, Claude); nothing after a write error (Grok, Claude, GPT);
  `fstat` of open descriptors (all); `output_ok` (all).
