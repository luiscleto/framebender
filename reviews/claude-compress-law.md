# Law review: compressed output (`-o`, `-O`), notes/compress.md

## Context
Read-only review requested by reviews/COMPRESS_LAW_PROMPT.md: review law `output`, the parser
grammar, the author's five questions, the driver design and clarity. No repository edits. Draft
in data/tmp/gz/draft/ matches the diffs in notes/compress.md (orig = branch tree).

## Verdict
No blockers. ACCEPT the law and the grammar as drafted, after the should-fix items below
(mostly driver design and the end-of-file rule).

## Findings

1. **should fix: output file opened before the VCF's format is known.** compress.md "Effects",
   `Io.out_open` "Called once in run.fai, after the FASTA, the .fai and the VCF are open". The
   VCF's kind is only detected on the first `Io.read_block` (io64.c:448, `io64_kind`), after the
   open. So `-o old.vcf.gz` with a plain-gzip input ("unsupported gzip"), "no BGZF in this build",
   or a VCF that opens but cannot be read (a directory) truncates the user's existing file for a
   run that never started. bcftools reads the input header before opening its output. Fix: open
   the output lazily, at the first `out_write` (or at `out_close` for empty output), so the
   input-is-output check and `ftruncate` happen only after the first VCF piece was read. Add a
   test: an existing `-o` file is unchanged after each of those input errors.

2. **should fix: EOF block on a stopped run (author's Q3).** A `-c e` or UNSORTED stop ends with
   code 1 (run.bend:357, 369) and a text missing every record after the stop. Writing the EOF
   block then gives a `.vcf.gz` that `bgzip -t`, `tabix` and htslib accept as complete. bcftools
   on error exits without `bgzf_close`, so its file has no EOF block. Fix: write the EOF block
   exactly when the exit code is 0. "Decompressed, the file is the output bytes" still holds
   (htslib only warns), framebender's own reader refuses the file ("bad BGZF"), and the rule
   is simpler to state: "a BGZF file is complete exactly when the run succeeded". Change the
   MACHINE.bend comment ("whatever its code") and the test "-c e stop: a complete file" to match.

3. **should fix: the compressed-block queue has no stated bound.** "Writer thread" and "Memory":
   the main thread waits only for compression, not for writing. With a slow disk or a slow pipe
   reader (`-Oz | slow`), finished blocks pile up, up to the whole compressed file (hundreds of
   MB, more on cohort files). Today's plain write is synchronous and has backpressure. Fix: bound
   the writer queue (for example, `out_write` waits while more than 2 × N blocks wait to be
   written) and state the bound. Add a slow-reader test that measures peak RSS.

4. **should fix: `Args.output` None silently means stdout plain.** "What the proofs need" item 4:
   the driver "treats None as stdout plain". If a later edit made `Args.output` disagree with
   `Args.parse`, `-o x.vcf.gz` would quietly go to stdout and no law would notice. Fix: prove
   `output_ok` (cheap: `Args.done` and `Args.sink.done` match the same `ArgSt` pattern after the
   same `Args.go`). Or make None after `Begin` an internal error (exit 2), not a fallback.

5. **should fix: after a write error, nothing more may reach the file.** "Writer thread": "later
   blocks are dropped", but `out_close` "writes the 28-byte end-of-file block". State that once
   an error is recorded, `out_close` writes no EOF block. Otherwise a torn block plus a valid EOF
   could follow a short write. Also say what driver errors in mid-run (`die` → exit 2 while the
   compressors and writer are running) do: stop the threads or `_exit` without the EOF block, so
   an exit-time teardown cannot crash and turn exit 2 into a signal.

6. **minor: the input check should use the open descriptors.** "Not an input": compare the
   output's `(st_dev, st_ino)` with `fstat` of the already-open VCF, FASTA and .fai descriptors,
   not `stat` of their paths. This gives the same result for symlinks and `/dev/stdin < in.vcf`,
   and leaves no window between the open and the check. Optionally include fd 2 when stderr
   is a regular file (`2> x.vcf -o x.vcf`).

7. **minor: law output's comment over-promises.** MACHINE.bend draft, law output: "changes
   nothing the program writes" / "same ... exit code". With `-o`, the driver can add its own
   errors ("output is an input", "cannot write <path>", exit 2). These are already listed under
   law machine's "does not cover". Say so in one clause: "apart from the driver's own errors for
   the `-o` file (law machine's comment)". Same for "Decompressed, the file is exactly the output
   bytes": add "when the run ends with the machine's code".

8. **minor: `Sink` keeps a level that means nothing.** `sink_ext_plain` gives
   `Sink{Some{"out.vcf"}, False, 9n}`. Either set the level to `Args.level()` when z is False, or
   document "level: ignored when z is False" on `type Sink`.

9. **minor: notes are inaccurate in two places.** "All 31 new examples hold": the diff has 27
   `def`s (draft examples.diff agrees). And bcftools' handling of `-Oz9 -o x.vcf` and `-Ov5`
   ("level ignored") is not in data/tmp/gz/t1.sh, which tests only `-Oz -o n_e.vcf`. Run it, or
   drop "as in bcftools". Under "Not taken from bcftools", also list: `-Ou`/`-Ob` with a `.vcf` or
   `.vcf.gz` path (bcftools writes by the extension: n_u.vcf is plain), a bare level `-O5`, and a
   repeated `-o` with an invalid earlier value. framebender refuses all of these.

10. **minor: test-plan additions.** (a) Round trip through framebender's own reader: a run on
    its `-Oz` output equals the run on the plain output. (b) A generated-text test of the cutter
    against `bgzip -l L`: line lengths around 65279/65280/65281, a header ending exactly at a
    window boundary, CRLF, and a header longer than one window. (c) The writer under
    ThreadSanitizer/ASan once. (d) The tests from items 1 and 3.

## Answers

**Q1, laws.** Law machine already fixes the text as `L.run(fasta, vcf, parse(argv).opts)`. Law
output says the output words change neither `Cfg` (via `Opts.args`) nor the launch. Together
with law usage, they say what a user needs: for any accepted line, dropping the output options one
at a time (each sits where an option is expected) gives the same text, messages and code. Nothing
the laws cover is changed by `-o`/`-O`. They cannot be true for an unrelated reason: `hb` and `he`
are not vacuous, `out_opt` is pinned by positive and negative examples, and machine forces `Some`
on accepted lines. What stays trusted: `Args.output`'s meaning in the driver (where and in what
format), the writer and the file handling. The draft states this plainly. With bgzip byte
identity as an exact oracle, the test plan is a fair substitute for a proof, given items 1, 3,
5 and 10.

**Q2, parser.** The grammar is deterministic: in a `PNone` position, `-o` and `-O` are exact
matches, checked before the `-O` prefix; anywhere else every word is a value. Every
previously accepted line is unchanged byte for byte, `Opts.args` included. Before, in a `PNone`
position, `-o`, `-O` and `-O…` set `opt` and were refused, and value positions are unchanged. I
checked the drafted examples: `-f -o in.vcf` (FASTA `-o`), `-o --threads` (path), missing value
(`out_noval`, and `-O` at the end leaves `PType`), glued forms, `-Ox -Oz` refused, last wins
(`sink_last`, `sink_dash`), extension in any case. All are correct. `-o in.vcf` is accepted by
the parser and refused by the driver, which is right: it is a property of the file, not of the
words.

**Q3–Q7, the author's five questions.**
1. Extension wins: yes. It matches bcftools, keeps the name honest, and keeps law output's
   premise local to one option. Document it, and do not warn: a warning would change stderr.
2. Not in the header: yes. It keeps `bgzip -dc` equal to the plain run and the header
   reproducible.
3. EOF on a stopped run: no. Write it only on exit 0 (item 2).
4. Default level 6: yes. It gives bgzip's exact bytes (the test oracle) and bcftools' sizes, with
   `-Oz1` documented.
5. `-o` refusing an input: yes. Keep it, with `fstat` of the open descriptors and the check
   done after the first read (items 1 and 6).

**Q8, clarity for a scientist.** In docs/LAWS.md, state the consequence in one sentence:
"for any accepted command line, removing every `--threads`, `-o` and `-O` gives the same text,
messages and exit code; those options only choose speed, and where and how the text is
written". Optionally describe threads and output there as one rule about "driver options".
