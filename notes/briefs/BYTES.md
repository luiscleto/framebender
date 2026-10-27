# framebender on packed bytes: brief for the bytes agent (phase A: code)

Read first:
- `../ARCHITECTURE.md`: the plan.
- `../spike/RESULTS.md`: what packed bytes cost, and how loops compile.
- `PROVING.md` and `notes/fast.md`: how framebender's code and proofs are organized, and what was
  already learned about speed.

## Goal

Rebuild framebender's implementation on packed bytes, so that it runs at about bcftools' speed:
- **today:** 4.5 s on chr22 and about 590 s on the whole genome;
- **bcftools:** 0.08 s and 7.4 s;
- **the measured prototype:** 0.10 s and 6.3 s sequential.

The output must stay byte-identical. This phase is code only: no proofs yet. Shape the code so the
proofs can follow, and write down the refinement argument as you go.

You work on the git branch `bytes` (already checked out). Do not touch `main`, and do not commit:
the lead commits.

## Fixed (do not edit)

- **The science layer:** `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`.
- **The contract**, revised by the lead on this branch:
  - `protocol.bend`: `In.Chunk{b: D.Bytes}`; `Ans.Known{clen, off, raw: D.Bytes}`.
  - `MACHINE.bend`: the driver definition feeds `P.Chunk{E.enc(c)}`, answers with `E.enc(...)`,
    and collects `E.text(o)`.
  - `bytes_enc.bend`: `enc`, the canonical packing (zero-padded, smallest block), and `text`.
  - The machine law's statement is unchanged.
- **`../lawful-words`, `../lawful-arrays`:** read only. Their laws are reviewed and their proofs are
  in progress.
- **`../lawful-bytes` and `../lawful-fields`:**
  - Use their operations: `B.find`, `B.find2`, `B.at`, `B.append`, `B.same`, `C.cut`, `C.num`, and
    the rest.
  - Do not change their laws or definitions.
  - You may replace operation bodies in `../lawful-bytes/bytes.bend` with faster word-at-a-time
    versions (see `../spike/pk.bend`, `rec.tpl`). Keep the signatures, keep
    `bend test/spot.bend` all True there, and list every replaced body in your notes: the proof
    agent will prove them.

## Yours

- `norm.bend`, `norm_line.bend`, `norm_run.bend`, and new code files.
- `Norm.Step`'s output becomes a `D.Bytes`. `MACHINE.bend` reads it as `Norm.Step{st, o, ns, nx}`
  with `o: D.Bytes`; keep that shape.
- The driver, `main.bend` and `io64.c`:
  - Read each VCF piece straight into a block packed as `E.enc` (a C effect, like
    `../spike/words2.c`).
  - Answer each reference read with an `E.enc` block.
  - Write each output buffer's bytes.

  The driver is trusted code: keep it small, and say in your notes exactly what it does. The lead
  will have it reviewed.

## Suggested design (yours to judge)

- **Fast path:** a record that is in scope and unchanged. That is all but 18 of the 4,048,342
  whole-genome records, and 1 of chr22's. Judge it on the bytes:
  - cut the first 8 fields (`C.cut`);
  - read POS (`C.num`);
  - look up CHROM;
  - compare REF with the reference answer's bytes (`B.same`, case-insensitive where the spec is);
  - check INFO for END;
  - check the normal form.

  The record's bytes then go to the output unchanged (`B.append`).
- **Slow path:** anything else (a record that changes, MALFORMED, out of scope, any doubt). Decode
  the line (`E.text` of its range) and run the existing String code (`J.*`, `Tan.normal`). It is
  proven, and rare.
- **The refinement argument for later:** the fast path's result equals the slow path's result on
  `E.text` of the same line. This is the same pattern as `J.same` (`notes/fast.md`).
- **The sorting buffer:** its items can keep each record's bytes (or a range of a retained buffer,
  using `B.shift` to drop what has been written), not Strings.
- **Piece size:** the driver's piece size is up to you (1-4 MB measured well). One piece must not
  exceed 2^31 bytes.

## Checks

- `test/compare.sh data/chr22.fa data/hg002.chr22.vcf` and
  `test/compare.sh data/chr22.fa data/scr.vcf`: 0 differing records each.
- `test/compare.sh test/edge/ref.fa test/edge/sorted.vcf`: exactly 1 differing record (`<DEL>`).
- stdout, stderr and the exit code byte-identical to the `main` branch's binary on every
  `test/edge/*.vcf`, chr22 and `data/scr.vcf`, under `-c e` and `-c w`. Build `main`'s binary
  once into `data/tmp/fb_main` with `git worktree` or `git show`, without leaving the branch.
- Whole genome, once chr22 is fast:
  - write both outputs under `data/tmp` (`/tmp` is RAM-backed, and too small);
  - run `TMPDIR=data/tmp test/compare.sh data/hg38.fa data/hg002.all.vcf`;
  - delete the outputs afterwards.
- The existing proofs break on this branch: that is expected in phase A. Keep `bend main.bend
  --check-only` passing apart from the expected unsafe or foreign-code report.

## Timing

Use `nice -n 19` and a `timeout` for every build and run. Set `BEND_NO_TELEMETRY=1`.

Two proof agents (`prove-words`, `prove-arrays`) are running `bend` checks on this machine. Before
each timing, check with `pgrep -af "bend "` that no other `bend` process is running, and wait if
one is. Time runs back to back. Report `+RTS --threads 1` and the default.

## Report

Keep `notes/bytes.md` with:
- the design;
- every change, with chr22 time before and after;
- the refinement argument (the fast path vs the String path);
- the driver's trusted code;
- the lawful-bytes bodies you replaced.

Stop when chr22 is under about 0.2 s and the whole genome is under about 10 s, or after about six
hours, and report:
- the times (chr22, scr, whole genome; framebender against bcftools);
- the comparison results;
- what the proofs will need.
