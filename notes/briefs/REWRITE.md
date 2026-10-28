# Rewritten records on bytes: brief for the rewrite agent (phase C)

Read first:
- `README.md` and `docs/DEVELOPMENT.md`: what framebender is and how it is checked.
- `notes/bytes.md`: the packed-bytes design (phase A), including the fast path's refinement
  argument against the String path.
- `notes/bytes_proofs.md` and the area notes it points to: how the bytes machine was proven
  (phase B), and "Where it got hard".
- `notes/briefs/PROVING.md`, `notes/fast.md`, `notes/speed.md`: proof patterns, and the SIGPROF
  sampler earlier agents used to profile (perf is not installed; no sudo).
- `../NOTES.md`: lessons from the lawful-* packages (big numbers, affinity, memory).

## Goal

A record that normalization rewrites still takes the slow path: its line is decoded to a `String`
and judged by the old String code. Phase A measured 60% of that time in reference counting of
shared Strings (`term_drop`, `span_fade`) in the String judge and `Rec.rebuild`.

| input (wall, `-c w`, to a file) | bcftools 1.24 | framebender (`main`) |
|---|---|---|
| chr22, 50,284 records, almost none rewritten | 0.12-0.14 s | 0.12-0.16 s |
| `data/scr.vcf`, 20,739 records, nearly all rewritten | 0.08 s | 5.2 s |
| whole genome, 4,048,342 records | 8.5-8.6 s | 9.1-9.7 s |

Bring `scr.vcf` as close to bcftools as you can, without making chr22 or the whole genome slower.
Raw caller output has many records to rewrite, so this is the path that decides whether the tool
is usable in practice.

## Fixed (do not edit)

- The science layer: `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`.
- The contract: `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`.
- `../lawful-*`: read only. If you need a new primitive or law there, describe it to the lead and
  wait. A new law needs a review first.
- The driver (`main.bend`, `io64.c`, `io64.js`): trusted code. Ask the lead before changing it.

## Yours

`norm*.bend`, new code files, `proof_*.bend`, `PROOF.bend` (its imports and proof bodies; the law
statements it proves come from `LAWS.bend` and `MACHINE.bend`), `examples*.bend` cases, and notes
in `notes/rewrite.md`.

## Steps

1. **Profile and plan.** Profile `scr.vcf` on the `main` build. Then write a plan in
   `notes/rewrite.md`: where the time goes, the design, what has to be proven, the estimated
   proof size, and what you expect to gain. Two directions, yours to judge by the profile:
   - a bytes path for rewritten records: trim and left-align on the packed line and the cached
     reference window, writing the new record straight into the output, proven equal to what the
     slow path gives (the same refinement pattern as the fast path's `WHit`);
   - a cheaper slow path, e.g. less sharing of Strings, if the profile says that gets most of it.
   Report the plan to the lead (print it and stop) before starting the proofs at scale.
2. **Code.** Outputs identical (checks below), with timings.
3. **Proofs.** `PROOF.bend` must check with `bend` and with `--verdict`, with no ?TODO in its import
   graph. You may dispatch sub-agents through Herdr, each in its own workspace
   (`herdr workspace create --cwd <dir> --label <name> --no-focus`, then
   `herdr agent start <name> --kind claude --pane <workspace>:p1 -- <args>`). Track them, and close
   their workspaces when they are done.

## Rules

- **Memory.** Every `bend` check goes through `test/bcheck.sh` (4 GB cap, at most two checks at
  once across all agents). Never close a goal about a big `Nat` by computation (`{==}`): the
  checker builds it in unary and can fill the machine (it once used 22 GB).
- **Timing.** `nice -n 19` and a `timeout` on every build and run. Set `BEND_NO_TELEMETRY=1`. One
  benchmark at a time across all agents: check `pgrep -af "bend |fb_|bcftools"` first. Interleave
  framebender and bcftools runs, and give ranges.
- **Git.** Work on the branch `rewrite`. Do not commit, push or switch branches: the lead commits
  by path. Build other binaries into `data/tmp` with `git worktree` if needed.
- Any change that keeps a statement's meaning but rewrites it (as `le31` did) is the lead's call:
  ask.

## Checks

- `test/compare.sh` against bcftools: 0 differing records on `data/chr22.fa data/hg002.chr22.vcf`
  and on `data/chr22.fa data/scr.vcf`; exactly 1 on `test/edge/ref.fa test/edge/sorted.vcf` (the
  `<DEL>` record); 0 on the whole genome (`TMPDIR=data/tmp`, `data/hg38.fa data/hg002.all.vcf`;
  delete the outputs afterwards).
- stdout, stderr and exit code byte-identical to `data/tmp/fb_ref` (the `main` build) on every
  `test/edge/*.vcf`, chr22 and `scr.vcf`, under `-c e` and `-c w`, plus `-w 1`, `-w 5` and
  `-w 300` on a few of them. Add inputs for the cases your path handles: multi-allelic records,
  `*`, lower case, N, REF mismatch, records at a contig's start, deletions that move a long way,
  CRLF.
- The tiny-limit builds of phase B (`notes/bytes_proofs.md`) again, if your path reads the
  reference differently.
- The gate's four steps (`check.sh`), each through `test/bcheck.sh`.

## Report

Keep `notes/rewrite.md` up to date. At the end, report:
- the times (chr22, scr, whole genome; framebender against bcftools);
- the comparison results and the gate;
- every statement you changed below the laws, and why (counterexample, or a true fact that was
  missing);
- anything the lead should decide.
