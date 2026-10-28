# Phase B proof area "budget" and the law `machine`: brief

Your earlier area is done; this is a new one, the last piece. Prove `machine` in
`proof_b_machine.bend` (MACHINE.bend's law, restated with `+`). The simulation already
gives partial correctness:
- `proof_b_sim.bend` (`adv_ok`, definitions in `proof_b_simdefs.bend`): one line;
- `proof_b_drive.bend` (`pump_ok`, `step_chunk`, `step_eof`, `step_ref`, `start_ok`): one
  driver step.

Those may still be `?TODO` (other agents); call them as they are. What is missing is the
budget: `M.drive` must stop within `M.bound(argv, fasta, vcf, cs)` steps and at most that
many reads. That means a potential `need` on driver states, which:
- every `M.dstep` lowers by at least one;
- every step's reads do not exceed (reads + need never grows);
- is at most the bound at the start.

## The driver and the bound

- `MACHINE.bend`: `dstep`, `absorb` (the `good` flag: `E.out` of every buffer is `Some`,
  and `E.reqs_ok` of every Ask), `drive`, `result`, `bound`. The bound is
  `|cs| + 3 + args_len(argv) + (|vcf| + 1) * (|fasta| + 3)`.
- The old String machine's proof of the same shape: `proof_machine_sim.bend` (`need`,
  `bud`, `cost`, `asks0`, `askdec`, `Ok`, `STEP`, `drive_good`, `start_ok`, `machine`) and
  `notes/proof_machine.md`.
  - Its Fasta facts are reusable: `proof_machine_fasta.bend`, `clen_le`: a contig has at
    most |fasta| letters.
  - So is "at most |vcf| + 1 lines": `proof_machine_lines.bend`, `N2`. These files may not
    check any more; copy what you need into your own files.

## The steps, by kind (code: norm.bend)

- A piece (`Chunk`) or the end of the file: `|cs| + 1`.
- The last step (`Finish`).
- `Ask` steps:
  - **reads for the current line: at most three `Want`s per line** (norm.bend):
    - the fast path asks at most once per line (`fneed`);
    - the slow path asks on the line's first try (`back` still 100) with `Req.of`;
    - once the window has grown it asks `parts(c, 0, e)`, the contig from 0 to the end
      of REF (`slow.reqs`). That window holds every later try for the line
      (`proof_b_cache.bend`: `req_holds`, `zero_holds`), so the line is then decided
      without asking again.
    - `back` and `fneed` reset to 100/False when a line is done.
  - **`Yield`**, byte mode: a step yields only after `ow >= 2^30`, and `take` sets `ow` to
    0, so a yielding step handled at least one line.
  - **`Yield`**, String mode: hands out at most 2^30 bytes of pending output per step.
  - **Pump fuel**: never runs out (fuel >= measure; `pump_ok`).
- **Reads per Ask** (the number of parts): `Norm.parts` splits a window into reads of at most 2^31 letters
  (`proof_b_cache.bend`, `parts_ok`: all but the last are full). The count is not one in
  general: a contig of more than 2^31 letters, or a REF that long, gives several.
  - Suggested accounting: give each line the allowance `|line| * (|fasta| + 3)`, since the
    sum of line lengths is at most `|vcf| + 1`. A Want with window `W` asks
    `k <= 1 + W / 2^31` reads.
  - `W <= back + len(REF) + margin + ahead`. Here `margin + ahead` =
    `Nat.pow(2n, 16n) + Nat.pow(2n, 24n)`, below 2^31: prove it generically.
  - `back` doubles, and the window grows only while REF fits the contig.
  - Pick whatever potential makes the proof simplest. Write it down in your notes first.
- **String-mode yields:** the pending output comes from the lines' outputs. Bounding it
  may need an upper bound on a normalized record's text length (`Rec.rebuild`). If that
  gets hard, say so and propose a code change (for example, a String-mode step that
  hands out its pending output in one buffer when it fits 2^31) before proving around
  it.

## Freedom and limits

- You may add statements of your own, about `advance`'s Want and Yield paths, in your
  own files, and prove them. Do not edit other areas' files or their statements.
- If the law cannot be met without a code change, stop and report the change you need
  (the lead decides).

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_machine.bend`'s `machine` body and new `proof_b_budget*.bend`
  files.
- Check with `timeout 1800 test/bcheck.sh proof_b_machine.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- No git commits.
- Keep notes in `notes/bytes_proofs_budget.md`.

Work about five hours, then finish with a report: the potential, what is proven, and
what is left.
