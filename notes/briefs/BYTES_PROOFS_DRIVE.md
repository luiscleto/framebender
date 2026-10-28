# Phase B proof area "drive" (the simulation's step level): brief

Your earlier area is done; this is a new one. Prove the five deliverables in
`proof_b_drive.bend`:
- `pump_ok`: pumping from a good state ends a step well;
- `step_chunk`, `step_eof`, `step_ref`: one driver input each;
- `start_ok`: the program's first state.

Each is `?TODO`, with its statement fixed. `StepG` says what a step ends with:
- the output buffer reads as text (`E.out`);
- what it wrote and said moves to the driver's side;
- the new state is good and stands for the same report;
- by next: More (no source, before the end of the file), Ask (reads within 2^31 letters,
  kept as asked), or Finish (the report is the driver's).

## Read first, in order

1. `notes/bytes_proofs.md` (plan, rules, technique), `notes/bytes.md` (design).
2. `proof_b_sim.bend`: `StP`, `mkSt`, `WF`, `report`, `measure`, `AdvG`, and `adv_ok`. The
   per-line lemma is another agent's work, still `?TODO`; call it as it is.
3. `proof_b_drive.bend`: `StepG`, `more_ok` and your deliverables.
4. The code, `norm.bend`:
   - `step`, `go`, `pump`, `fuel.src`, `out`, `md.take` (`NR.take`, `ms.take`), `left`,
     `idle`, `finish` (`fin.mb`, `fin.ms`, `fin.ms.go`), `feed`/`feed_eof` and helpers,
     `set_win`, `start`;
   - `MACHINE.bend`'s driver definition (`dstep`, `absorb`, `truths`).
5. Lemmas to build on (call them even if still `?TODO`):
   - `proof_b_run.bend`: `run_take`, `run_finish`, `run_reserve`, `run_start`, `of_str`;
   - `proof_b_lines.bend`: `pend_add`, `pd_len`, `join_ok`, `eof_ok`, `pd_empty`,
     `piece_src`, `lf_ok`, `lines_eof`, `lines_nolf`, ...;
   - `proof_b_cache.bend`: `win_truths`, `parts_ok`;
   - `proof_b_enc.bend`: `out_ok`, `enc_bt`, `enc_ok` (proven);
   - `proof_b_frame.bend`: `finish_pre`, `run_pre`, `settle_inv`.
6. The old String machine's step level, for the shape (lemmas `PL`, `MS`, `AS`, `STEP`,
   `fin_ok`): `proof_machine_sim.bend` and `notes/proof_machine.md`.

## Route (suggested)

- First state and prove two helper lemmas of your own:
  - `out`: handing out a step's output keeps the state good and the report the same,
    with O and N extended by what was handed out (byte mode: `run_take`; String mode:
    `ms.take`, which hands out at most 2^30 bytes);
  - `finish` from an `Ended` or idle-at-end state.
- Then `pump_ok` by induction on the fuel. Case-split `Norm.advance`'s result through
  `adv_ok`'s `AdvG`. Fuel never runs out, because `measure <= f` and each `Went` lowers
  `measure`.
- Then the three step lemmas, through `feed`/`feed_eof`/`set_win` and `pump_ok`.
- `start_ok`: `Norm.start` with `run_start`, `pd_empty`, `WNone`.

## Not in this brief (the next step, once this is done)

The budget: driver steps and reference reads within `M.bound`. The law `machine` needs it
on top of these lemmas. Do not start it; report when the five deliverables are done.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_drive.bend`'s deliverable bodies and new `proof_b_drive_*.bend`
  files.
- Check with `timeout 1800 test/bcheck.sh proof_b_drive.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Other areas' TODOs will show; they are not yours.
- No git commits.
- If a statement is false, stop and report why, with a counterexample.
- Keep notes in `notes/bytes_proofs_drive.md`.

Work until done or about five hours, then finish with a report.
