# Phase B proof area "frame": brief

Your earlier area is done; this is a new one. Fill in the proofs of the six deliverables in
`proof_b_frame.bend`: `settle_inv`, `step_pre`, `run_pre`, `finish_pre`, `settle_pre`,
`run_halted`. Each is `?TODO`, with its statement fixed.

They are spec-level facts (`run.bend`, `LAWS.bend` only) that the simulation needs:
- a report does not depend on what `P.settle` forgets: the last item's text, and a stopped
  run's buffer and last item;
- the spec goes on the same with what the driver already collected in front (`S.pre`).

The old String machine's proofs have most of this:
- `proof_fast_run.bend`, lemma `inv`: blanking the last item's text does not change the
  report. It used the old `NR.blank_st`; `P.blank_st` is the same definition.
- `proof_machine_frame.bend`, the `fr_*` lemmas: run.bend's functions commute with
  `pre`. It used the old `Norm.RunSt.out/notes/clear`; `P.RunSt.out/notes` and `P.clear`
  in `proof_b_defs.bend` are the same.
- `proof_machine_sim.bend`: `run_go_halted`.

Neither file checks any more, because the code they were about changed. Copy what you need
into new files `proof_b_frame_*.bend`, adapted.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_frame.bend` and new `proof_b_frame_*.bend` files.
- Check with `timeout 1800 test/bcheck.sh proof_b_frame.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: no TODO of yours left. The file imports `proof_b_sim.bend`, which has holes of
  other areas; you only need `S.pre`, so you may import `proof_b_defs.bend` alone in your
  helper files.
- No git commits.
- If a statement is false, stop and report why, with a counterexample.
- Keep notes in `notes/bytes_proofs_frame.md`.

Work until done or about four hours. Then finish with a report.
