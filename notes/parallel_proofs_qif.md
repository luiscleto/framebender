# Phase E, area F ("qif"): notes

## Status (2026-10-28)

`step_chunk_pic`, `feed_line_ok` and `set_win_ok` in `proof_e_qif.bend` are proven; their
statements are unchanged. No TODO of mine is left.

- In the real tree, after area A's AdvG change: `proof_e_qif.bend --check-only` reports only the 15
  TODOs every file importing `MACHINE.bend` reports (its laws, proven only in `PROOF.bend`).
- `--verdict` refuses any file importing MACHINE (those 15 TODOs), so the kernel check uses a
  harness, `proof_e_qif_vh.bend`: `PROOF.bend` plus `import ./proof_e_qif.bend as QI`.
  `timeout 1800 test/bcheck.sh proof_e_qif_vh.bend --verdict` gives ALL PROOFS CHECK (40 s). A copy
  with one proof broken on purpose fails, so the harness does check these files.
- While area A's files were mid-edit, I checked against a copy of HEAD in my scratch directory
  (through the real `test/bcheck.sh`); same results there.

Files:
- `proof_e_qif_fed.bend`: `Fed(fa, c, p, X)`, the fed state (exactly `feed_line_ok`'s
  conclusion), and `core`: norm.bend's feed after the room (`Norm.feed.k`) for a piece given as
  any good buffer `C.BT(len, t)` of depth d with view `E.codes(c)`, from a state waiting for more,
  gives Fed. It is `proof_b_drive_chunk.bend`'s core with BTc(c) replaced by the buffer; its leaves
  return the fed state instead of calling `go_ok2`. The text helpers (`txt_e`, `txt_a`, `txt_j`,
  `emp_eq`, `bt0`) are reused from that file.
- `proof_e_qif_step.bend`:
  - `fed_go`: Fed, then go, is the step's guarantee (`DO.StepG2`): `rep_of` (same run, options and
    lines give the same report), the guard through the same run, then `DS.go_ok2`.
  - `step_chunk_pic_h`: by the state (the three cases more_ok rules out, as in step_chunk_h2),
    the room (`RN.run_reserve`, as chunk_mb2), then `core` and `fed_go`.
  - `feed_line_h`: `W.feed_line` is `Norm.feed.k` without `md.reserve`, so it is `core` itself.
  - `sw_nil`, `sw_eq`, `sw_wf`: step_ref_h2's two cases with the state named (nothing asked: the
    window stays; one window's reads asked: `PCA.win_truths` gives the window and wp_ok,
    `DS.mbw_of` gives mb_win).
- `proof_e_qif.bend`: `step_chunk_pic` and `feed_line_ok` are one call each; `set_win_ok` builds
  the state by `p` and `rs` (its conclusion names `StP.pd`, defined in this file, so the tuple is
  built here).

Unused hypotheses: `hcb` and `hcn` (the piece is bytes, at most 2^31 of them) in
`step_chunk_pic` and `feed_line_ok`, `hq` in `set_win_ok`. Phase B needed `hcb`/`hcn` only to get
the buffer's `D.ok` and view from `E.enc(c)`; here both are given.

## What was hard

- Nothing in the statements: phase B's core never used that the buffer was `E.enc(c)` beyond
  `D.ok` and the view, so a script replacing BTc(c) by `C.BT(len, t)` and the depth by d gave a
  core that checked at once.
- Bend: a `+` parameter must have a Data type, so `Norm.St` (holds functions) is taken erased
  (`-X`) and the `@cs -> ...` component is taken linear; a pair given as a computed value cannot be
  destructured (pass it to a lemma that takes it as a parameter), and its destructuring must come
  before any let or rewrite; a hypothesis of a deliverable is linear, so `set_win_ok` copies `hb`
  (`+hb2 = hb`) for its two uses.
