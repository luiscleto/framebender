# Phase E, area D (task): plan_all and batch

## Status (2026-10-28)

DONE. `plan_all` and `batch` are proven; no `?TODO` of mine anywhere.

- `timeout 1800 test/bcheck.sh proof_e_task.bend --check-only`: "15 TODOs found", all inherited
  (LAWS.bend's 13 open laws and MACHINE.bend's `machine`, `usage`; any importer of them reports
  the same 15). Every helper file likewise reports only inherited TODOs (13 or 15).
- `--verdict` refuses any file with those TODOs, so the kernel check uses a harness as area F's:
  `proof_e_task_vh.bend` = PROOF.bend plus `import ./proof_e_task.bend as TK`.
  `timeout 1800 test/bcheck.sh proof_e_task_vh.bend --verdict` prints **ALL PROOFS CHECK** (38 s).
  The same harness with a false lemma added fails.

Files (all mine):
- `proof_e_task.bend`: the deliverables, plus assembly lemmas that name this area's pictures
  (helpers cannot import the file back): `rs_ok_eq`, `two_eq`, `pcok`, `plan_cons*`, `plan_step`
  (plan_all); `conv`, `mk_conv`, `tres_ok`, `fcons.k`, `force_true`, `force_false`, `force_ok`,
  `batch_k` (batch).
- `proof_e_task_buf.bend`: the plan's reads hand the buffer back whatever the indices (pair laws
  for num, rlf, cp, Q.text; any byte read is below 256), the reads are within 2^31 with bytes
  contigs, the last line (`last_b`, `last_ok`).
- `proof_e_task_first.bend`: field 0 of a line is the bytes before its first tab, also when the
  line ends with a CR (`fld0`, via `first_shrink`).
- `proof_e_task_piece.bend`: one piece's plan (`piece_t`): the `ok` decision, c0 = the first
  CHROM after k (`first_c0`), the prefix before the first LF (`pre_lf`).
- `proof_e_task_run.bend`: states equal once settled stay so under `run.go` (`go_cong`, from
  proof_b_frame_bl's `step_bl`); `run.go` over appended lines; one loop step composes (`go_step`).
- `proof_e_task_ms.bend`: advance keeps the String mode (`ms_stays`).
- `proof_e_task_loop.bend`: the task loop (`loop_ok`): invariant `Inv` (good picture, report,
  guard, eof False, the batch's options, and in the byte mode the lines handled so far with the
  run settling as the spec's run from `SD.rs0`); Went composes `Moved`; Want swaps in the next
  spare window (same run, same text); Idle gives TcOK's facts (in the body by `ib_step`, not
  stopped, WF's parts); fuel 0, Ended and Yield are dirty.
- `proof_e_task_start.bend`: task.run0 is a good run picture standing for `SD.rs0(c0, l)`.
- `proof_e_task_win.bend`: a task's window is `win_truths` of its read (`[r] = parts(r)` within
  2^31), or none for a contig name over 2^28 bytes.
- `proof_e_task_one.bend`: one task: the copy holds the piece, the start picture's invariant
  (`inv0`), and the loop's result (`one_ok`, `one_no`).
- `proof_e_task_vh.bend`: the verdict harness.

## Statement issues

- **c0's length (resolved by a code change).** The task's start run needs `RunInv`, so
  `NR.of_str(c0)` must be a good buffer; phase B's `PR.of_str` needs `len_le(c0, 2^30)`
  (`BF.put_str_ok` underneath: |c0| + 8 < 2^31). batch's hypotheses bound c0 only by its piece
  (up to 2^31 bytes), so a piece of about 2^31 bytes whose first CHROM has 2^31 - 8 .. 2^31 - 3
  bytes was not covered. The coordinator changed norm_par.bend's `task` to run only when
  `ok && Q.len_le(c0, 268435456)` (else `TOut{b, TDirty{}}`); no picture or statement changed.

- **k + 1 < len (resolved by a statement change).** The task's source `SB{b, k+1}` needs
  `src_ok` (k + 1 <= len). PcOK's decomposition `c = a ++ "\n" ++ after(c, k)` does not give it:
  with k + 1 > |c|, after(c, k) = "" and the decomposition still holds. The coordinator added
  the plan's own test `U32.is_lt(k + 1, len)` to PcOK's True case.

- **The copy near 2^31 bytes (resolved by a code change).** The task's copy
  `NR.put_bytes(BY.empty(NR.depth(len + 8)), b, 0, len)`: phase B's `put_bytes_t` needs
  len + 8 < 2^31 (room's no-grow branch); pieces up to 2^31 bytes take the grow path at
  2^31 - 8 .. 2^31. The coordinator made `task.len` run only when `len < 2^30`.
- **c0 is bytes (resolved by a statement change).** The start run's `NR.of_str(c0)` stands for c0
  only if c0 is bytes; PcOK's first-CHROM fact may draw on the text after the piece. PcOK's True
  case gained `E.is_bytes(c0)` (the plan reads c0 from the piece).

## Plan of the proofs

plan_all, by induction on the pieces; one piece:
- only the first line needs exact reasoning: the `ok` decision (minp <= len, k < len,
  k + 1 < len, its LF e1 < len, a tab t < e1) and c0 = bytes k+1 .. t-1 = field 0 of the
  first line of `after(c, k)` (cut_str's `cut_fld`, `body_eq`; proof_fast's `cut_split`);
- the last line, the POS digits and the reads: only "the buffer comes back" (pair laws, no
  bounds) and "a CHROM read is bytes" (any byte read is below 256), so every read's contig is
  bytes and every read is within 2^31 (plan.win's and plan.reqs's le31 tests, or empty).

batch:
- `HH.all = HD.force` (lawful-halves `all_force`), then each task;
- the copy: `NR.put_bytes` into an empty block;
- the start picture: `task.run0` (of_str, run_reserve), the source `SB{b, k+1}`, empty line end,
  window from `win_truths` (`[r] = parts(r)` by le31) or WNone; WF;
- the loop: invariant (picture, WF, report, guard, eof False, the composed Moved facts while in
  the byte mode); String mode stays String mode (Q's ms.* paths), so Idle there is dirty.

## What was hard

- **Direction of `%h : G(_)`.** With `h : {X == Y}`, `%h : G(_)` proves `G(Y)` from `G(X)`: to
  turn a goal's X into Y, pass a proof of `Y == X`. Most of my failed checks were this.
- **No destructuring of computed values.** A sigma from a lemma call cannot be matched; it must
  arrive as a parameter. Hence the `.k` continuation defs, pair-law statements
  (`f(...) == (buffer, Pair.snd(f(...)))`) instead of existentials, and recursion passed in as
  a lambda (`ih`, `rec`) since a def cannot call one below it.
- **Linear things.** `+x = ...` needs Data; Type-valued lets (an Adv, a TOut, a sigma) must be
  plain lets or inlined. A linear hypothesis used twice (plan_all's `hb`) goes to a helper once.
- **Matching order.** A parameter cannot be matched after a later one (ROK, tres_ok); a picture's
  match arm with `_` before a constructor (TResOK's `_ TDirtyP`) is stuck while the first
  scrutinee is a variable.
- **Big closed numbers.** `U32.to_nat(1073741824)` against `2^30` overflowed the checker's stack;
  keep the word abstract (`le_w` with `PL.lit_pow`), and use `NM.lt_c0` for the `0 + len + 8`
  shape of `put_bytes_t`.
- **Imports with open laws.** proof_fast.bend brings 13 TODOs (via LAWS.bend); its four cut
  lemmas are copied into proof_e_task_first.bend. `--verdict` needs the harness.
- **Statements.** Four gaps were found by reading the code against the start state's WF and
  RunInv (c0's length, k + 1 <= len, the copy near 2^31, c0 bytes); each was fixed by the
  coordinator before the proof went on.
