# Phase E, area E2 (budget and assembly): notes

## Status (2026-10-28)

DONE up to the kernel check. `proof_e_machine.bend` passes `--check-only` with both deliverables
proven (`usage` directly, `machine` from the assembly) and no TODO of mine: the 15 TODOs it reports
are LAWS.bend's and MACHINE.bend's laws, which every area's file reports (proven in PROOF.bend).

Kernel check: the harness `proof_e_mach_vh.bend` is PROOF.bend plus `import ./proof_e_machine.bend`
(as areas D and F do). It fails nondeterministically on `--check-only`: "the machine stack
overflowed", or exit 139, on runs whose input is identical to passing runs. Bisected: PROOF.bend
with only LAWS.bend's proofs and E2's files passes; adding MACHINE.bend's two proofs
(`M.machine` forwards to phase B's assembly) tips it over; E1's harness core-dumps the same way.
`ulimit -s` is 16384 here. Asked the coordinator for a larger stack in `test/bcheck.sh` (theirs).

Files (all mine; each passes `--check-only` up to imported TODOs):
- `proof_e_mach_asm.bend`: the driver invariant Good (InvW + budget), drive_ok, the law.
- `proof_e_mach_inv.bend`, `proof_e_mach_dup.bend`: InvW read by the driver; InvW twice/thrice.
- `proof_e_bud_defs.bend` (the potential), `proof_e_bud_api.bend` (KontW, need_ge, bud_startW),
  `proof_e_bud_main.bend` (bud_chunkW / bud_eofW / bud_refW by phase).
- `proof_e_bud_start.bend`: the start bound (HO + 12 per big piece <= |vcf| + 1 + args_len).
- `proof_e_bud_step.bend` (BudW, kont_of, needs_le), `proof_e_bud_none.bend` (no batch, batch
  start), `proof_e_bud_phase.bend` (collecting, closing, answered Asks), `proof_e_bud_plan.bend`
  (the plan step, the tasks), `proof_e_bud_seq.bend` (Q's step while combining),
  `proof_e_bud_list.bend`, `proof_e_bud_ph1.bend`, `proof_e_bud_lem.bend` (lists, counts).

## The potential

For a wrapper state W.St{q, bat} with the driver's pieces cs, end-of-file flag ef, next nx and
output O (proof_e_bud_defs.bend):

    needW = BN.needS(q, held ++ cs, eQ, nx, O) + X(bat) + XK(cs)
    held  = the batch's pieces' texts (chars of each buffer's view)
    eQ    = ef with no batch, else False (Q has not seen the end of the file)
    XK    = 12 for each piece of cs of at least 256 bytes
    X     = BNone 0; BCol{ps, k}: 7k + 4; BAsk 0; BComb: 1 while seq (Q in the middle of a piece)

A pending Ask (Q's, the plan's, or the combine's Ask{[]}) is paid by needS's RD(nx).
Where each wrapper step is paid:
- BNone, a piece Q takes, Eof, Ref: phase B's per-step lemmas (needS drops by 1 + reads).
- BNone -> BCol (a batch starts): the piece's 12 pays 1 and leaves 7 + 4 in BCol.
- BCol -> BCol: the piece's 12 pays 1 and leaves 7.
- BCol closing (a short or the kmax-th piece, or Eof): 7k + 4 pays the step, the plan's Ask
  (1 + at most 2 reads per piece, 2(k + 1)); with no reads the combine runs in the same step.
- BAsk answered, BComb (seq False) answered: RD pays; the combine's step for the next piece is
  paid by Q's count of that piece (|held ++ cs| drops by 1): a dirty piece is Q's Chunk step; a
  clean piece is feed_line, the edge's advances, then a merge or Q's go; the next Ask{[]} is
  paid by the same drop (the piece left held without a Chunk) or by Q's step's drop.
- Q asks while combining (seq True): its Ask's RD pays the answer; the extra 1 pays the
  Ask{[]} after it.
- The merge: Q's state after it is (empty source, the task's line end tp, back 0, the task's
  window), and its lines still to come are a suffix of Q's before the piece: Q's text was
  pend ++ a ++ LF ++ after(c, k) ++ rest (PcOK), and TcOK gives lines(after ++ rest) =
  ls ++ lines(tp ++ rest). So WA after <= WA before; no fact about the edge's chain is needed.

Start: phase B's bound gives HO <= v + args_len with v = |vcf| + 1 from out_len <= 126 v + 122 +
2 |args|; the 12 per piece of 256 bytes adds at most 12 (v - 1) / 256, inside the slack.

## What was hard

- InvW is Type-kinded, so a proof of it is used once. E1's step and the budget both need it:
  `inv_dup` copies it structurally (every leaf is an equality, Data). It follows the shapes of
  PcOK, TcOK, TOutOK, BatchOK and PhaseOK and must be updated when they change.
- Destructuring `(+a, +b) = h` fails ("cannot infer") when the second component is marked
  reusable; take the last equality linear and copy it with `eq_dup`.
- A Q state (Norm.St) is linear: a lemma about `needS(st, ...)` can compute with st once. The
  budget names `WAS(st, L)` once as a Data value with its equation (`name_was`), then works on it.
- A step's state appears in the continuation's types many times; its notes list, needed as a
  value, is passed separately with an equation.
- BudW states its bound as "every n equal to the potential is at most V", so a larger bound needs
  no computation on the (erased) state.
- Matches must follow the parameter order; a destructured binder cannot be matched after a later
  one.
