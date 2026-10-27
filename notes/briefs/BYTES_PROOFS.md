# framebender on packed bytes: brief for phase B (proofs)

Phase A is done and committed on the `bytes` branch:
- chr22 takes 0.14 s and the whole genome 6.9-8.9 s;
- outputs are identical to `main`'s binary and to bcftools.

Phase B proves it. When it is done, `./check.sh` on this branch must print ALL PROOFS CHECK twice
(`bend` and `--verdict`) for every law: the 13 science laws, and the two implementation laws
`machine` and `usage` as revised and accepted (`MACHINE.bend`, `bytes_enc.bend`).

## Fixed (do not edit)

- **The science layer:** `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`.
- **The contract:** `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`. Accepted in three review
  rounds.
- **`../lawful-words`, `../lawful-arrays`, `../lawful-bytes`:** proven, all laws. Use their laws
  by importing their proof files, as they import each other; their notes list the names.
  - `../lawful-bytes/fast.bend` (yours, from phase A) is not proven yet. Another agent will prove
    it equal to `bytes.bend` (law by law: same results as the reference operations). Until then,
    state what you need from it as hypotheses of your lemmas, or use the reference operations in
    the proof and a `fast = reference` lemma at one place.
- **`../lawful-fields`:** its 19 laws are being proven now (agent `prove-bytes`). They are
  reviewed and frozen; use them once its `check.sh` passes.

## Yours

- The program files (`norm*.bend`) and new proof files.
- You may change the program to make proofs easier, as long as:
  - outputs stay byte-identical;
  - the speed stays (re-time chr22 after any change to a hot path);
  - you write down why.
- The driver (`main.bend`, `io64.c`) is under three-model review now. Its findings come to you
  through the lead.
- The existing proofs of the String machine (`proof_machine*.bend`, `proof_fast*.bend`, ...) are
  yours to reuse, adapt or replace. The science-layer proofs (`proof_var*`, `proof_window*`,
  `proof_run*`) should keep working unchanged.

## Plan

`notes/bytes.md`, "What the proofs will need", lists eight areas. They are independent enough to
prove in parallel: split them across sub-agents (the lawful-bytes prover did this well), each with
its own file and a precise statement of the lemmas it owes. Then assemble the machine proof.

Suggested order:
1. Fix the interfaces: the lemma statements each area must deliver.
2. Prove the areas.
3. Assemble.

## Rules

- Use `nice -n 19` and a `timeout` for every check. Keep heavy checks to one or two at a time:
  other proof agents share the machine.
- No git commits; the lead commits.
- Keep `notes/bytes_proofs.md`: the plan, the interfaces, what is proven, and short bullets on
  where it got hard (research data, as in `NOTES.md`'s "Where proofs got hard").
- Work until everything is proven, or about eight hours. Then report:
  - what is proven;
  - what is left, and why;
  - any code change made for the proofs, with its timing.

If you find that the contract or a lawful-* law is false or unusable as stated, stop and report it.
Do not work around it.
