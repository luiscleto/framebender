# Phase B proof area "run": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in `proof_b_run.bend`:
- define `RunInv` (its body is yours; its signature is fixed);
- prove the 13 deliverables. Each is `?TODO`, with its statement fixed.

The deliverables say that the machine's run on bytes (`norm_run.bend`, `NR.Run`) refines
run.bend's `R.RunSt`. Each operation the machine uses, on a pictured run `P.mkRun(p)` with
`RunInv(p)`:
- gives a pictured run again, with `RunInv`;
- stands (`P.specRun`) for what run.bend's operation gives, up to the last item's text
  (`P.blank_st`).

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_defs.bend`: the shared definitions (`RunP`, `mkRun`, `specRun`, `blank_st`,
   `clear`, `btext`, `res_text`). Read-only: if you need more shared definitions, put them
   in your own file.
3. `proof_b_run.bend`: your skeleton and deliverables.
4. The code, `norm_run.bend`, and run.bend, the spec it refines:
   - `Run`, `Ck`, `start`, `tick`;
   - the flush loop (`flush.*`: write ready items; UNSORTED on a key below the last);
   - `add` (an item's text into `ob`, at the end or in the middle: `mid`), `same_run`,
     `new_run`, `keyed`, `body_line`, `same_done`, `fast_done`, `head_line`, `finish`,
     `take`, `reserve`, `put_bytes`, `put_str`, `of_str`, `to_spec`;
   - `run.bend` (spec, read-only): `insert`, `take_ready`/`drop_ready`, `flush`,
     `same_run`, `new_run`, `keyed`, `body_line`, `head_line`, `finish`.
5. Earlier proofs of the same refinement, on Strings, to reuse:
   - `proof_fast_run.bend` proved the old String machine's `norm_run.bend` (linear
     insert, take/drop in one pass, flush with a blank last) equal to run.bend's. See git
     `show 4c8703b^:norm_run.bend` for that old code.
   - Its `inv` lemma (the report from a state equals the report from it blanked) is used
     with `P.blank_st` here.
   - `notes/fast.md` explains them.
6. lawful-bytes, all proven:
   - `../lawful-bytes/LAWS.bend`: `append_view`/`append_ok`, `push_*`, `grow_*`,
     `truncate_*`, `len_*`, `capacity_*`, `empty_*`, `to_list_*`;
   - `../lawful-bytes/proof_core.bend` (`C.BT`, bounds lemmas), its `notes/` and
     `PROVING.md`.
   - `F.append` (fast.bend) is reached only through `proof_b_fasteq.bend`
     (`FE.append_view`, `FE.append_ok`, `FE.append_pair`: holes on purpose, leave them).
7. `notes/briefs/PROVING.md`, `notes/proof_machine.md` ("Where it got hard"), `bend guide`.

## Hints

- The sizes the machine guarantees are hypotheses:
  - `hbig`: `ob` holds less than 2^29 bytes;
  - `hk`: a line's bytes are at most 2^28 + 1;
  - `hfit`: `ob` plus a rewritten text is at most 2^30;
  - `hh`: the header is at most 2^28.
  Your invariant must keep `ob` well formed (`D.ok` with depth at most 29) and below
  2^31 bytes, so `room`/`grow` never overflow.
- Keep U32 reasoning on U32 constants (cheap). Never compare a symbolic Nat with a big
  Nat literal; `Norm.lim()` is `Nat.pow(2n, 30n)`, so keep it abstract.
- Mirror every buffer (`C.BT`). For a loop whose buffer changes, use either:
  - an equation naming the next mirror, or
  - a Data function mirroring the whole loop, plus one lemma equating them.
  `../lawful-bytes/notes/` has examples.
- Expect `mid` (an out-of-order item's text inserted inside `ob`) and the flush loop to
  be the hardest parts. `spec.items` takes each item's text from `ob` in order: an item
  inserted after the items whose keys are at most its own takes its bytes at the sum of
  their lengths.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_run.bend` and new `proof_b_run_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_run.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: the only TODOs left are the 5 in `proof_b_fasteq.bend`.
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_run.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about seven hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
