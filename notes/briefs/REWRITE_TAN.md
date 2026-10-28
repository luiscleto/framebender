# Phase C, area "tan": brief

You prove that Tan et al.'s algorithm run on bytes (`norm_fix.bend`, `NX.norm`) is `tan.bend`'s
`var_in`. You are a sub-agent of the rewrite agent (the "lead" below), which wrote the code and the
statements.

## Read first

- `notes/rewrite.md`: the rewrite path, and the closed form the code keeps (three counters k, tr,
  d; allele i is `drop(take(R_k ++ a_i, L_i - tr), d)` at position `pos - k + d`).
- `norm_fix.bend`, section "Tan et al.'s algorithm on the bytes", and `tan.bend` (`var_in`,
  `right`, `left`, `next_act`).
- `proof_c_defs.bend`: the pictures your statements use (`NZ` is `NX.norm` with `C.AT` for its byte
  reads; `V0`, `VW`, `BF`, `RK`, `ALK`, `KOK`).
- `notes/briefs/PROVING.md` (Bend proof syntax and patterns), `bend guide` ("Laws and Proofs"),
  `notes/bytes_proofs.md` ("Where it got hard"), `../NOTES.md` (big numbers, affinity).
- Mirrors and byte reads: `../lawful-bytes/proof_core.bend` (`C.BT`, `C.AT`, `at_pair_t`,
  `at_view_t`), and how phase B used them: `proof_b_alleles_loop.bend`, `proof_b_cut_pair.bend`.
- List lemmas you may reuse: `proof_var_lists.bend`, `proof_base.bend`, `proof_window_lists.bend`,
  `../lawful-bytes/proof_*.bend`, `../lawful-words/proof_nat.bend`, `proof_u32.bend`.

## Deliverables

`proof_c_tan.bend`: `norm_pair` and `norm_var`. Their statements are fixed: replace each `?TODO`
by a proof. Suggested route:

1. `norm_pair`: unfold `NX.norm` against `Q.NZ` step by step; every `BY.at` hands its buffer back
   (`C.at_pair_t`), so each loop of `norm_fix.bend` has a buffer-free twin in `proof_c_defs.bend`
   (`EL`, `ENDS`, `NEXT`, `RIGHT`, `FIRSTS`, `LEFT`). One lemma per loop, by induction on its list
   or fuel.
2. `norm_var`, in two levels:
   - lists: an invariant for `tan.right` on the closed form (the alleles are
     `take(R_k ++ a_i, L_i - tr)` at `pos - k`; `inits` adds one to tr, `shifted` adds one to k with
     the window base at `pos - k - 2`; lengths stay at least 1), and for `tan.left` (`tails` adds
     one to d);
   - bytes to lists: each byte `NZ` reads is the list element (`C.at_view_t`, with the hypotheses'
     bounds), and `NX.code` compares bases as `Base.is_eq` of `B.Base.of_fasta` does.

If a statement is false or cannot be used, stop and report it to the lead with a counterexample
(record it under `notes/cex/`). If you need a true fact that is missing as a hypothesis, report it
with the reason; do not change the statement yourself.

## Rules

- Edit only `proof_c_tan.bend` and helper files `proof_c_tan_*.bend` you create (`ls` first: the
  name must be free), and `notes/rewrite_tan.md`. Never edit code (`norm*.bend`, `main.bend`), the
  spec, the contract, `proof_c_defs.bend`, other areas' files, or `../lawful-*`.
- Check only through the wrapper: `timeout 1800 test/bcheck.sh proof_c_tan.bend` (add `--verdict`
  for the Lean kernel at the end). It caps each check at 4 GB and runs at most two checks at once
  across every agent; it waits for a free slot.
- Never make the checker compute with a big closed `Nat` (`Nat.pow(2n, 31n)`, `2147483648n`,
  `U32.to_nat` of a big word compared by `{==}`): it builds them in unary and can fill the
  machine. Keep bounds abstract, or compare words (U32), which the checker evaluates natively.
- No benchmarks, no builds of the binary, no git commits.
- Keep `notes/rewrite_tan.md` short and current: what is proven, what is left, and bullets on where
  it got hard (research data).

## Reporting

When `proof_c_tan.bend` checks with no `?TODO` (also with `--verdict`), or you are blocked, say so
in your final answer: what is proven, the files, anything the lead must decide.
