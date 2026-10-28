# Phase B proof area "alleles": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in the proofs of the three deliverables in
`proof_b_alleles.bend`: `alleles_pass`, `alleles_norm`, `fast_same`. Each is `?TODO`, with
its statement fixed.

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_alleles.bend`: your skeleton, helpers (`up`, `lb`, `bases_of`, `REF`, `ALTS`)
   and deliverables.
3. The code, `norm_fast.bend`:
   - `NF.alleles`: REF's bytes go through `NF.bases`, then the ALT alleles through the
     `As` loop.
   - Each allele is one `alt` step: `F.find` for the next comma, `NF.bases`, first and
     last byte, `eqa` against REF, `dup` against the earlier alleles.
   - Verdict: every allele is upper-case ACGTN and non-empty; they do not all end with the
     same base; not (all start with the same base and all are 2 or longer); no two are
     equal.
4. The String side:
   - `types.bend`: `B.Allele.read`, `B.Alleles.read`, `B.Text.is_letters`,
     `B.Text.any_empty`, `B.Text.any_not_letters`, `B.Allele.show`, `B.Alleles.show`,
     `B.Alleles.distinct`, `B.Base.of_letter`.
   - `tan.bend`: `V.var_in`. With `lasts_eq` false, `right` stops at once (AStop); with not
     (`firsts_eq` and `all_long`), `left` stops at once.
   - `norm_line.bend`: `J.fast` and helpers (`fast.go`, `fast.ans`, `fast.found`,
     `fast.problem`, `fast.ref`, `fast.norm`, `same.text`, `ref_check`, `end_ok`;
     INFO is "").
   - `proof_fast.bend` and `proof_var_lists.bend` may have reusable lemmas.
5. lawful-bytes, all proven:
   - `../lawful-bytes/LAWS.bend`: `at_view`, `at_pair`, `find_view`, `find_pair`,
     `same1_view`, `same1_pair`, `first_*`, `list_eq_true`.
   - `../lawful-bytes/proof_core.bend` (`C.BT`, bounds lemmas), `notes/`, `PROVING.md`.
   - `../lawful-fields/defs.bend` (`FD.split`) and `LAWS.bend` (`split_join`, ...). Those
     laws may not be proven yet: prove what you need yourself.
6. `notes/briefs/PROVING.md`, `notes/proof_machine.md` ("Where it got hard"), `bend guide`.

## Route (suggested)

- Reach `fast.bend` only through `proof_b_fasteq.bend`: rewrite `F.find` to `BY.find`
  with `FE.find_eq`. That is a hole on purpose: leave it.
- Start with `fast_same`: it is pure String reasoning and independent of the rest.
  Evaluate `J.fast` on the given fields step by step, rewriting with the hypotheses.
- Then relate the byte loops to list facts on the view: one list-level predicate per test,
  shown to hold when the loop answers True.
- Then lift those facts to the String functions through `Norm.chars`:
  `String.split` of the chars equals `FD.split` of the bytes, mapped by chars.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only your skeleton file and new `proof_b_alleles_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_alleles.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: the only TODOs left are the 5 in `proof_b_fasteq.bend`.
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_alleles.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about six hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
