# Phase C, area "pre": brief

You prove what the rewrite path's tests on a line's bytes (`norm_fix.bend`, `NX.line`) say about the
line's text, as phase B's `proof_b_cut.bend` does for the fast path's `NF.line`. You are a
sub-agent of the rewrite agent (the "lead" below), which wrote the code and the statements.

## Read first

- `notes/rewrite.md`: the rewrite path and its refinement argument (steps 1-4 and 7 are yours).
- `norm_fix.bend`, sections "Bytes", "INFO has no entry with key ...", "The line's tests".
- `proof_c_defs.bend` (shared pictures: `fx_of`, `fld`, `SL`, `BF`, `BFS`, `STRS`, `ALS_IN`,
  `ALS_L`, `lets`, `TL`).
- Phase B's proofs of the same kind, to reuse: `proof_b_cut.bend` and its helpers
  (`proof_b_cut_pair.bend` mirrors `NF.cut`, `NF.num`, `NF.noend`; `_inv`, `_fx`, `_pos`, `_ne`,
  `_ne2`, `_str`, `_nat`), `proof_b_alleles*.bend` (allele letters against `Allele.read`), and
  notes `notes/bytes_proofs_cut.md`, `notes/bytes_proofs_alleles.md`.
- `notes/briefs/PROVING.md` (Bend proof syntax and patterns), `bend guide` ("Laws and Proofs"),
  `notes/bytes_proofs.md` ("Where it got hard"), `../NOTES.md` (big numbers, affinity).

## Deliverables

`proof_c_pre.bend`: `line_pair`, `fix_lf`, `fix_fields`, `fix_pos`, `fix_als`, `read_bf`,
`fix_info`, `fix_cr`. Their statements are fixed: replace each `?TODO` by a proof.

- `NX.line` runs `NF.cut`, `NF.num` and `NF.noend` exactly as `NF.line` does, so `fix_lf`,
  `fix_fields` and `fix_pos` should follow phase B's proofs closely (their conclusions are phase B's
  `CU.LFD`, `CU.FDD` and `pass_pos`'s).
- New: the alleles in either case (`NX.lets`, `NX.alts.go`, `NX.feq` up to case, `NX.dis.go`), and
  INFO's stale keys (`NX.nostale`: no entry whose key, the text before its first `=`, is CIGAR,
  HOMLEN, HOMSEQ or AA; END comes from `NF.noend` as in phase B).

If a statement is false or cannot be used, stop and report it to the lead with a counterexample
(record it under `notes/cex/`). If you need a true fact that is missing as a hypothesis, report it
with the reason; do not change the statement yourself.

## Rules

- Edit only `proof_c_pre.bend` and helper files `proof_c_pre_*.bend` you create (`ls` first: the
  name must be free), and `notes/rewrite_pre.md`. Never edit code (`norm*.bend`, `main.bend`), the
  spec, the contract, `proof_c_defs.bend`, other areas' files (phase B's `proof_b_*` are read-only:
  copy a lemma if you need a variant), or `../lawful-*`.
- Check only through the wrapper: `timeout 1800 test/bcheck.sh proof_c_pre.bend` (add `--verdict`
  for the Lean kernel at the end). It caps each check at 4 GB and runs at most two checks at once
  across every agent; it waits for a free slot.
- Never make the checker compute with a big closed `Nat` (`Nat.pow(2n, 31n)`, `2147483648n`,
  `U32.to_nat` of a big word compared by `{==}`): it builds them in unary and can fill the
  machine. Keep bounds abstract, or compare words (U32), which the checker evaluates natively.
  (`fix_pos`'s bound 10^9 is a word comparison; phase B's `pass_pos_small` shows how.)
- No benchmarks, no builds of the binary, no git commits.
- Keep `notes/rewrite_pre.md` short and current: what is proven, what is left, and bullets on where
  it got hard (research data).

## Reporting

When `proof_c_pre.bend` checks with no `?TODO` (also with `--verdict`), or you are blocked, say so
in your final answer: what is proven, the files, anything the lead must decide.
