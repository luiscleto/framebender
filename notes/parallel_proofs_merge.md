# Phase E, area C (merge): notes

## Status (2026-10-28): done

All five deliverables of `proof_e_merge.bend` are proven, statements unchanged: `merge_yes`,
`merge_no`, `merge_inv`, `merge_segok`, `merge_spec`. merge_spec needed the phantom test that the
coordinator added to `merge.ok` (see "merge_spec: the counterexample" below).

- `timeout 1800 test/bcheck.sh proof_e_merge.bend --check-only` prints "15 TODOs found". All 15
  come from imports: LAWS.bend's 13 open laws and MACHINE.bend's `machine` and `usage`, through
  `proof_b_simdefs.bend` and `proof_e_defs.bend`. A file that imports only those reports the
  same 15. None of the 15 are mine: my files have no `?TODO`.
- `--verdict` on the real file stops at those 15 TODOs before the kernel runs. To get the kernel's
  answer, I copied the `.bend` files of framebender and `../lawful-*` into my scratchpad, removed
  the 15 open laws from the copies of LAWS.bend and MACHINE.bend (nothing uses them; the copy of
  proof_b_simdefs.bend checks clean), and ran
  `test/bcheck.sh <copy>/proof_e_merge.bend --verdict`. It prints **ALL PROOFS CHECK**. The
  kernel translation (`-o .bendtt`) contains the helpers.
- Every helper file passes `--check-only`, with only the imported TODOs.

Files (all new, mine):
- `proof_e_merge_lem.bend`: general lemmas: Bool (`not_t`, `or_fl`, `or_cong`, `and_mk`,
  `and_assoc`, `and3_swap`), `Nat.max` (comm, assoc, swap, `le_max_l/r`, `max_le`), Maybe.or,
  strings (`str_assoc`, `take_add`, `ctake`), `push_eq`, `cnt_eq`, `chroms_full`. Byte-item lists:
  `max_inpos` over front ++ reverse(back) (`mi_items`), `keys_ge`/`keys_le` of the buffer,
  `nil_items` (empty buffer iff `|f| + |b| == 0`), the buffer's first and last
  (`first_items`, `last_items` = `buf_first`, `buf_last`), and `cks_shift`, which keeps
  lengths, counts and keys.
- `proof_e_merge_sp.bend`: `NR.spec.items` keeps what the tests read. Keys, order, input POS,
  first, last, emptiness and `real_inpos` are the same on the picture (`sp_*`). Shifting line
  numbers commutes with the picture (`sp_shift`). The items' texts are the text they were cut
  from, up to their lengths (`texts_take`). Also blanked lasts (`bl_*`) and `last_same`.
- `proof_e_merge_ok.bend`: `ok1`..`ok12`, merge.ok's 12 tests one at a time. It is generated:
  `&&` is **left**-associative in Bend, so each test is taken out by a chain of `and_true_l`
  and then one `and_true_r`. **If merge.ok changes, regenerate it** (generator: a short Python
  script that lists the 12 tests as merge.ok writes them).
- `proof_e_merge_inv.bend`: `inv_w`. RunInv of the merged run is built from T's parts:
  parts 5 to 8 go through `cks_shift`, part 9 (the header is bytes) is S's, and part 10 is
  trivial in the body. T's `x` is False by `ok4`.
- `proof_e_merge_seg.bend`: `segok_w` builds segok.k's ten tests from merge.ok's. The only test
  that is not just a rewrite is the last: `g10` cases on `same`, then on `changed`, then on
  `eempty`. segok's max(E) is bounded by merge.ok's (`maxe_le`, `mk_le`): every key is at most
  S's tl (RunInv parts 7 and 8), and an empty buffer gives the same value. merge.ok's
  `eempty` (`sbn == 0`) is the picture's empty buffer by RunInv part 6, since S is not stopped.
- `proof_e_merge_spec.bend`: `spec_w`, field by field through `st_cong` on the settled states:
  - ended: `push_eq`;
  - last: `last_eq`, see below;
  - buffer: `shift_items` + `sp_shift`;
  - counts: `cnt_eq`;
  - out: `out_eq`. S's ob text is its first ow letters followed by its items' texts, since
    `ow + lens(items) == |ob|` (RunInv part 5) and the ob text is a `take` of its own length
    (`ctake`);
  - notes: `note_app_nil`.
- `notes/cex/proof_e_merge_cex.bend`: the counterexample, kept as a record. It is a runnable program, not a
  proof file. With the new test it prints okP False.

### last_eq (the merged run's last against shiftS's)

`last_eq` cases on T's last:
- None: both sides are None.
- A real item (line > 0): both are that item with its line moved on by S's n.
- The phantom, S's CHROM not c0: both are None.
- The phantom, S's CHROM y equal to c0: merge.if takes the last of S's buffer, or else S's last,
  and pictures it under T's CHROM. shiftS takes the same item under y. merge.ok's new test gives
  `is_cur(tc, c0)`, so T's CHROM x is c0, and `x == y` by `str_eq_sound` (proof_run_base.bend).
  The rest is `last_same`: the blanked last of S's pictured buffer is the picture of its last
  byte item (`bl_li`).

## merge_spec: the counterexample (fixed in the code)

The statement was false with merge.ok as it stood. When T's last item is the phantom (line 0)
and S's CHROM is c0 (`same`), merge.if gave the merged run S's last item (or the last of S's
buffer) as its last, pictured under T's CHROM, since `P.specRun` names every item by the run's
current CHROM. `SD.shiftS` gives the same item under S's CHROM, c0. Nothing in RunInv or
merge.ok tied T's CHROM to c0 while T's last is the phantom: `chroms_ok` lets T's current CHROM be
any CHROM that S has not ended and that is not S's current one.

Concrete values (`proof_e_merge_cex.bend`): c0 = "1", l = 10, w = 5. s: n 3, CHROM "1", last
`Ck{5, 5, 3, None, 0}`, empty buffer and ob. t: n 1, CHROM "2", nothing ended, last the phantom
`Ck{10, 10, 0, None, 0}`, empty buffer and ob. RunInv(s), RunInv(t) and the old okP were all
True. The lasts came out as `At{3, "2", "5"}` and `At{3, "1", "5"}`, and `P.settle` blanks only
the text.

A real task cannot reach this: a new CHROM run sets last to None. The coordinator took the fix in
the code: merge.ok also tests `Bool.not(last_ph(tl)) || R.is_cur(tc, c0)`, placed right after
`Bool.not(R.has(c0, se))`. The statement is unchanged.

## What was hard (research data)

- **`&&` and `||` associate to the left.** `a && b && c` is `Bool.and(Bool.and(a, b), c)`. A
  two-law probe showed it. Statements written as `Bool.and(a, Bool.and(b, c))` would not match
  merge.ok's unparenthesized chain.
- **Direction of `%e : P`.** With `e : {a == b}`, the goal must be P with b at `_`, and it becomes
  P with a there. To rewrite an `a` in the goal, pass `Equal.sym(e)`. I got this backwards once
  (kg_app).
- **A def must come before its use** (an unfilled law is "a dead claim"); `and_mk` had to move up.
- **TODOs from imports block `--verdict`.** Any file that imports LAWS.bend or MACHINE.bend
  reports their open laws as TODOs, and `--verdict` stops there. A scratch copy with those laws
  removed gets the kernel's answer.
- **What went well.** Field-level lemmas with every parameter `+` and Data (no RunP in the
  statements) let the deliverables be one call after `match s t`. Long chains of
  `Equal.trans`/`Equal.cong` with `+` lets checked on the first try once the shapes were right.
  The checker unfolds `merge.ok`, `segok.k`, `mergeP` and `specRun` (lets included) by
  conversion.
