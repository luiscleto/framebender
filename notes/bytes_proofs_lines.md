# Phase B area "lines": notes

Brief: `notes/briefs/BYTES_PROOFS_LINES.md`. Deliverables: `proof_b_lines.bend` (statements unchanged; imports, a
lemma section for `join_ok`, and proof bodies added).

## Status (2026-10-28): done

All 14 deliverables are proven:
- `lf_ok`, `src_line`, `src_nolf`, `pend_add`, `pd_len`, `join_ok`, `eof_ok`, `pd_empty`, `piece_src`;
- `line_eq`, `lines_cons`, `lines_eof`, `lines_nolf`, `lines_nolf_app`.

`timeout 1800 test/bcheck.sh proof_b_lines.bend --check-only` prints "5 TODOs found". All 5 are
`proof_b_fasteq.bend`'s holes (`find_eq`, `append_view`, `append_ok`, `append_pair` and `find2_eq`; `lf_ok`
and `NR.put_bytes` reach them). None of the open TODOs is mine. A copy with `piece_src`'s proof replaced by a
wrong one fails, as it should.
- Statements are unchanged. Additions: imports, a lemma section for `join_ok` (it uses `pdsrc`), and proof
  bodies.
- The bounds follow the lead's word form: `P.pd_ok`'s `U32.is_le(len, 268435456)`, the code's U32 sum tests,
  and `P.le31` in `piece_src`. They reach powers of two only through `proof_b_lit.bend`'s `lit28w`.
- No statement looked false. Two have hypotheses that are never needed:
  - `join_ok`'s `hn`/`hn2` (no LF before byte k);
  - `lines_nolf_app`'s two (it is append associativity).

Files:
- `proof_b_lines_str.bend`:
  - String facts: `split` at LF, `jf` (a text with no LF joins the next piece), `lines_cons`, `lines_lf`,
    `lines_nolf`.
  - From `proof_machine_lines.bend`: `S1`, `A3`, `A4`, `L1`, `fr_nolf`, `line_eq`.
  - `lines_eof.go`, plus `NR.chars` facts (`chars_app`, `chars_norm`, `chars_codes`, `bytes_chars`,
    `length_chars`).
- `proof_b_lines_lst.bend`: `take_drop`, `has_get`, `drop_get`, `all_bytes_drop`, `rl_nolf` (the bytes before
  the first 10 hold no LF), `first_w` (`D.first` as `from + run_len(drop ..)`).
- `proof_b_lines_bt.bend`: `lf_ok.go`, `src_line.go`, `src_nolf.go`.
- `proof_b_lines_room.bend`: `NR.room` on a mirror, with `len + k <= 2^29`. The result is a mirror `BT(len, t2)`
  of some depth, with the same view and room for `len + k`.
  - Bounds: `ovf_*` (no U32 wrap).
  - `dg_le`, `dg_ge`, `dg_cap`: `NR.depth.go`'s result is at most 29, at least the old depth when the test
    failed, and big enough.
- `proof_b_lines_pd.bend`:
  - `put_ok` (`NR.put_bytes` = room, then `F.append`), `put_len`, `str_ok` (`NR.put_str "\n"`).
  - Text reads: `text_eq`, `textof_eq`, `bt_lf`.
  - Word sizes: `sum_fit`/`fit32` (`a < 2^31`, `b <= 2^31` give `a + b < 2^32`, exponent kept a variable),
    `w28`, `sum_w`, `wk1` (the code's sums do not wrap).
  - The deliverable bodies `pd_len.go`, `pd_empty.go`, `eof_ok.go`, `pend_add.go`.
- `proof_b_lines_piece.bend`: `piece_src.k` (through `EN.enc_bt` and `EN.enc_ok`).

## Where it got hard (research data)

- **Closed big numbers, three ways:**
  - A `def n(x) = U32.to_nat(x)` wrapper next to `Nat.pow(2n, 32n)` in a hypothesis overflowed. The full
    comparison unfolds both sides and never re-checks a subterm syntactically, so it expanded `Nat.pow(2n, 32n)`
    to unary. Fix: write `U32.to_nat` everywhere a power of two is near, and change `8n` to `U32.to_nat(8)` (and
    `4n`, `2n`) only through a `subst` motive with a small `{==}`.
  - With 2^28 written as `Nat.pow(2n, 28n)` inside `P.pd_ok`, `pend.add.l` and `join.l`, no unfolding of them
    could be checked with a symbolic size. Even `{f(x) == Nat.add(x, Nat.pow(2n, 28n))}` overflows. The lead
    switched them to the literal; after that the unfoldings are plain `{==}`.
  - The literal and the power can't be related cheaply: `{268435456n == U32.to_nat(268435456)}` overflows at once.
  - What worked in the end is the lead's word form. Bounds are U32 words, which the checker evaluates natively.
    `lit28w` (`to_nat(268435456) == 2^28`, through `shln(1, 28)`) turns them into powers, and every power
    meets only itself (`subst` motives) or has a variable exponent (`sum_fit`).
  - The code's sums `len + k` and `(len + k) + 1` are U32 sums, so each needs a no-wrap lemma
    (`sum_w`, `wk1`).
- **The 22 GB check (my fault).** Scratch file `proof_b_lines_tmp.bend` held
  `{Nat.is_le(268435456n, Nat.pow(2n, 29n)) == True}` by `{==}`. Both sides are closed, so the checker
  evaluated them. It built `Nat.pow(2n, 29n)` as a unary chain of 2^29 (about 537 million) successor nodes on the
  heap and stepped it down against the literal. At roughly 40 bytes a node that is about 22 GB; the machine ran
  out of memory and the user stopped it. The earlier overflows of this kind died on the stack within a second.
  This one built its chain on the heap instead, so `timeout` did not save it. Since then every check goes through
  `test/bcheck.sh` (4 GB cap), and no test evaluates a closed big number.
- **Kinds of result pairs.** `&x: A -> B` and `A & B` are affine: destructuring them into reusable `+` names
  failed ("cannot infer" on the second component). Results that are taken apart are `Sigma<&2, &2, ...>`
  (Data), as `C.BMirror` is. A computed value can't be destructured (`(a, b) = f(..)` is refused), so a helper
  takes the pair as a parameter (`piece_src.k`, `put_ok.r`).
- **Matches.**
  - `match` must follow parameter order (`match pp z`, not `match z pp`), and comes before any let or rewrite.
  - `pend.add.k`/`join.go` match `small pd`, so with `small` symbolic nothing reduces, even in the `PS` case.
    Every case split covers all four (`pp`, `z`) pairs.
- **A `Bytes` let** (`+b = C.BT(len, t)`) is refused (Type). Write the term out.
- **Rewrite direction** caused about 8 failed checks, as everywhere (`Equal.sym(A, x, y, e)` takes `e : {x == y}`).
- **Bisecting** with a script that replaces chosen defs' bodies by `?TODO` (copy to a scratch file next to the
  others, check it) found every overflow in two or three checks.

## Follow-up (2026-10-28): fasteq's holes filled

`proof_b_fasteq.bend` now has no hole. Each lemma calls lawful-bytes' proven fast law (`L.fast_*`, with
`PROOF.bend` imported for the proofs).
- `find_eq`/`find2_eq` gained `fast_find`'s hypotheses: `D.ok(b, d)`, `from <= to`, `to <= size`, byte values.
- New `find_pair`/`find2_pair` (from `fast_find_pair`) need none.
- The `Bytes` arguments are no longer erased (the laws take them as ordinary arguments).

Callers:
- `proof_b_cut_pair.bend`: `F1`/`F2` are now the fast search's index. So `ff1`/`ff2` are the pair lemmas,
  with no hypotheses, as before. The new `f1_view`/`f2_view` give the index under the hypotheses, and
  `proof_b_cut_nat.bend`'s `tj_view`/`lj_view` and `proof_b_cut_ne2.bend`'s `hjv` use them.
- `proof_b_alleles_loop.bend`: the same for `FV`, `find_step` and `fv_val`.
- `proof_b_lines_bt.bend`: `lf_ok.go` passes `hok`, `hs`, `to <= size` and `10 < 256`.
- No deliverable statement changed. Every call site already had the hypotheses.

Results:
- `--check-only` is clean on cut, alleles, lines, run_take and cache, and on every edited file. cache's only
  open TODOs are its own.
- `--verdict` passes on lines, fasteq and alleles, and on cut_pair, cut_nat and cut_ne2.
- cut's `--verdict` goes over the 4 GB cap in `proof_b_cut_fx.bend`, a file I did not touch. Every file it
  imports passes `--verdict` alone.

## Follow-up (2026-10-28): `proof_b_run_ins.bend` for the run area

The insert side of the run area: `NR.ins.start` (with `NR.mid` and `NR.at_end`) against `R.insert` on the spec items,
independent of RunInv. `--check-only` and `--verdict` pass (5 s), with no holes.
- The requested lemmas are in the file under the exact statements pb-run wrote in `notes/bytes_proofs_run.md`
  ("Wanted from pb-lines"), with every parameter `+`: accessors `ipre`, `iplen`, `irest`, and `ins_eta`,
  `ins_split`, `ins_plen`, `ins_mid`, `ins_end`.
- Inside, sizes are `nlen` (head added last, as `ins.cons` adds them); `lens_nlen` bridges to `RD.lens`.
  `keys_allle` bridges `RD.keys_le` to `allle`.
- `go_items`: `R.insert` and `ins.go` split the list at the same place, the first key above k. Its text
  facts are String take/drop lemmas (`s_take_take`, `s_drop_take`, `s_drop_drop`).
- `items_app` / `tail_x` place each item's text. `mid_core` / `end_items` are the text forms.
- `ins_plen` turns `RD.lens(xs) <= 4 * 2^29` into `< 2^32` with `C.fits_e(.., 29n, 32n, {==}, h)`, so
  `Nat.pow(2n, 32n)` only meets itself.
- Hard parts:
  - Every error inside a def whose hypotheses hold `Nat.pow(2n, 32n)` printed as a stack overflow, because the
    checker normalizes the context to print it.
  - A text replace that matched the first `case` line in the file instead of the intended def.
  - Five rewrite-direction slips.

## Follow-up (2026-10-28): drive's step_chunk

`step_chunk` in `proof_b_drive.bend` is one call, `DC.step_chunk_h`, into the new `proof_b_drive_chunk.bend`.
Both files check with no TODO of their own; every TODO the check reports is inherited from the drive and sim
files they import. A copy with one proof broken fails.
- The proof follows `Norm.step`'s Chunk case:
  - `E.enc(c)` is rewritten to its mirror (`EN.enc_bt`; `EN.enc_ok` gives ok and the view).
  - `md.reserve`: `RN.run_reserve` in the byte mode, so WF, report and guard carry over by `specRun`
    equality; the String mode is unchanged.
  - `Pd.len` (`PL.pd_len`), then feed's three cases, each ending in pb-enc's `DS.go_ok`:
    - an empty line end: the piece is the only source;
    - no LF in the piece (`PL.lf_ok`, then `PL.src_nolf` and `PL.pend_add`): the piece joins the line end;
    - an LF at j (`PL.src_line`, `PL.join_ok`, `PL.pd_empty`, `LP.bt_lf`): the joined line and the rest of the
      piece become the two sources.
  - In each case the text still to come is the same string (`txt_e`, `txt_a`, `txt_j`), so `DS.rep_lines`
    gives the same report.
- Reused from pb-enc's files: `go_ok`, `rep_lines`, `mo_*`, `ends_lf_lf`, `empty_of_len`, `x8_a`/`x9_k`/`x9_mk`.
- Hard parts:
  - the nine-test WF chains (a generator wrote the argument lists);
  - destructuring the lines deliverables' `&`-results (helpers that take the pair as a parameter, with
    `+` only on the non-final parts);
  - lets before a `match`;
  - four rewrite-direction slips.
