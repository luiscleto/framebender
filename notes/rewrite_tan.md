# Phase C, area "tan": notes

Brief: `notes/briefs/REWRITE_TAN.md`. The closed form: `notes/rewrite.md`.

## Status (2026-10-28)

Done. `proof_c_tan.bend` checks with no `?TODO`, also with `--verdict`
(`timeout 1800 test/bcheck.sh proof_c_tan.bend [--verdict]`). Both statements are as the lead
wrote them; only imports were added.

- `norm_pair`: `NX.norm` hands both mirrors back with `Q.NZ`'s counters.
- `norm_var`: when `Q.NZ` answers `Some{K3{k, tr, d}}`, `V.var_in` on the record (`Q.V0`) gives
  `Some{Q.VW(...)}`, and `Q.KOK` holds.

For the lead: `norm_var` does not use `hp1` or `hp2`. It uses `hb`, `hw`, `ha`, `hn`, `ho1`,
`ho2` and `hz`. The word bounds come from words already there (`p0`, an allele's `ln`, `bl`)
through `U.to_nat_lt_p`, so 2^30 is never needed.

## Files (about 3,200 lines)

| file | what |
|---|---|
| `proof_c_tan_pair.bend` | `norm_pair`: one lemma per loop (`el`, `ends.go`, `ends`, `next`, `right`, `firsts`, `left`, `norm.r`), each byte read by `C.at_pair_t` |
| `proof_c_tan_lists.bend` | list lemmas on bytes (`get`/`take`/`drop`/`last`/`head`/`tail`), `Q.BF` commuting with them, `NX.code` = index of `B.Base.of_fasta`'s base (`beq_code`), word to Nat |
| `proof_c_tan_num.bend` | index arithmetic on Nat (window index, line index, shift index, the invariant steps) |
| `proof_c_tan_el.bend` | the bridge: byte j of `R_k ++ a` (`XA`) is the byte `NX.el` reads (`C.at_view_t`), in the window and in the line |
| `proof_c_tan_alk.bend` | one allele on the closed form: `last`, `head`, length, `init` (trim: tr + 1), `tail` (left trim: d + 1), shift (`SB(k) <> init` is `R_{k+1}`), `Win.get` of the shift letter |
| `proof_c_tan_sim.bend` | all alleles: `Q.ENDS` = (`lasts_eq`/`firsts_eq`, `all_long`), `total`, `inits`, `shifted`, `tails`, `Q.KL` along the steps, `Q.BFS` = closed form at (0, 0, 0) |
| `proof_c_tan_run.bend` | `step` (`NX.act` vs `next_act`), `right_sim`, `left_sim` (induction on the fuel, step for step), `fin` (from `hz` to the counters) |

## Where it got hard (research data)

- Rewrite direction: `%e : P` takes `e : {new == old}`. About half of the failed checks (some 15
  of 30) were an `Equal.sym` the wrong way round. Writing down the old and the new term before
  each rewrite fixed it.
- A rewrite cannot be the start of a let (`+h = %e : P ...` does not parse). It works as a def
  body or as a call argument, so small facts became one-line lemmas (`lt_add0`, `kl_inc_h`) or
  were passed inline.
- A let cannot bind a type (`+T = {a == b : X}` must be Data). A pair of equalities
  `{..} & {..}` is not Data either, so it cannot be `+`. `fin` and `norm_var` call
  `left_sim`/`right_sim` twice, once for `Pair.fst` and once for `Pair.snd`.
- `match` refines hypotheses that mention the matched variable (tested first). That made the
  inversions short (`act_trim`, `act_shift_*`, `fin`'s `None` case).
- After `match xs i`, you cannot match the tail of `xs` (it counts as a later binder). Fix: match
  `xs`, then `t i` together (`last_take`).
- One discriminator for two symbolic constructors (`akd(x, x)`) does not reduce. Use one per
  target constructor (`akT`, `akS`).
- Pattern-bound tails used in more than one hypothesis need `+t`.
- `&&` is left-associative: `ALS_IN`'s cons case is `(1 <= L && s + L <= len) && rest`.
- The Nat arithmetic (`proof_c_tan_num.bend`, 440 lines) is the largest piece, mostly
  subtraction chains (`((p - 1) - k) - o` against `((p - k) - 2) - o`). `sub_sub`,
  `add_sub_r` and `le_cancel_l` did most of the work.
- What made it tractable: the buffer-free twins in `proof_c_defs.bend` made `norm_pair` purely
  mechanical, and the closed form made each tan.bend step one list identity per allele
  (init of a take, a cons on a shift, the tail of a drop). The bytes enter only through one
  bridge lemma (`el_get`).
- Each file checks in under 1 s; `--verdict` takes 1.4 s.

# Area "txt" (same agent, 2026-10-28)

Done: `proof_c_txt.bend`'s `ala_show`, `acc_join` and `qq_pos` are proven (`proof_c_txt_lem.bend`,
about 420 lines). The statements are as given. `test/bcheck.sh proof_c_txt.bend` shows no error
and only "13 TODOs found". Those are `LAWS.bend`'s 13 laws (open claims there, proven in
`PROOF.bend`). They come in through `proof_c_text.bend` → `proof_b_judge_bytes.bend` →
`LAWS.bend`, so `--verdict` stops on them too. A temporary copy with `proof_c_text.bend`'s five
definitions (`ALS`, `NA`, `ALA`, `ACC`, `QQ`) copied word for word instead of the import printed
ALL PROOFS CHECK under `--verdict`. The copy is deleted.

- `ala_show`: `TX.ALS` from byte j with j + n = L - tr, by induction on n. Each step is
  `drop_get` plus `el_get`. One byte: `Chr{NX.letter(NX.code(x))} = Base.letter(of_fasta x)`,
  through `code_idx`.
- `acc_join`: `String.join.go(xs, h, ",") = h ++ JS(xs)`, and `TX.ACC(.., acc, False) = acc ++ JS(..)`,
  using `String.append` associativity once per step.
- `qq_pos`: the sum does not wrap: p0 < 10^9 < 2^31 and d < bl ≤ 4·2^bd ≤ 2^31. `pos31`,
  `four_pow` and `sum32` are copied from `proof_b_cache_hit.bend`, whose imports also carry
  `LAWS.bend`.

Where it got hard:
- Stack overflow: `N.le_lt_trans(Q.n(..), .., Nat.pow(2n, 31n), ..)` when the other proof's type
  says `U32.to_nat(..)`. When the heads differ (`Q.n` against `U32.to_nat`), the conversion
  check normalizes the whole type, `2^31` in unary included. Fix: use `U32.to_nat` throughout
  any term that sits next to a closed power.
- A let before a `match` blocks the match. Lets go inside each branch.
- `case 1n+n1:` with n1 used in several hypotheses needs `1n+(+n1)`.
