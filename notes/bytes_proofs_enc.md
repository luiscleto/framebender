# Phase B, area "enc": notes

## Status (2026-10-27)

All five deliverables in `proof_b_enc.bend` are proven: `enc_bt`, `enc_ok`, `chars_codes`,
`chars_eq`, `out_ok`. No `?TODO` is left. `bend proof_b_enc.bend --check-only` and
`--verdict` both print ALL PROOFS CHECK. A copy with one proof broken on purpose fails. The
statements are unchanged; the only changes to the skeleton are imports, a lemma section above
the deliverables, and the proof bodies.

Files:
- `proof_b_enc.bend`: the deliverables, plus lemmas about `ttree`:
  - `tree_eq`: `fromT(ttree(d, ws)) == E.tree(d, ws)`.
  - `full_ttree`: the mirror is a perfect tree of depth d.
  - `view_ttree`: its words are `pad(2^d, ws)`.
  - `view_words`: the first `length(xs)` bytes of the block built from `words(xs)` are `xs`.
  - `shape_full`: `E.shape` of a perfect tree gives `(Some d, its words)`.
  - `enc_view`, `norm_chars`, and `out_go` (out_ok with a reusable `hok`).
- `proof_b_enc_lem.bend`: facts that do not need `ttree`:
  - codes: `length_codes`, `bytes_codes`, `chars_codes1`.
  - lists: `append_assoc`, `take_app`, and `pad` (the first k words, zero-padded) with
    `pad_take`, `pad_add` and `pad_app`.
  - words: `wz` (the zero bytes padding the last word), `l4p` (bytes of `pack4`),
    `words_unpack` (`unpack(words xs) == xs ++ wz(xs)` for bytes), and `words_len`
    (at most 4k bytes make at most k words).
  - depth: `lt_pow`, `le_four`, `go_fits` (`n <= 4 * 2^depth(n)`), and `go_le`
    (`depth(n) <= B` when `n <= 4 * 2^B`, with `go_le_s`, `next_le`, `next_lt`).
  - bounds: `pow_four` (`n <= 2^e` with `e = 2 + B` gives `n <= 4 * 2^B`, B and e
    abstract) and `to_nat_fits` (`to_nat(from_nat n) == n` for `n <= 4 * 2^29`, via
    lawful-bytes' `fits_e`).

Route for `enc_ok`: `hn` gives `n <= 4 * 2^29` once (`pow_four` at B = 29, e = 31). That
gives `to_nat(from_nat n) == n` and `depth(n) <= 29`. `go_fits` gives
`n <= 4 * 2^depth(n)`, and `C.ok_mk` builds `ok`. The view is `take(unpack(pad(2^d, W)), n)`,
with `W = words(codes s)`. Since `|W| <= 2^d`, that is `take(unpack W ++ unpack Z, n)`, which
is `take(codes s ++ wz ++ unpack Z, |codes s|) = codes s`.

## Where it got hard (research data)

- **The `%e : G; t` expression form overflowed the checker's stack** on
  `is_le(to_nat(from_nat n), M)`, where M is `4 * 2^depth(n)`. The same rewrite as
  `AB.subst(Nat, x => {...}, a, b, e, t)` checks at once. `pow_four` and `to_nat_fits` were
  fine, so the cause is the `%` form here, not the 2^31 literal. When a check overflows,
  bisect the proof with `?TODO`: it takes seconds.
- **A wrong proof can also overflow** instead of printing a type mismatch (seen when the
  last component of `enc_ok` was wrong on purpose). The checker seems to normalize the terms
  to print them. So an overflow does not by itself mean a 2^32 trap.
- **Affine hypotheses in fixed statements.** `out_ok`'s `hok` and `enc_ok`'s `hn` are not
  `+`, and each was needed twice. `out_ok` hands `hok` once to `out_go`, which takes
  `+hok`. `enc_ok` turns `hn` into one reusable `hn29` (`n <= 4 * 2^29`), from which both
  the U32 bound and the depth bound follow.
- **Forward references.** `chars_codes` needs `chars_eq`, which comes after it in the fixed
  order. A copy (`norm_chars`) sits in the lemma section, and `chars_eq` calls it.
- **Lets of an Array are refused** (`+FL = AT.fromT(U32, l)`: "+FL can be used many times,
  so its type must be Data"). Write the `fromT` term out instead.
- **Rewrite direction** caused most of the failed checks, as in every earlier area.
  `Equal.sym(A, x, y, e)` takes e : `{x == y}`.
- `pad` (first k words, zero-padded; structural on k) made the tree view easy. `pad_add` and
  `pad_take` match the split in `E.tree` exactly, and `pad_app` turns it into "list then zeros"
  only once, at the end. An arithmetic formulation (`ws ++ replicate(2^d - |ws|, 0)`) would
  have needed case splits on `|ws| <= 2^(d-1)` at every node.
- `depth.go`'s `Bool.pick` reduces only on a literal Bool. The lemmas take the condition c
  with `hc : {cond == c}` and match on c (`pick_le`, `go_le_s`). The recursive call goes in
  as a lambda (`h1 => go_le(...)`), because its hypothesis holds only in the False branch.

## Update (2026-10-28): the bound in word form

Under the bound rule, enc_ok's `hn` is now `P.le31(String.length(s)) == True{}`. The bound is
checked on words (the U32 round trip, and `U32.is_le` with 2147483648). enc_ok gets the power
form `n <= Nat.pow(2n, 31n)` from it through proof_b_lit.bend's `le31_le`, and the rest of the
proof is unchanged. proof_b_enc.bend checks: its 4 TODOs are proof_b_lit.bend's open bridges.

What I learned on the way, for the record: a bare big literal (`2147483648n`) cannot be related
to anything but itself. Probed through test/bcheck.sh:
- `Nat.add(1073741824n, 1073741824n) == 2147483648n` overflows;
- `U32.to_nat(2147483648) == 2147483648n` overflows;
- `U32.from_nat(2147483648n)` crashed the checker (exit 134).
