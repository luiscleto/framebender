# Phase B area "alleles": notes

Brief: `notes/briefs/BYTES_PROOFS_ALLELES.md`. Skeleton: `proof_b_alleles.bend`.

## Status (2026-10-27): all three deliverables proven

`bend proof_b_alleles.bend --check-only` reports 5 TODOs, all of them the holes in
`proof_b_fasteq.bend` (the proofs reach `fast.bend` only through `FE.find_eq`). The
statements of `alleles_pass`, `alleles_norm` and `fast_same`, and the skeleton's
definitions, are unchanged. `--verdict` stops at the same 5 holes, so the kernel has
not checked these files yet. The one helper with no holes, `proof_b_alleles_list.bend`,
passes `--verdict`. A copy with one rewrite broken on purpose fails (both in the skeleton
and in the loop file), so the passes are not cached.

Files (about 3100 lines):
- `proof_b_alleles_list.bend`: pure lists. `FD.split` at the first separator (`split_run`,
  `spl`: the first piece of a slice ends at `D.first`; `one`: that piece splits into itself;
  `ext`: the earlier pieces grow by one across a separator), `split_app`, and
  take/drop/slice arithmetic.
- `proof_b_alleles_loop.bend`: the byte loops on the mirror `C.BT(len, t)`:
  - `bases_t` (bytes all bases, and the last one), `eqa_t` (= `D.list_eq` of the two slices),
    `fv_val`/`fv_range`/`fv_hit` (the comma search, through `FE.find_eq`);
  - `dgo`: the dup loop answers `memb` (the allele is one of the pieces of a .. e-1), given
    fuel >= the number of pieces;
  - `astep` (one ALT allele), `aloop` (the As loop, by induction on its fuel), `go_true`
    (REF all bases, s3 < e3, s4 < e4) and `alleles_spec` (the ALT pieces pass `spec`, a list
    function that follows the loop: each allele ok, plus the final flags).
- `proof_b_alleles_spec.bend`: what `spec` gives. Every ALT allele is non-empty and all bases
  (`sp_ok`); REF and the ALT alleles are distinct (`sp_dist`); the flags (`sp_flags`).
- `proof_b_alleles.bend`: the Base/String level. Per-byte facts by a five-case eliminator
  (`base_cases`); `csplit`/`jsplit` (String.split / String.join against FD.split);
  `read_up`, `show_up`, `is_letters_up`, `aread`, `anyempty`, `anynl`, `ashow`, `adist`;
  `slast`/`sfirst`/`slong` (tan.bend's tests on the bases); `vin` (var_in stops at once);
  then the three deliverables.

## Where it got hard (research data)

- Rewrite direction: `%e : M` needs `e : {new == old}`, with old in the goal. Still the
  most common error (about 40 this time), each fixed with `Equal.sym`. Same for the inline
  form `%e : M; body` used as an argument: the expected type is M with old, the body has M
  with new. With `{%e : M; body : T}` the annotation T is M with old.
- Affine hypotheses: a deliverable's non-`+` hypothesis used twice is refused (`h1` in
  `fast_same`, `hp` in `alleles_pass`). Fixes: bind it once with `+e = Equal.sym(...)`, or
  have the deliverable call a `.go` lemma whose hypotheses are all `+`.
- A Bytes cannot be let-bound with `+` (`+B = C.BT(len, t)` is refused). Terms that hold
  one are named through small defs instead (`DNX`, `ANX`, `AKG`, `SPG`, `DUPH`).
- Induction hypotheses that hold in only one case: the dup and As loops continue only
  when the next comma is before the end, and only then do the next state's hypotheses hold.
  The recursive call goes to the case-split helper as a lambda (`+hl => dgo(k, ...)`; a
  plain `hl =>` binds hl affinely), and the helper calls it only in that case. Lambdas can
  nest (`aloop` passes `+h16 => dval(...)` inside one).
- Fuel. The dup loop has fuel 16 and only checks earlier alleles, so the proof needs
  (number of earlier alleles) <= 16. That comes from `length(E) + fuel <= 17` in the As loop.
  The first allele has no dup search (`s4 < s4` is false), so `aloop` takes the dup answer
  as a function of the bound (`hDf`) and handles the first allele like the others.
- Tracking the earlier alleles: they are the pieces of s4 .. a-2, with a comma at a-1.
  Adding the current allele needs `split(us ++ [sep] ++ q) = split(us) ++ [q]` for q without
  a separator (`ext`), plus U32 arithmetic `(c + 1) - 1 = c` (`dec_inc`).
- Representing the loops by one list function (`spec`) that follows the loop's own flag
  updates kept the loop proof down to rewriting. Three gaps needed lemmas: the first byte is
  `headb` of the piece only when the piece is non-empty (`hd_at`), `U32.is_le(2, c - a)` is
  `Nat.is_le(2, length)` (`ge2`), and the REF comparison and the dup search are one `memb`
  over `REF :: earlier`.
- `match` must follow parameter order (`cs.k` had to take b before r), and `LT` is a Cmp
  constructor, so it cannot be a binder name.
- Nothing false found. Every statement held as stated.
