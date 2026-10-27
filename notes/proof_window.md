# Proof notes: window area

Files: `proof_window.bend` (the walk), `proof_window_lists.bend` (generic lemmas). No code change
(`norm_line.bend` untouched).

## Status (2026-10-27)

- `window`: **proven modulo `PV.var_in_sound`**. `window.core(sound, ...)` proves the law taking
  `var_in_sound` as the hypothesis `sound: VarSound()`; everything else is closed.
- `window_enough`: **proven modulo `PV.var_in_enough`**, the same way (`window_enough.core(enough, ...)`).
- To finish, once the var agent has proven the two interface laws, uncomment in `proof_window.bend`:
  ```
  def window(fa, body, a, r, ht, hr):
    window.core(PV.var_in_sound, fa, body, a, r, ht, hr)
  def window_enough(fa, body, a, ht, he):
    window_enough.core(PV.var_in_enough, fa, body, a, ht, he)
  ```
  Checked ahead of time: with those two laws stubbed (`?TODO`) in a temporary copy of
  `proof_var.bend`, both forwarding defs type-check (`VarSound`/`VarEnough` match the restated
  laws' types exactly, `@+x` binders included).
- `bend proof_window.bend --check-only`: 26 TODOs = 15 LAWS + 9 var laws + these 2; no errors.
- Kernel: `--verdict` cannot run while laws are open, so I ran it on a scratch copy of the project
  with all `law` blocks removed (the cores need no open law): ALL PROOFS CHECK for
  `proof_window.bend` and for `proof_window_lists.bend`. A deliberately bad def is rejected there,
  so the run is real.
- If the var agent changes the statement of `var_in_sound`, `var_in_enough` or `PV.covers`, change
  `VarSound`/`VarEnough` to match; only `win.norm` and `en.ref.b` use them.

## How the proofs go

Both walk `J.judge_in` (code) and `L.judge` (spec) side by side, one helper def per level
(`win.shape → win.ans → win.known → win.found → win.problem → win.ref → win.ref.b → win.norm`;
`en.*` the same for `window_enough`). Each helper generalizes the computed scrutinees (malformed,
answer, contig lookup, END/REF/ALT reads, POS = 0, distinct, REF check, var_in result) into
parameters plus a "remember" equation `{expr == x}`, then matches `x`.

The pieces between code and spec:
- `window_bases`: a truthful answer's `of_fasta(raw)` is `L.slice(of_fasta(contig), off, len)`.
  Needs `String.eq` sound (`string_eq_sound`, down to `Word.cmp` on the 32 bits of each U32
  char code), and `of_fasta` commuting with length/take/drop.
- `ref_sound`: a REF check the window answers (`Some b`) equals the whole-contig check. Not fitting
  the contig (`Some False`) is a mismatch in the spec too because REF is non-empty
  (`slice_len_fits`, `bases_eq_len`); covered: `slice_win` (slice of a slice).
- `ref_none.*`: `None` means "fits but not covered"; `en.none` shows that contradicts `enough`
  (for both the RefMismatch and the Normalized requirement, via `le_min_l`, `min_le_id`).
- `valid_of` + `ok_ref`/`ok_alts`/`ok_nalts`: the variant reaching the normalizer is `L.valid`;
  non-empty REF and ALTs come from the line not being MALFORMED, at least one ALT from
  `String.split` never giving an empty list.
- `en.covers`: `L.enough`'s Normalized requirement gives `PV.covers` (window length = `String.length(raw)`,
  REF length = `String.length` of the REF field, min with `clen` is a no-op since REF fits).

## Where it got hard (research data)

- Spec gap only seen in proving: the code's REF check says `Some False` when REF runs past the contig
  even for an empty REF, while the spec's `Bases.eq(slice, ref)` would be True for an empty REF past
  the end. Harmless because a non-MALFORMED line has a non-empty REF, but it forced carrying
  `malformed(fs) == False` down five levels instead of generalizing it away.
- `L.valid` needs facts the window walk otherwise never looks at (non-empty alleles, at least one ALT):
  three extra lemma chains (`read_len`, `alts_ok`, `alts_len`, `split_ne`) just to call
  `var_in_sound`.
- `String.eq` soundness is not in Base; it bottoms out in `Word.cmp` over 32 bits. Doable because
  U32 is a data type over `Word(32n)`, but needed `order_lt`/`order_gt` with nested `Chr{x}`
  patterns (a `match h1 h2` on pattern-bound chars was refused: "can't be matched in this
  position"; nested patterns in the outer case work).
- Pair destructuring `(a, b) = f(...)` is a match on a computed value: refused. Split into two
  lemmas instead (`word_fin_t`/`word_fin_b`, `en.lo`/`en.hi`).
- Equation hypotheses used twice must be `+` ("consumed more than once"); I made every equation
  parameter `+` mechanically.
- A `case _:` default does not refine the scrutinee in the goal: the `B.Code` case had to list
  all ten constructors (`en.noans.code`).
- `&&`/`||` are left-associative: `L.valid` and `B.Rec.malformed` are left-nested chains, so
  `and_tt`/`or_false_r` are applied outside-in.
- Rewriting a hypothesis (rather than the goal) needs a helper whose goal is the rewritten
  hypothesis (`en.he`).
- Law-shaped hypotheses: the function type must use `@+x:` binders to accept a law restated with
  `for +x` (plain `@x:` is a type mismatch).
