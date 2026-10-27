# Proof notes: run area (`sorted`, `grouped_in`, `no_unsorted`, `twice_run`)

## Status (2026-10-27)

- Proven: `sorted`, `grouped_in`, `no_unsorted` (in `proof_run.bend`, which calls the helper
  files). `bend proof_run.bend --check-only` shows only the TODOs of other areas' open laws and
  `twice_run`. `--verdict` (Lean kernel) accepts all three, checked on a scratch copy with the open
  law statements of other areas removed (the kernel refuses to run while any TODO is open).
- Open: `twice_run` (plan below; it needs the var laws).
- No code change (this area owns no code).

## Files

- `proof_run_base.bend`: Nat order (le_trans, le_flip, cancellation of `+ w`, `<` to `+1 <=`),
  String append (assoc, `++ ""`), String.eq is equality (`str_eq_sound` through Word.cmp, refl,
  symmetry).
- `proof_run_sort.bend`: the buffer (`insert`, `take_ready`/`drop_ready`, `flush`) and the spec's
  sort (`isort`, `texts`): a flush of sorted items writes them all; a flush that does not break had
  sorted items; inserting keeps "sorted from k"; `isort(xs ++ [e]) == insert(e, isort(xs))` (the
  spec's insert-before-first-not-lower and the buffer's insert-after-last-not-higher commute);
  "some key below k" (`any_below`) survives insert and non-breaking flushes; ready items and the
  bound on the last key.
- `proof_run_steps.bend`: judge never answers UNSORTED; eliminators for one body line
  (`BL`: stops with a non-UNSORTED message, or goes on as its item), `SR` (same_run: breaks or
  writes), `NR` (new_run: breaks, CHROM came back, or starts the run); a stopped run stays stopped
  (exit 1, messages kept); the items of the body lines (`nitems_cons`).
- `proof_run_sorted.bend`: `doomed` (an item below the last key in the buffer: the run ends with
  exit 1) and `sorted_body` / `sorted_head`.
- `proof_run_grouped.bend`: `grouped_run` / `grouped_first` / `grouped_head`.
- `proof_run_nounsorted.bend`: `nu_run` / `nu_first` / `nu_head`.

## How the proofs go

- Every lemma is an induction over the lines with the state written out as a constructor
  (`RunSt{n, True{}, h, cur, ended, last, buf, k, out, notes, False{}}`), so `line_step`,
  `tick`, `keyed` compute; only `judge`'s answer, the Bool tests and the flush results are case
  split (helpers that take the value and an equation, the "value + equation" pattern).
- The goal after a line is a motive on the next state (`M: RunSt -> Type`), and `BL`/`SR`/`NR`
  are eliminators taking one function per case; the induction hypothesis goes in as a function
  argument (no forward references, so helpers cannot call the main lemma).
- `sorted`: ghosts `gr` (items of the current CHROM run, input order), `gd` (earlier runs, sorted),
  `W` (written part of the current run). Invariant: `isort(gr) == W ++ buf`,
  `out == HD ++ (texts(gd) ++ texts(W))`, keys of `W` <= key(last), `buf` sorted from key(last),
  `cur == cur_of(gr)`. An item inserted below key(last) makes the run "doomed": separate lemma
  `doomed` shows exit code 1, so the `code == 0` hypothesis closes that branch.
  The gsort side follows the machine exactly: `gsort.go` is the same left fold (same Bool test
  `String.eq(chrom(first of run), chrom)` on both sides), so no reasoning about permutations.
- `grouped_in`: machine `cur = Some{gc}`, `ended = ge` are exactly grouped.go's `cur`/`ended`
  (after rewriting `c` to `gc` with String.eq soundness when the CHROM is the same).
- `no_unsorted`: invariant "last written key + w <= input POS of the previous line" (`lbound`) and
  `buf` sorted from key(last); a later line z of the run has key(last) <= key(z) because
  `inpos(prev) <= inpos(z) < key(z) + w`. Flushes never break, a CHROM never comes back (grouped),
  stops from judge are never UNSORTED (`judge_ok`).

## Where it got hard (research data)

- Rewrite direction, over and over: `%e : G` needs `e : {new == old}` with `old` in the goal;
  nearly every lemma is stated "computed == simple", so most uses need `Equal.sym`. Cost ~10
  failed checks. Rewriting a hypothesis instead of the goal: `{(%e : G; h) : T}` with `T = G[old]`.
- `match` after a `let` is refused: lets moved into each branch (twice).
- Lambda parameters are affine: `+x => ...` needed when the parameter is used twice.
- Destructuring a pair in a let counts as a match on a computed value: needs a helper def.
- Doomed states: the obvious invariant `W ++ buf == isort(run)` is false once an item lands below
  the last key (it will break later, not now). Splitting that case into its own lemma
  ("doomed => exit 1") kept the main invariant simple.
- `sorted_from(k, xs)` with `k` first failed termination (the first argument that changes must
  shrink): list argument moved first.
- Spec observation: `no_unsorted`'s hypothesis `1 <= w` is not needed (unused in the proof). With
  w = 0, small_moves forces key > inpos for every item, which the proof handles like any other w.

## Plan for `twice_run`

Needs the var laws (`twice` or `normal_unchanged` + `standard_form`, and `stays_valid`), taken as
hypothesis arguments until proven. Pieces:
1. `body(out(run(fa, X, o))) == texts(gsort(items(fa, X)))` when the run succeeds (from `sorted`,
   the lines of `head ++ texts` split back into the same lines, the two added lines and the
   original header lines are not `#CHROM` lines).
2. The lines of `out1`'s body are the items' texts; re-judging each gives the same key, CHROM and
   text: unchanged for out-of-scope / problem lines; a normalized line's rebuilt text is judged
   normalized again with the same variant (`Pos.read(Nat.show(q)) == Some{q}`,
   `Allele.read(Allele.show(s)) == Some{s}`, split/join round trips, END rewritten consistently),
   and `Norm.var` leaves it (var law), and rebuild of it gives the same text.
3. Run 2 never stops: no MALFORMED / UNKNOWN_CHROM / strict problem (same outcomes as run 1), and
   no UNSORTED: within each CHROM run keys are sorted, so every insert goes last and flushes are
   in order (for any w, including 0, so not via `no_unsorted`).
4. `texts(gsort(items2)) == texts(gsort(items1))`: items2 agree with `gsort(items1)` on key, CHROM
   and text, and `gsort` is idempotent.
