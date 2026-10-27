# Proof notes: run area (`sorted`, `grouped_in`, `no_unsorted`, `twice_run`)

## Status (2026-10-27): complete

- All four laws proven in `proof_run.bend` (restated with `+`, statements unchanged).
  `bend proof_run.bend --check-only` shows only the 15 TODOs of `LAWS.bend`'s own statements.
- `PROOF.bend` still needs `def L.twice_run(fasta, vcf, o, h): PR.twice_run(fasta, vcf, o, h)`
  (lead's file). Checked on a scratch copy with that line added: `bend PROOF.bend --check-only`
  and `--verdict` both print ALL PROOFS CHECK (whole project).
- No code change (this area owns no code). `examples.bend` unchanged and still checks.
- `twice_run` uses the var laws `PV.twice` and `PV.stays_valid` (one call each, per normalized
  line, in `proof_run_line.bend`), and this area's own `sorted` / `grouped_in` lemmas.

## Files (about 7,900 lines)

- `proof_run_base.bend`: Nat order and `+ w` cancellation, String append, String.eq is equality.
- `proof_run_sort.bend`: buffer (`insert`, `take_ready`/`drop_ready`, `flush`) and spec sort lemmas.
- `proof_run_steps.bend`: judge never says UNSORTED; eliminators `BL`, `SR`, `NR`; stopped runs.
- `proof_run_sorted.bend`, `proof_run_grouped.bend`, `proof_run_nounsorted.bend`: the first three laws.
- For `twice_run`:
  - `proof_run_text.bend`: a good line's text splits back into that line; every line of
    `B.Text.lines` is good (no LF in the body; CR LF, or LF after a body not ending in CR).
  - `proof_run_dec.bend`: `Pos.read(Nat.show(n)) == Some{n}` (divmod invariant, accumulator of
    `Nat.show.go`, strong induction through fuel) and `Nat.show` writes only digits.
  - `proof_run_rec.bend`: split/join round trips, `Rec.put` field facts, last field, allele text
    round trips, INFO/END after `Info.set_end`, "ends with CR" through joins.
  - `proof_run_rejudge.bend`: a rebuilt normalized record is judged normalized again, as itself
    (`rejudge`), and its line stays good (`good_re`).
  - `proof_run_line.bend`: per line of run 1 that goes on, its item is "read back" by run 2
    (`line_qi`): text is a good line, run 2 judges it so the run goes on, same key/CHROM/text.
  - `proof_run_two.bend`: run 2: lines that all go on, items grouped and key-sorted per CHROM,
    exit 0 and output = header ++ items in input order, for any w (including 0).
  - `proof_run_head.bend`: split at the first #CHROM line (run state, items, header string,
    `body()`), the two added lines are good and not #CHROM, code 0 => #CHROM line and every
    body line goes on.
  - `proof_run_gsort.bend`: gsort keeps `qi`, keeps the CHROM sequence (so grouped), sorts keys
    within each CHROM.
  - `proof_run_twice.bend`: assembly (`twice_main`).

## How the proofs go

- Every run lemma is an induction over lines with the state written as a constructor, so
  `line_step`/`keyed` compute; only judge's answer, Bool tests and flush results are case split
  (helper takes the value and an equation). The next state goes into a motive `M: RunSt -> Type`;
  `BL`/`SR`/`NR` (and variants `BLG`, `BLK`) are eliminators with one function per case; the
  induction hypothesis is passed as a function (no forward references).
- `sorted`: ghosts `gr` (current CHROM run, input order), `gd` (earlier runs sorted), `W` (written
  part of `gr`): `isort(gr) == W ++ buf`, `out == HD ++ texts(gd) ++ texts(W)`, buffer sorted from
  the last key. An item inserted below the last key: separate lemma `doomed` (exit 1).
  gsort follows the machine (same left fold, same Bool test), so no permutation reasoning.
- `grouped_in`: machine `cur`/`ended` are grouped.go's (String.eq soundness when same CHROM).
- `no_unsorted`: invariant "last key + w <= input POS of the previous line".
- `twice_run`: out1 = header lines ++ texts(gsort(items1)) (`sorted`); every item text is a good
  line `l2` with `qi` (run 2 judges it as an item with the same key, CHROM, text, and goes on);
  gsort keeps `qi`, groupedness and sorts keys; so run 2 over `lns(gsort(items1))` exits 0 and
  writes them in order; `body()` of both outputs is that same text. Header: the added lines are
  not #CHROM lines (they start with "##"), and are good lines (args are `clean`ed: no LF/CR).

## Where it got hard (research data)

- Rewrite direction (`%e : G` needs `e : {new == old}`, `old` in the goal) was the most common
  error by far, maybe 60 failed checks over the area. Rule I ended up applying: if the lemma is
  `{goal_term == simpler}`, use `Equal.sym`; to rewrite a hypothesis instead, write
  `{(%e : G; h) : G[old]}` where `h : G[new]`.
- Affinity: function-typed hypotheses are usable once and erased ones cannot be used in proofs at
  all, so the var laws could not be passed down as hypotheses; once proven, they are called
  directly per line. Lambda parameters need `+x =>` when used twice; `+x` lets need Data types
  (a `def T(...) -> Type` alias for an equality is not known to be Data: inline the type).
- `match` after a `let` or after a rewrite is refused: lets moved into branches, rewrites into
  helper defs. Matches must follow parameter order (reordered parameters several times).
- Termination: the shrinking argument must be first (`sorted_from(xs, k)`, `lastp(t, h)`,
  `hd_cr_rev(t, ...)`).
- Text facts were the bulk of `twice_run`: decimal round trip, split/join, CR handling (a body
  ending in CR with an LF terminator would split back differently, so "the rebuilt record ends
  with CR only if the original did" had to be proven through `Rec.put`, `Info.set_end` and joins).
- `||`/`&&` parse left-assoc, `++` right-assoc; mattered for the extraction lemmas.
- Concrete strings and chars compute fine (`Base.of_letter(Base.letter(b))`, `Pos.digit` of
  each digit, `is_chrom_line` of a literal), so many facts are `{==}` after a 10-way match.
- Stuck terms: `String.order.go(F, "HROM", LT{})` needed both strings matched; `split.push` on an
  abstract split needed a lemma (`field0_push`).
- Spec observations:
  - `no_unsorted`'s hypothesis `1 <= w` is not needed (the proof never uses it).
  - `twice_run` holds for every w, including 0 (run 2's input is sorted per CHROM, so every
    insert goes last), which is why run 2 is not proven through `no_unsorted` (its `small_moves`
    hypothesis fails for w = 0 on run 2's items, whose key equals their input POS).
  - `twice_run` depends on `Nat.show`/`Pos.read` agreeing and on `clean` removing CR and LF from
    the command line: both true, both needed.
