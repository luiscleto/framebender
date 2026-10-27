# Proof notes: run area (`sorted`, `grouped_in`, `no_unsorted`, `twice_run`)

## Status

- In progress. Helper files: `proof_run_base.bend` (Nat order, String append, String.eq is
  equality), `proof_run_sort.bend` (buffer and sort lemmas), `proof_run_steps.bend` (one body line
  of `L.run`, case by case).

## Plan

- Body phase invariant (non-halted, after the #CHROM line), with ghosts `gr` (items of the current
  CHROM run, input order), `gd` (earlier runs, sorted), `W` (items of the current run already
  written): `isort(gr) == W ++ buf`, `out == HD ++ texts(gd) ++ texts(W)`, every key of `W` <=
  key(last), `buf` sorted from key(last), `cur == cur_of(gr)`.
- Inserting an item below key(last) makes the state "doomed" (an item below the last key waits in
  the buffer): a doomed run always ends with exit code 1 (separate lemma), so `sorted` only follows
  the non-doomed states.
