# Phase B proof area "adv" (the simulation's per-line lemma): brief

Your earlier area is done; this is a new, larger one. Prove `adv_ok` in `proof_b_sim.bend`.
Handling the next line (`Norm.advance`) on a good machine state (`WF`) that stands for a
report T (`report`) gives:
- a good state standing for T again;
- `Went` with less work left (`measure`);
- `Want` asking reads within 2^31 letters;
- `Idle` with no source left;
- `Ended` (stopped), or `Yield`.

## Read first, in order

1. `notes/bytes_proofs.md` (plan, rules, technique) and `notes/bytes.md` (the program's
   design).
2. `proof_b_sim.bend`: the pictures (`StP`, `MdP`, `mkSt`), `smd`, `pre`, `intext`,
   `report`, `WF`, `measure`, `AdvG`, and the deliverable. Do not change any of them.
   Your proofs go in new files `proof_b_adv*.bend`; `adv_ok`'s body must call your proof.
3. The code, `norm.bend`, all of `advance`'s paths:
   - the byte mode (`mb.rs`, `mb.src`):
     - fast path: `body.k` → `fast.pre` → `fast.run` → `against` → `fast.hit` / `fast.need`;
     - slow path: `decoded` → `slow` → `verdict` → `slow.vd` → `body.res` /
       `same_done` / `want.b`;
     - header lines: `head`;
     - a source with no complete line: `part.len`;
     - switching to the String mode: `to_str`, `to_ms`;
   - the String mode (`ms.adv`, `ms.src`, `ms.line`, `ms.body`).
4. The lemmas you build on. Other areas prove them; call them as they are, even if still
   `?TODO`:
   - `proof_b_cut.bend` (`pre_of`, `pass_*`, `line_text`): a line that passes `NF.line`;
   - `proof_b_alleles.bend` (`alleles_pass`, `alleles_norm`, `fast_same`): `J.fast` gives
     Same;
   - `proof_b_cache.bend` (`serve_ok`, `win_truths`, `req_holds`, `jtruth_ok`,
     `against_hit`, `parts_ok`): the window;
   - `proof_b_lines.bend` (`lf_ok`, `src_line`, `src_nolf`, `pend_add`, `lines_cons`,
     `line_eq`, ...): input text and lines;
   - `proof_b_run.bend` (`run_*`): the byte run against run.bend, up to `P.settle`;
   - `proof_b_frame.bend` (`settle_inv`, `step_pre`, `run_pre`, `run_halted`): spec level;
   - `proof_fast.bend` (`fast_judge`: `fr_res(J.fast(a, J.pfs(body), body)) == J.judge_in(a, body)`)
     and `proof_window.bend` (`window`: a result from a truthful answer is `L.judge`'s);
     both are proven;
   - `proof_b_enc.bend` (`chars_eq`, `chars_codes`): proven.
5. `notes/proof_machine.md` explains how the old String machine's simulation was proven
   (the same shape), and `proof_machine_sim.bend` is that proof (lemma `TL` is the old
   per-line step). Reuse its techniques: abbreviation defs for big goals, "remember"
   equations for computed scrutinees, and impossible branches through Type-valued
   matches.

## Route (suggested)

- Do the byte mode's fast path first; it is most of the real work. Then the slow path,
  header lines, `part`/`to_str`, then the String mode.
- In each path:
  - step `advance` on `mkSt(fa, p)` with the `*_pair`-style lemmas (`line_pair`,
    `run_same`, `against_hit`, ...);
  - build p2;
  - show `report(..., p2) == T`. Unfold `report` to `R.finish(L.run.go(B.Text.lines(intext), ...))`,
    split off the first line with `src_line` + `lines_cons`, then use `L.run.go`'s step,
    `step_pre`, the run deliverable's settle equation and `settle_inv`.
- If a lemma statement you need from another area is missing, write it as a `?TODO` in
  your own file with a precise statement, and list it in your notes. Do not edit other
  areas' files.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only new `proof_b_adv*.bend` files, plus `adv_ok`'s body in `proof_b_sim.bend`.
- Check with `timeout 1800 test/bcheck.sh proof_b_sim.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Other areas' TODOs will show; they are not yours.
- No git commits.
- If a statement is false, stop and report why, with a counterexample.
- Keep notes in `notes/bytes_proofs_adv.md`.

This is the biggest area. Work about six hours, then finish with a report: what is proven
(path by path), what is left and why, and the missing lemmas you stated.
