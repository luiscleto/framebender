# Fast-agent notes (2026-10-27)

Brief: FAST.md. Laws untouched; only implementation files and implementation proofs changed:
`norm.bend`, `norm_line.bend`, `proof_machine_sim.bend`, new `proof_fast.bend` (548 lines).
Gate: `./check.sh` ALL PROOFS CHECK (bend and `--verdict`). `test/compare.sh`: 0 / 0 / 1 (the
`<DEL>` record). stdout, stderr and exit code byte-identical to the previous binary on chr22,
scr, small, short, zz and every `test/edge/*.vcf`, under `-c e` and `-c w`.

## Result

Back-to-back, alternating, `nice -n 19`, 32 threads, otherwise idle machine (15:17):

| input | before | after |
|---|---|---|
| GIAB HG002 chr22 (50,284 records, 1 changed) | 13.29 13.00 13.18 s | 10.64 10.48 10.38 s (−20%) |
| `data/scr.vcf` (scrambled: most records rewritten) | 8.55 8.44 s | 9.59 9.39 s (+12%) |

The whole genome was not run (rule: only once chr22 is under about 2 s).

## Changes

| step | change | chr22 | proof work |
|---|---|---|---|
| f1 | `step.go(fuel, st)` / `step.ref`: the fuel (`St.fuel`) is computed before the line work, not after | 13.5 → 13.5 s alone (needed by everything below: with the fast path it is worth ~1.7 s, measured in the prototype) | none: the new helpers unfold to the same terms |
| f2 | `J.pfs`: a pending line keeps its first 8 fields, cut at tabs (`J.cut`/`J.cuts`), not `B.Rec.fields` (no copy of INFO's tail, FORMAT, samples) | 13.5 → 10.4 s with f3 | `proof_fast.bend`: `cuts == take(1+n, split)`, the cut fields agree with the split on malformed, scope, fields 0-7 and POS (9-way case split on the list, `lt8`) |
| f3 | `J.same(a, fs)`: the record is valid, in normal form and written as `Rec.rebuild` would write it, so `Norm.same_done` writes the line as it came: no second judge, no `rebuild` join, no `String.eq(t, body)` walk, no `t ++ term` | (with f2) | `same_judge` (a chain of 6 lemmas following judge's cases), `rebuild_same` (put_same, join_split, str_eq_sound), `same_done` = `body_done`; machine proof: `GoodA`/`bl` use `J.pfs`, 3 rewrites in `LS_body`, `wch`/`wfr`/`wup` for the asked window, `judge_none` in PL, and `ASs` (the ask step splits on `J.same`) |

Errors hit while proving: rewrite direction of `%` about 10 times (always `Equal.sym`), a `match`
after a `let` (1), a lambda binder needing `+` (1), `take(xs, 0)` not reducing on a variable list
(a `take0` lemma). Each check of the whole gate takes about 3 s, so iterating was cheap.

## What the runtime makes expensive (new findings)

- **Sharing is the main cost, not copying.** Matching a value that has two live references copies
  reference counts into all its fields (`span_fade`), wrapping each field in a new refcount cell
  (`rfc_wrap`, an allocation); dropping it later walks it again (`term_drop`). A read-only walk of
  a shared 700-character line therefore costs about an allocation and two atomics per character,
  more than copying it. Micro-benchmark on chr22: split into lines + concat 2.0 s; plus an
  identity rebuild of each line 2.1-2.3 s; plus a shared `String.length` walk of each line 2.4-2.9 s.
- What made things shared: `step.go(st2, advance(st2))` kept a second reference to the whole state
  while `advance` ran (St.fuel was computed after); `+l`/`+fs` everywhere; and in `run.bend`
  (`same_run`: `+buf` used by both `take_ready` and `drop_ready`; `insert` with `+x <> +t`;
  `flush` keeps `Some{x}` as `last` while copying `x`'s text).
- `Bool.pick` evaluates both branches (a prototype that chose between "unchanged" and `rebuild`
  with it ran the rebuild for every line: +3.5 s).
- Profiler: the previous agent's SIGPROF sampler and allocation counter (reused, scratch only).

## Prototype numbers for what is not done yet (no proofs; same output on chr22)

Measured on a scratch copy, all back to back:

| prototype | chr22 |
|---|---|
| base | 13.4 s |
| f2+f3 style fast path, state still shared | 9.9 s |
| + linear state handling (= f1) | 8.2 s |
| + linear buffer (`insert` passing the head's key, `take_ready`/`drop_ready` in one pass, `same_run`/`keyed` over them), spec `flush` | 5.8 s |
| + `flush` that copies each text once and keeps `last` without its text | 5.1 s |
| (linear buffer without the fast path) | 11.2 s |

The real code (10.5 s) is a bit slower than the 8.2 s prototype because `J.pfs` copies INFO (cut)
and `J.same` then scans the copy, and resolve still matches the pending line shared.

## Remaining ideas, by measured size

1. **Linear buffer** (~2.7 s on chr22, the biggest): own versions of `insert`, `take_ready` +
   `drop_ready` (one pass, returning both), `same_run`, `keyed`, called from `body_done`/
   `same_done`; each proven equal to the `run.bend` function it replaces (local induction lemmas),
   plus one rewrite in `LS_body` and in `PF.ib_body_line`'s use. Cost estimate: 1 h.
2. **`last` without its text** (~0.7 s more): the spec keeps the last written item, text included;
   copying it costs 2.5 s, so the machine must keep it without the text. That changes the machine
   invariant (`rs == clear(S)` with `clear` also blanking `last`'s text) and needs a frame lemma
   that the run's bookkeeping does not depend on `last`'s text (like `fr_body_line`).
3. **scr regression** (the +12%): for a record that is rewritten, `J.same` judges up to `var_in`
   and the slow path judges again. Fix: have `same` return the normalized variant (or the whole
   judge result) and reuse it; the proof is the existing chain with one more case.
4. INFO END check without copying INFO (a scan that stops at the tab, ~0.3-0.5 s), and the line
   split keeping each line's LF so unchanged lines need no `body ++ term` copy.
5. Driver (the lead's): `bytes_str`/`str_bytes` are ~18% of the profile at 5.5 s. Batching reads
   (one `Ask` per piece) and parallel judging were not tried: at this point the per-line work is
   not the bottleneck; the shared-state costs above are.
