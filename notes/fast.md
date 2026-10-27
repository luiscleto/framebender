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

# Pass 2 (2026-10-27, after the lead's String driver, eb87ee4)

Baseline for this pass: HEAD eb87ee4 built as is (`fb_h2`), chr22 9.2-10.1 s, scr 8.8-9.1 s.

| step | change | chr22 | scr | proof work |
|---|---|---|---|---|
| g1 | `norm_run.bend`: linear `insert` (head's key passed on), `take_ready`+`drop_ready` in one pass (`ready`), `same_run`, `keyed`, `body_line` over them | 9.3 → 7.0 s | 9.1 → 8.3 s | `proof_fast_run.bend` (equal to run.bend's by induction); machine proof: `bl` uses it, one rewrite in `LS_body`, `ibn` for inbody |
| g2 | `J.fast` replaces `J.same`: judged once, `Same` or `Other{judge_in's result}` | 7.0 s | 8.3 → 7.4 s | `fr_res(fast(a, pfs, body)) == judge_in(a, body)` (chain k_*), `ASs` splits on the result |
| g3 | the machine keeps the last written item without its text (`N.blank`); `N.flush` moves each text into the output | 7.0 → 6.1 s | 7.4 → 7.0 s | the machine's bookkeeping is `blank_st` of run.bend's; `inv`: the report from a state is the report from it blanked (induction over lines through `line_step`, `body_line`, `keyed`, `same_run`, `new_run`, `flush`, `finish`); `LS_body` now says `blank_st(line_step(S)) == pre(.., mstep)`, its two uses go through `inv` |

| g4 | INFO is not copied: `J.c7` cuts CHROM..FILTER (a fixed chain), `J.noend` scans INFO in place up to its tab; the machine keeps INFO as "" when it has no END entry (`J.info.if`) | 6.0 → 4.7 s | 7.0 → 6.6 s | `c7_split` (7 small lemmas), `ikeyT_cut` (the key read in place is the key of INFO cut at the tab), `noend_scan` (no END found ⇒ `J.scan` of INFO is Nil), `info_end`; agreement lemmas restated for the `Got` shape (`sh_mal`, `sh_jgo`, `sh_fgo`) |

All four: `./check.sh` green, stdout/stderr/exit code identical to `fb_h2` on all test inputs (`-c e`, `-c w`).

## Whole genome (g4 build, 15:58-16:08, nothing else running)

`data/hg002.all.vcf` (4,048,342 records, 2.8 GB) with `data/hg38.fa`, `-c w`, `nice -n 19`:

| tool | time |
|---|---|
| bcftools 1.24 to /dev/null | 6.7 s |
| bcftools 1.24 to a file | 7.4 s |
| framebender to a file | 595 s (exit 0; "4048342 records, 18 changed, 512 out of scope, 0 passed with a problem") |

That is 147 µs per record against 94 µs on chr22; not investigated yet.
`test/compare.sh` on it is **not valid yet**: it ran out of disk quota on /tmp (my two outputs above
plus compare.sh's own two copies), bcftools exited 255 while writing, and the "218613 differing
records" are bcftools' truncated output. To be rerun once the space is freed.

## Proof cost (pass 2)

- New: `norm_run.bend` (code, 190 lines), `proof_fast_run.bend` (about 640 lines). `proof_fast.bend`
  reworked (the `take`-based lemmas replaced by the `c7` shape, the `same` chain by the `fast`
  chain). `proof_machine_sim.bend`: `ASs` splits on `J.fast`; `LS_spec` (the old `LS_body`, with
  run.bend's `body_line`) and `LS_body` (blanked) ; `ibn`, `bpre`, `ib_bst`; two uses of `LS_body`
  go through `PFr.inv`.
- The invariant change for g3 was cheaper than expected: the machine invariant stays
  `rs == clear(S)`; only the spec state S carried by the proof now has its last item blanked, and
  `inv` (the report from a state equals the report from it blanked) bridges it. The machine's
  bookkeeping functions are proven to give exactly `blank_st` of run.bend's (rare paths, like a new
  CHROM, just call run.bend's and blank), and independence (`*_bl`) follows from that without
  re-proving anything about sorting.
- Errors hit: rewrite direction about 15 times (always `Equal.sym`; the rule is `%e : G` with
  `e : {new == old}` and G holding `_` where old is), a `match` after a rewrite statement (2), a
  forward reference (2), a match on a computed value (1), binder order in a match (1), a bare
  constructor in a let (1), one bad splice of my own (the file duplicated). The gate takes 3-4 s,
  so each fix was a few seconds.

## Where the time goes now (chr22, 4.7 s; profile of the g4 build)

| | share |
|---|---|
| line split (`String.split` of each piece) | ~15% |
| output copies (`Line.text` of each unchanged record, the step's output) | ~15% |
| INFO walked in place for END (shared: the line is also held by the queue) | ~15% |
| `Norm.line`'s CR check (a walk of each line, shared) | ~8% |
| driver I/O per step (read, `pread` per record, write from String) | ~15% |
| freeing, buffer insert, normalizer, rest | the rest |

## Not done, and why

- Batching reads per piece and judging lines in parallel: the remaining costs are per-character
  passes over Strings and per-step driver I/O, not shared state. Batching would cut the per-record
  `pread`/write steps (part of the ~15% driver share); parallel judging needs batching first. Both
  need the machine proof's one-read-at-a-time Ask invariant (`Good`, `askdec`) redone: the largest
  remaining proof change, not started.
- Fusing the CR check and the INFO END scan into the line split (one linear pass instead of
  three walks, two of them shared), and keeping each line's LF so an unchanged record needs no
  `body ++ term` copy: both change the queue's representation (`B.Line`) and the pieces-to-lines
  proofs (`proof_machine_lines.bend`). Estimated 20-30% on chr22.
