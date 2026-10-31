# Speed notes (speed agent, 2026-10-27)

Goal (`notes/briefs/SPEEDUP.md`): make `framebender norm -c w` faster on real data, output byte-identical, every
proof re-established (`./check.sh`: ALL PROOFS CHECK twice).

## Result

GIAB HG002 chr22 (50,284 records), `nice -n 19 ./framebender norm -c w -f data/chr22.fa
data/hg002.chr22.vcf`. All stages were timed back to back at 13:40, three alternating rounds, on an
otherwise idle machine. Allocations are heap-block allocations counted by an instrumented build;
they are deterministic.

| stage | change | chr22 s (3 runs) | allocations | proof work |
|---|---|---|---|---|
| s0 | HEAD (0810b08) | 22.47 23.01 23.66 | 1,147.0 M | |
| s1 | run.bend: `take_ready`/`drop_ready` stop at the first item not ready | 21.73 21.74 22.65 | 1,119.3 M | 2 lemma statements |
| s2 | norm_line: INFO keys copied only up to '=' (`J.end_ok`, later replaced by s7) | 19.98 20.28 21.25 | 1,066.5 M | new bridge lemma, 2 rewrites in proof_window |
| s3 | norm: a line's fields split once per visit (`J.judge_fs`), not 4 times | 17.24 17.67 18.57 | 925.7 M | 3 call sites get the extra argument |
| s4 | norm: `Norm.line` reads the CR without reversing the line | 16.96 17.03 17.55 | 855.3 M | 1 lemma (+40 lines), 1 extra rewrite in A1 |
| s5 | norm: `outs_text` does not copy its last piece (`Norm.cat`) | 16.38 16.75 17.42 | 785.1 M | 2 lemmas (+25 lines), 4 lines in outs_cons |
| s6 | norm: the waiting line keeps its fields (`Pending.fs`) | 15.25 15.36 15.65 | 714.7 M | 1 new invariant conjunct, ~15 mechanical edits |
| s7 | norm_line: INFO scanned once for END, not split into entries (`J.scan`) | 13.95 14.05 14.45 | 653.3 M | proof_window_info.bend rewritten (211 lines) |

chr22: 22.5 s to 14.0 s (best of 3, −38%). `data/scr.vcf`: 11.15 / 11.14 / 11.44 s to
8.61 / 8.61 / 8.63 s (−23%). bcftools: 0.08 s.

Checks on the final code: `./check.sh` ALL PROOFS CHECK (bend and `--verdict`);
`test/compare.sh` gives 0 / 0 / 1 differing records (the `<DEL>` one); stdout, stderr and exit code
are byte-identical to the s0 binary on chr22, scr, and every `test/edge/*.vcf` under `-c e` and `-c
w`. They are also identical on two inputs I made up: one with non-ASCII bytes in INFO and the
header, and one with 60 records covering END and INFO corner cases (`END`, `END=`, `END=03`, two
ENDs, `END=1,2`, `ENDX=`, `XEND=`, empty entries, `END=3=4`, lower case, CIGAR/HOMLEN).

## Spec rewrites (same function, listed as the rules require)

- `run.bend`: `take_ready` and `drop_ready`. Reason: `take_ready.put(ok, x, take_ready(...))` and
  `drop_ready.put(...)` are strict helpers, so the recursive call ran on every line over the whole
  buffer (~140 items at `-w 100000`), and `drop_ready` rebuilt the whole buffer and threw it away.
  The rewrite (`take_ready.go(buf, head_ready(...), w, inpos)`) matches on a flag for the head
  item and only looks further while items are ready. Same result for every input (proven: the two
  lemmas about them, `take_drop` and `take_ready_ready`, hold for the new definitions, and every
  other proof uses only those lemmas).
- No other spec definition changed. Everything else is code (`norm.bend`, `norm_line.bend`), and
  code-local functions are proven equal to the spec ones they replace: `J.end_ok == B.Info.end_ok`,
  `Norm.line == B.Text.line`, `Norm.cat == String.concat`.
- (Not mine: someone else changed comments in `LAWS.bend` at 13:02, `R.has` to `has` and so on.
  The gate passed with those changes in place.)

## How it was measured

- Wall time is noisy: the CPU runs the `powersave` governor, and the lead's own benchmarks ran
  12:40 to 12:52. Single runs varied by ±1.5 s, so the table above is back to back. Changes of a
  few percent were judged by allocation counts first.
- Allocation counter: the generated C (`bend main.bend -o x.c`), with an atomic counter added to
  `heap_alloc` and a destructor that prints it.
- Profiler: perf is not installed. I linked a SIGPROF sampler (2 kHz, it records the PC and walks
  frame pointers) into a `-O3 -g -no-pie` build. Each Bend def compiles to its own host function
  `WL_FID_<def>`, so samples map to defs by symbol. Callers are only one level deep (calls between
  defs are tail jumps).

## What the runtime makes expensive (findings)

- Text is a list of Chars, and every Data constructor seals its fields with refcount cells. One
  copy of the 35 MB file is tens of millions of allocations. At s0 each byte was copied about 12
  times: bytes to String, line split, the reverse in `ends_with`, 4 field splits, 2 INFO splits,
  the join in `rebuild`, `++ term`, `Flush.pre`, `outs_text`, str_bytes.
- Strictness: a helper that takes the recursive result as an argument (`f.put(ok, x, f(t))`)
  always recurses to the end. The fix pattern, used in every change above: match on an `ok` flag
  computed for the head by a non-recursive helper, `f.go(t, head_ok(t))`, so recursion stops at the
  first failure. It is structural (termination is fine) and proofs generalize over the flag.
- Matching a shared (`+`) value bumps the refcounts of all its fields (`span_fade`), and the
  value is freed by whoever drops the last copy. About 35% of samples are `term_drop` and 17% are
  `span_fade`.
- Allocations and time don't always move together: writing ASCII output as a String
  (`File.write`, which skips str_bytes) saved 10% of allocations and no time, because the ASCII
  check costs as much. Making `Flush.pre` skip `++ ""` saved 3.5% of allocations and no time.
  Both were dropped.
- The sorting buffer: `-w 1` takes 9.9 s against 15.1 s at the default (both on s6). The profile
  diff shows the extra time spread over everything, `bytes_str` and `String.split` included. So it
  is cache pressure from holding ~140 records as Char lists (~32 bytes per character), not buffer
  operations. A lazy `insert` (−0.5 s) and computing the fuel before `advance` (−0.4 s) were
  measured and not kept (each about 3%).

## Proof cost per change (research data: "what does it cost to change proven code")

- The cheap changes kept the old terms definitionally equal. Passing a value computed once
  (`B.Rec.fields(B.Line.body(l))`) to a function that used to compute it gives the same term after
  unfolding, so the machine proof went through by conversion. s3 needed only one extra argument at
  3 `Norm.try_line` sites, first try after the expected error.
- Rewriting a spec function in place (s1) was cheap because only 2 lemmas unfolded it. Every other
  use of `take_ready`/`drop_ready` goes through those lemmas: changing 2 lines of lemma statements
  was enough (the proof bodies, which split on a flag, did not change).
- New state in the machine (s6): a new field in `Pending` means a new invariant. I added one
  conjunct `{fs == B.Rec.fields(B.Line.body(l))}` to `GoodA`, the tuple patterns grew by one, and
  `AS` rewrites `fs` away like the other conjuncts. About 15 mechanical edits, first try.
- Code-local replacements with a bridge lemma (s2, s4, s5, s7) touched the existing proofs in 1 or
  2 places each (the only lemma that unfolds the replaced call: `A1` for `feed.go`, `win.known`
  and `en.known` for `judge_in.ans`, `outs_cons` for `outs_text`). The work was the bridge lemma.
  The INFO scanner (s7) was the largest: about 200 lines. It needed a statement for each scanner
  mode (`scan(s, True) == ends.go(split s)`, `scan(s, False) == ends.go(tail(split s))`), lemmas
  for the lazy key and entry copies, and `split` never being empty. Choosing the key comparison
  through `String.eq(ikey(s), "END")`, rather than matching E, N, D character by character, avoided
  all character-level reasoning.
- Errors hit: rewrite direction of `%` (5 times, always fixed with `Equal.sym`), a forward
  reference to a helper (1), a let of a bare constructor without annotation (1), my own slicing
  mistake in an experiment (1). No proof needed a new idea once the statement was right.
- Not attempted because of the proof cost: changing the buffer's representation (a two-list
  queue, or newest first). The sort proofs (`proof_run_sort/sorted/gsort/nounsorted`, about 2,000
  lines) are written against the list `RunSt.buf`.

## Remaining ideas (each below about 10%, or a spec change)

- Buffer footprint (up to ~34% at the default window, by the `-w 1` comparison): store buffered
  items more compactly, or flush earlier. Either changes RunSt/Item or the buffer representation
  in the spec, and the sort proofs with it.
- Driver (`main.bend`, unproven): `bytes_str` (~6%) and `str_bytes` (~3%) convert between byte
  lists and Strings. `File.read`/`File.write` on Strings decode and encode UTF-8, so they are not
  byte-exact, and the ASCII fast path measured no gain.
- Output copies in the spec: `t ++ B.Line.term(l)` in `body_line`, the join in `Rec.rebuild`,
  `Flush.pre`. Each is a few percent of allocations, and `Flush.pre` measured no time gain.
- `St.fuel` keeps the old state shared while `advance` runs (−0.4 s measured by passing the fuel
  first; small machine-proof change).
- Line split plus field split are still 2 copies of every line; fusing them would change
  `B.Line`.

# fb-end: INFO/END and gVCF lines on bytes (2026-10-31)

Brief: `notes/briefs/SPEED_END.md` (fixes 1 and 2 of `notes/briefs/END.md`). Branch `speed-end`, from
main 03c3ed4. Scratch: `data/tmp/fb-end/` (generators from `data/tmp/end/`, test copies, benches).

## Fix 1: a valid END on bytes (done)

The fast path (`norm_fast.bend`) refused every record with an END entry (`noend`). It now runs
`endok`, which walks INFO entry by entry (the pieces between ';', a key up to the first '=', as
`B.Info.key`): no END entry, or exactly one, `END=` then 1 to 9 digits without a leading zero
(`num`, POS's reader), whose value v has `pos <= v`, `1 <= len(REF)` and `v - pos == len(REF) - 1`
in U32 (so no word wraps, and no bound is needed). Anything else (two ENDs, `END=.`, `END`,
`END=0..`, ten digits, a wrong value) answers Slow as before. `norm_fix.bend` (records that need
rewriting) still uses `noend`; setting END on bytes there (the second half of fix 1) is not done.

Proofs (no law or spec change; internal statements changed):
- `proof_b_cut_pair.bend`: the mirror of `endok` (`EK`, one Data state per entry, as the rewrite
  path's `nostale` mirror), `PRE` uses it.
- `proof_b_cut_inv.bend`: the Pass inversion hands out `EK == True` in place of `NE == True`.
- `proof_b_end_key.bend` (new, ~650 lines): `info_end`, a passing `EK` gives
  `B.Info.end_ok(INFO's text, POS + len(REF) - 1)`. An induction over the entries
  (`eloop`/`estep`) with the invariant "no END value left once one was seen, else the rest passes
  `end_ok.go`", reusing `proof_c_pre_key.bend`'s search lemmas (its `KE` is `EKE`). The END entry's
  value: `String.drop(entry, 4)` is the value's bytes (`drop_fld`), read by `PO.pos_core`.
- `proof_b_end_inf.bend` (new, generated): field 7 of `B.Rec.fields(body)` is INFO's bytes, from
  `proof_c_pre_inf.bend`'s chain without its no-END hypothesis (`data/tmp/fb-end/mk_inf.py`).
- `proof_b_end.bend` (new): `pass_end`, INFO as `J.pfs` keeps it passes `J.end_ok` (`pfs_end`:
  `J.pfs`'s INFO reads as the full split's for the END check; then the two files above and
  `proof_window_info.bend`'s `end_ok_eq`).
- `pass_fields` (`proof_b_cut.bend`) now gives `J.pfs`'s own field 7 where it said `""`; its chain
  in `proof_b_cut_fx.bend` lost the no-END hypothesis (`data/tmp/fb-end/mk_fx.py`). `fast_same`,
  `fast_res`, `fix_fast`, `fix_res` take INFO as `f7` with its END check as a hypothesis; the
  rewrite path gets it from `fix_info` (no END entry, `end_of_has`). `FS8`, `lid_pfs`, `fs_f`,
  `fs_shape` take the same field 7.

Timings (`data/tmp/fb-end/bench.sh`, `-c w`, under the bench lock, niced, cores 0-15, interleaved
with main's build `fb_main`, 3 rounds, best of 3; load average 3.5 to 4.7: other agents were
checking proofs):

| input | main | fix 1 |
|---|---|---|
| chr22, valid END on every record | 1.114 s | 0.056 s |
| chr22, END with 2% of them POS-1 (BAD_END) | 4.531 s | 0.201 s |
| chr22, `,<NON_REF>` added to every ALT | 0.564 s | 0.557 s |
| chr22 as short `<NON_REF>` blocks with END | 0.351 s | 0.366 s |
| HG002 chr22 (no END) | 0.053 s | 0.055 s |
| HG002 whole genome (no END) | 2.065 s | 1.966 s |

The 2% bad file is still 4x the plain one: the BAD_END lines take the String path, and every
piece holding one is redone by the main thread (fix 3, fb-tasks'). The gVCF shapes are fix 2.

Same output: `test/same.sh` (128 runs), `test/par.sh` (312), `test/threads.sh` (2128, usage
errors, thread counts), `test/out.sh`, `test/index.sh`, `test/split.sh` (80) all identical to
main's build or pass; and `data/tmp/fb-end/cmp.sh`: stdout, stderr and code against main on 66
runs (the END and gVCF files, 12,000 generated END corner cases from chr22 records in four
layouts: LF, CRLF, INFO last with LF and CRLF, each under `-c e`, `-c w`, `-w 1`, `--threads 1`;
chr22 and scr). Gate: `check.sh`'s four steps pass (through `test/bcheck.sh`).

What it took: the mirror passed first try; the induction about 10 check rounds (rewrite
direction, a `match` after a let, a Type-valued `+` let). `pass_fields`' `""` was read in 7
places downstream (two in the rewrite path's proofs, one in the budget proofs); each took a
generalized parameter.
