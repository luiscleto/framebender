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

## fb-tasks (2026-10-31): pieces redone on the main thread

Brief: `notes/briefs/SPEED_TASKS.md`. Branch `speed-tasks` from main 03c3ed4 (briefs 984688a).
Commits: a36ff20 (false UNSORTED), be463c1 (tasks keep their notes). Files: `norm.bend` and
`proof_e_*` only (new: `proof_e_seg_nf.bend`); no law, spec, `norm_fast.bend` or `norm_fix.bend`
change. Scratch: `data/tmp/tasks/`.

### What changed

1. **False UNSORTED** (`norm.bend`: `task.retry`, `task.run1`, `task.ended`, `again.*`). A task
   that stops as UNSORTED against its phantom (the line before the refused item is line 0) hands
   back its piece and windows (`TAgain`) and runs once more, from the key of the refused item. The
   key is read from the run's output buffer (the item's text starts right after the bytes written:
   CHROM, tab, POS); the stop note only names the input POS, which is the phantom itself for
   these lines. Any key is correct (the merge checks it against the true run); a second stop is
   dirty. The first run is unchanged, so files that never stopped (HG002) pay nothing.
   - Proofs: the task loop's Ended case (`proof_e_task_loop.bend`: `LAgain`, `ag_run`, `ended_go`),
     the second run in `proof_e_task_one.bend` (`run1_ok`, `retry_ok`, `final_ok`), and `TcP`
     carries the phantom its run started from (`TcOK`, `TResOK`, `mkTRes`; about 6 wrapper files
     take the field). About 400 lines.
2. **Tasks with notes** (`norm.bend`: `merge.ok` lost its "T wrote no message" test; `merge.if`
   keeps T's messages in the merged run, renumbered by `notes_shift`). END.md's fix 3.
   - Spec side: `SD.shiftS` writes T's messages (renumbered) after S's (`notes_app`), `segok` no
     longer asks for none.
   - Segment lemma: `G.M` says "not stopped" where it said "no messages" (so `mono`'s case analysis
     stands); `lift` writes Y's messages after S's. The step lemmas still take a T state without
     messages: a line that warns is a real step (`kd2n`, `kd0n`, `dk1n`), shown from the no-message
     step at S's messages plus the warning, through phase B's frame lemmas (`F.fr_keyed_go`,
     `fr_pieces`, `run_pre`) and `proof_e_seg_nf.bend` (`lift_pre`: messages T already has move
     into X's list). `par` and `drain` recurse with that list, so their hypotheses hold for every
     list (`DrainIHA`) and the recursion reads the lines first (`par.r`, `drain.r`: Bend's
     decreasing-call check reads arguments left to right).
   - Merge: `proof_e_merge_ok.bend` regenerated (generator `data/tmp/tasks/gen/gen_merge_ok.py`;
     the names keep the old numbering, `ok5` is gone), `merge_spec`'s messages (`notes_eq`:
     norm.bend's `notes_shift` is the spec's, and commutes with reverse), `pre_shift` in
     `proof_e_wrap_spec.bend`. About 700 lines changed.

### Pieces left to the main thread (instrumented scratch build, `data/tmp/tasks/instr.py`)

| file | main | now |
|---|---|---|
| cohort `-m -any` | 6 (3 UNSORTED, 3 empty) | 3 (empty) |
| joined `-m -any` | 19 (6 merge refused, 13 empty) | 13 (empty) |
| HG002 chr22, `-c w`, reference with 2% of REFs changed | 9 (merge refused) | 0 |
| HG002 chr22, `-c w`, fb-end's 2% bad END | 9 | 0 |
| first 400k genome records, 2% bad END | 82 (77 merge refused) | 5 (4 empty, 1 window miss) |
| scrambled chr22 indels | 3 (1 UNSORTED, 2 window misses) | 2 |

### Timings

`flock data/tmp/bench.lock nice -n 19 timeout ... taskset -c 0-15`, interleaved with main's build
(`data/tmp/tasks/fb_main`), to /dev/null, `-c w`. The machine was busy (load 5 to 9: other agents'
checks, never their timings), so small differences are noise.

| input | main (s) | now (s) |
|---|---|---|
| cohort `-m -any` (8 rounds) | 1.05-1.20 | 0.90-1.06 |
| joined `-m -any` (3) | 0.96-1.03 | 0.85-0.92 |
| HG002 chr22, 2% REF mismatch (3) | 0.152-0.157 | 0.060-0.073 |
| HG002 chr22, 2% bad END (3) | 4.35-4.48 | 1.10-1.19 |
| first 400k genome records, 2% bad END (3) | 37.7-38.8 | 6.65-7.25 |
| HG002 whole genome, 2% REF mismatch (3) | 10.5-12.7 | 2.20-2.39 |
| HG002 whole genome (8) | 1.48-2.18 | 1.52-1.83 |

The bad-END gain is more than the redo: a piece with a note was redone by Q one line at a time,
and END lines take the String path, so the redo was the serial part. HG002 itself: no measurable
change (same work: the tasks merged before too).

### Checks

- Gate through `test/bcheck.sh`: `PROOF.bend` ALL PROOFS CHECK (`--check-only` and `--verdict`),
  `examples.bend` TODOs only, `main.bend` "rely on unsafe" as before.
- Byte-identical to main's build (stdout, stderr, exit code): `same.sh` 128, `par.sh` 312,
  `threads.sh` 2128, `out.sh` OK, `index.sh` ALL PASS, `split.sh` 80 as bcftools (run with private
  output dirs: `data/tmp/tasks/suite.sh`); the probe files above at 1, 4 and 16 threads (30 runs);
  whole genome `-c w`, 2% mismatch `-c w` and `-c e`, and `--threads 4`; the 400k bad-END file.

### What did not pay / notes

- The first try took the retry key from the UNSORTED note: it names the input POS (the
  phantom's own), so it never fired. The output buffer has the moved key.
- A fixed lower phantom (POS - D) was considered and dropped: it refuses merges when the line
  before is within D bases, which a dense file hits; the retry costs nothing when there is no stop.

# fb-refuse: refused lines under -m on bytes (speed phase, 2026-10-31)

Brief: `notes/briefs/SPEED_REFUSE.md` (driver review 10, decision 13). With `-m -any`, a line the
byte splitter could not split came back as `None`, and the machine sent it to the String path
(`slow.parts`, which runs `B.Rec.parts` on decoded text): about 0.14 s per 146 KB cohort line.

## What it does now

- `norm_split.bend`: when the writer gives up on a line (one already found not MALFORMED, with
  two or more ALTs, none equal up to case, and no CR), `refuse` reads the line again for
  `split_problem`'s INFO and sample problems, in order. INFO is decoded (it is short) and judged
  by copies of LAWS.bend's problem functions (`first`, `count_problem`, `info_problem`,
  `gt_problem`, `format_problem`, `sample_problems`). Each sample is first given to the writer
  alone, in the record for ALT 1 (`sprob`): when the writer writes it, it has no problem
  (`sample_t`: the writer writes only what `B.Fmt.split` gives; `proof_s_when.bend`'s `col_gc`:
  `B.Fmt.split` refuses a sample exactly with its first problem). Only a sample the writer gives
  up on is decoded and judged on its text. A problem: the answer is `Ref{b, c, chrom, pos}`; none
  (the writer gave up for a size): `Out{b, None}` as before.
- `norm_seq.bend`: `split.out` on `Ref`. Under `-c e` the String path (the run stops there).
  Under `-c w`, when the window is the line's contig (`Win.on`: a `WKnown` window, its name equal
  to CHROM) and the line has at most 2^28 bytes, the line is written as it came with the warning c
  (`ref.pos`, `NR.problem_line`); else the String path.
- Proofs: `proof_s_ref.bend` (refuse is `PROBF`, the first problem after the ALTs);
  `proof_s_drv.bend` (the splitter's answer `SPR` gains the refusal case, with
  `B.Rec.parts == Unsplit{c}` from `ws.p`, and CHROM and POS as the line's fields);
  `proof_b_adv_ref.bend` (the branch gives what the spec gives: the pass-through is
  `body_done` of the problem c, which the String path's `SL.body` already covers, given that
  judge's outcome does not stop the run under `-c w`: not MALFORMED, and the window says the
  contig is in the reference); `proof_b_bud_ref.bend` (the budget, with `K.body`); and their
  wiring in `proof_b_adv_split.bend` and `proof_b_bud_inj.bend` (a record buffer never gives a
  refusal: a record has one ALT). No law or spec definition changed.

## Timings

`-c w -m -any`, default threads, wall seconds, three rounds interleaved with main's build
(984688a = 03c3ed4 plus the briefs), each run under `data/tmp/bench.lock` on CPUs 0-15, 21:22 to
21:29. The machine was not idle: load average 3.4 to 4.3 from other work. Output identical
(md5) in every pair.

| input | main | this branch | bcftools |
|---|---|---|---|
| u100: c100 without `##FORMAT=<ID=GQ`, every line refused | 15.12 14.64 15.81 | 0.33 0.32 0.32 | 0.09 0.10 0.11 |
| u300: c300 the same | 45.38 51.76 53.51 | 0.73 0.74 0.73 | 0.27 0.26 0.28 |
| p100: c100 with one PL value too many in each line's last sample | 18.10 19.48 17.85 | 0.44 0.46 0.44 | |
| c100 (nothing refused) | 0.18 0.17 0.18 | 0.17 0.20 0.17 | |
| c300 | 0.30 0.33 0.32 | 0.32 0.30 0.27 | |
| cohort.vcf (218 MB) | 1.34 1.24 1.19 | 1.24 1.51 1.14 | |
| HG002 chr22 | 0.07 0.08 0.07 | 0.07 0.08 0.08 | |
| HG002 whole genome | 2.66 2.77 2.57 | 2.98 2.71 2.48 | |

Refused lines: 45x to 70x faster, now 2.7x to 3.5x bcftools (bcftools drops the undefined tag and
splits; framebender passes the line through with UNDEFINED_TAG). Lines that split, the cohort
and HG002: within the noise (the only change on their path is one match on the writer's answer).

## What paid, what did not

- The cost was `B.Rec.parts` on Strings: a build that skipped it (wrongly, as an experiment)
  took u100 from 14.0 s to 0.76 s; the rest was decoding the line and the String verdict.
- `split_problem` on Strings, tried before `B.Rec.parts` (correct, by law `split_when`), saved
  little: 12.4 s. The spec's problem functions on text cost about as much as the split.
- A first prototype found every problem on bytes exactly (counts, genotypes, kinds); it ran as
  fast as the version kept, but would have needed new exact (both-way) byte lemmas for
  genotypes and counts. Checking each sample with the writer instead reuses its proofs, and costs
  the same: the writer's per-sample check is a fresh small buffer per sample.
- Passing the line through on bytes (rather than the String path with the code already known)
  paid too: the decoded path's line decode and verdict alone cost about 5.7 ms per cohort line.

## Still slow (documented in USAGE)

- A line refused for `BAD_CR` or `ALT_DUP` (the splitter gives up before the writer runs).
- A refused line met before the window is on its contig: in a file where every line is refused,
  the first line of each contig takes the String path once (its verdict asks for the window).
- Under `-c e`, the refused line the run stops at.

## Proof-writing notes (Bend 2.0.39)

- The checker overflowed its stack while printing an error whose context held a `+` hypothesis
  of a `Type`-valued type (`hk1: RK(...)` with `RK -> Type`): the error itself was "must be
  Data". Such hypotheses must be linear.
- `match` must come before any `+x = ...` or `%` step in a body, and a computed value cannot be
  destructured in place (give it its own def); defs must come before their uses, constructors
  too.

# fb-end: INFO/END and gVCF lines on bytes (2026-10-31)

Brief: `notes/briefs/SPEED_END.md` (fixes 1 and 2 of `notes/briefs/END.md`). Branch `speed-end`, from
main 03c3ed4. Scratch: `data/tmp/fb-end/` (generators from `data/tmp/end/`, test copies, benches).

## Result

`-c w`, `data/tmp/fb-end/bench.sh`: under the bench lock, niced, cores 0-15, interleaved with main's
build (`fb_main`), 3 rounds, best of 3, default threads. Load average 3.1 to 3.3: other agents were
checking proofs.

| input | main | speed-end |
|---|---|---|
| chr22, valid END on every record | 1.064 s | 0.051 s |
| chr22, END with 2% of them POS-1 (BAD_END) | 4.340 s | 0.199 s |
| chr22, `,<NON_REF>` added to every ALT (gVCF variant lines) | 0.540 s | 0.042 s |
| chr22 as short `<NON_REF>` blocks with END (gVCF reference blocks) | 0.350 s | 0.047 s |
| HG002 chr22 (no END) | 0.047 s | 0.047 s |
| HG002 whole genome (no END), 5 rounds | 1.308 / 1.358 s (min / median) | 1.320 / 1.335 s |
| HG002 whole genome, `--threads 1`, user CPU, 4 rounds | 4.756 s (median) | 4.952 s (+4%) |

The 2% bad file is still 4x the plain one: its BAD_END lines take the String path, and every
piece holding one is redone by the main thread (fix 3, fb-tasks'). The single-thread cost on
plain files is fix 2's, not fix 1's; see "What it cost" below.

## Fix 1: a valid END on bytes (done)

The fast path (`norm_fast.bend`) refused every record with an END entry. It now runs the old quick
test first (`noend`), and when INFO has an END entry, `ends`: it walks INFO entry by entry (the
pieces between ';', a key up to the first '=', as `B.Info.key`) and passes when there is exactly
one END entry, `END=` then 1 to 9 digits without a leading zero (`num`, POS's reader), whose value v
has `pos <= v`, `1 <= len(REF)` and `v - pos == len(REF) - 1` in U32 (so no word wraps, and no bound
is needed). Anything else (two ENDs, `END=.`, `END`, `END=0..`, ten digits, a wrong value) answers
Slow as before. `norm_fix.bend` (records that need rewriting) still refuses END: setting END on bytes
there (the second half of fix 1) is not done.

Proofs (no law or spec change; internal statements changed):
- `proof_b_cut_pair.bend`: the mirror of `ends` (`EK`, one Data state per entry, as the rewrite
  path's `nostale` mirror) and of the END test (`EKQ`: `NE`, then `EK`); `PRE` uses it.
- `proof_b_cut_inv.bend`: the Pass inversion hands out `EKQ == True` in place of `NE == True`.
- `proof_b_end_key.bend` (new, ~650 lines): `info_end`, a passing `EK` gives
  `B.Info.end_ok(INFO's text, POS + len(REF) - 1)`. An induction over the entries
  (`eloop`/`estep`) with the invariant "no END value left once one was seen, else the rest passes
  `end_ok.go`", reusing `proof_c_pre_key.bend`'s search lemmas (its `KE` is `EKE`). The END entry's
  value: `String.drop(entry, 4)` is the value's bytes (`drop_fld`), read by `PO.pos_core`.
- `proof_b_end_inf.bend` (new, generated): field 7 of `B.Rec.fields(body)` is INFO's bytes, from
  `proof_c_pre_inf.bend`'s chain without its no-END hypothesis (`data/tmp/fb-end/mk_inf.py`).
- `proof_b_end.bend` (new): `pass_end`, INFO as `J.pfs` keeps it passes `J.end_ok` (`pfs_end`:
  `J.pfs`'s INFO reads as the full split's for the END check; then, case on `NE`: no END entry,
  `proof_c_pre_ifo.bend`'s `info_k` gives `J.scan == Nil`; else `info_end` and
  `proof_window_info.bend`'s `end_ok_eq`).
- `pass_fields` (`proof_b_cut.bend`) now gives `J.pfs`'s own field 7 where it said `""`; its chain
  in `proof_b_cut_fx.bend` lost the no-END hypothesis (`data/tmp/fb-end/mk_fx.py`). `fast_same`,
  `fast_res`, `fix_fast`, `fix_res` take INFO as `f7` with its END check as a hypothesis; the
  rewrite path gets it from `fix_info` (no END entry, `end_of_has`). `FS8`, `lid_pfs`, `fs_f`,
  `fs_shape` take the same field 7.

## Fix 2: out of scope on bytes (Skipped done, BAD_END not done)

`NF.line` has a new outcome, `Skip`: when the fast path's alleles test fails, REF is one or more
letters (`letters`, `Char.is_alpha` on each byte), no ALT allele (comma piece) is empty and some
ALT allele is not all letters (`oos`, one allele at a time), and the CR test passes. That is
`B.Rec.out_of_scope` and not `B.Rec.malformed` (CHROM not empty and POS are norm_seq's and `num`'s).
`norm_seq.bend`'s skip path then does the CHROM run and size tests and `NR.skip_done` (as
`fast_done`, counted out of scope). No reference is read: Skipped comes before the contig in
`judge`. This covers gVCF's `<NON_REF>` blocks and `,<NON_REF>` variant lines, and `*`, `.`,
`<DEL>`, breakends. Under `-m`, a line with a comma in ALT is split before (as on main).

Proofs:
- `proof_b_cut_pair.bend`: mirrors of `letters`, the ALT loop and the `sk.*` steps; `PRE`'s new
  branch. `proof_b_cut_inv.bend`: Skip never gives Pass (`psk_no`). `proof_b_skip_inv.bend` (new):
  the Skip inversion (`invs`, `dsts`), as the Pass one.
- `proof_b_skip_str.bend` (new): `lett_s` (REF's bytes all letters is `B.Text.is_letters`), and
  `oos_v` by induction over the ALT pieces (`kloop`, `kstep`, `kcons`): no piece empty, some piece
  not all letters.
- `proof_b_skip.bend` (new): the cut, POS and fields from the Skip inversion through
  `proof_b_cut.bend`'s `pass_*.k`, and `skip_judge`: `L.judge` gives `Res{Skipped, POS, body}`
  (`J.fast` with no answer, then `proof_fast.bend`'s `fast_judge` and `proof_window.bend`'s
  `window` with `None`, which is truthful).
- `proof_b_run.bend`/`proof_b_run_bl.bend`: `run_skip_done` (`fast_done`'s with the skipped count).
- The step proofs: `proof_b_skip_hit.bend` (new, generated from `proof_b_adv_hit.bend`'s fast hit by
  `data/tmp/fb-end/mk_skip_hit.py`: the window's facts dropped, `skip_judge`, `skip_done`) and the
  `Sk.*` chain in `proof_b_adv_fast.bend`; the budget proofs: `proof_b_budget_skip.bend` (new,
  generated by `data/tmp/fb-end/mk_skip_bud.py`) and the `Bk.*` chain in
  `proof_b_budget_fast.bend`.

BAD_END on bytes (the other half of fix 2) is not done: it would be one more `Pre` outcome with
notes and `-c e` stops on bytes, for 0.20 s against 0.05 s on the 2% bad file, most of which is the
piece redo that fix 3 removes. Given the code-shape cost below, I did not add it.

## What it cost

- Fix 1 as first written (the entry scan on every record) cost 4 to 6% of single-thread CPU on the
  whole genome without END: about two searches per INFO entry against `noend`'s one per 'E'.
  Running `noend` first removed it (0.4%, within noise).
- Fix 2 costs about 4% of single-thread CPU on files without out-of-scope records (4.952 against
  4.756 s user, median of 4, order reversed and not), and nothing measurable at the default
  threads. It is not the Skip test (530 of 4,048,342 whole-genome records fail the alleles test):
  bisecting with variants (`data/tmp/fb-end/fb_v*`), a fourth `Pre` constructor that is never made
  costs about 1%, and the skip path's code, which Bend inlines into `norm_seq.fast.pre` (68 to 81 KB
  of generated C), the rest; moving the test to the slow path alone (no `Pre` change) still cost
  about 2%. Bend gives a function its own entry point only when it has several callers, so there was
  no way to keep the new code out of the hot function short of restructuring the slow path's proof
  (`DE.dec`). Fix 1 alone (commits up to 83ca5fd, plus the `noend`-first change of 72b6c60, which
  would need a small port) has no such cost.

## Same output

`test/same.sh` (128 runs), `test/par.sh` (312), `test/threads.sh` (2128, usage errors, thread
counts), `test/out.sh`, `test/index.sh`, `test/split.sh` (80) all identical to main's build or pass
(the first two run as copies whose caches are under `data/tmp/fb-end/`); and
`data/tmp/fb-end/cmp.sh`: stdout, stderr and code against main on 78 runs (the END and gVCF files;
12,000 generated END corner cases from chr22 records in four layouts: LF, CRLF, INFO last with LF
and CRLF; 8,813 generated gVCF and out-of-scope corner cases in LF and CRLF, including empty
alleles, `*`, `.`, `<DEL>`, breakends, lower case, a digit in REF or ALT; each under `-c e`, `-c w`,
`-w 1`, `--threads 1`; chr22 and scr), and `cmpm.sh` (36 runs under `-m -any`, with and without
`--multi-overlaps .`). Gate: `check.sh`'s four steps pass (through `test/bcheck.sh`).

## What it took

About 4,000 lines of proof, of which about 1,800 generated by scripts from existing chains. The
mirrors passed first try; the hand-written inductions took 5 to 10 check rounds each (rewrite
direction of `%`, a `match` after a let, a Type-valued `+` let, a forward reference). One mistake
cost a check over the 4 GB cap: a wrong argument list next to `Nat.pow(2n, 32n)` in context, where
the error printer blows up (the known trap). `pass_fields`' `""` was read in 7 places downstream
(two in the rewrite path's proofs, one in the budget proofs); each took a generalized parameter.

# fb-rewrite: records that are rewritten (2026-10-31)

Brief: `notes/briefs/SPEED_REWRITE.md`. Branch `speed-rewrite`, from the speed branch with fb-tasks,
fb-refuse and fb-end merged (d4a14ba). Scratch: `data/tmp/rewrite/` (inputs, builds, profiles,
the bench and comparison scripts).

## Where the time went

`data/scr.vcf` (20,739 records, 685 bytes a line, 14 MB: four 3.5 MB pieces). Found with fb-tasks'
instrumented build (`data/tmp/tasks/instr.py`, a note for each piece left to the main thread), a
debug build that prints `merge.ok`'s conjuncts, and gprof (`clang -pg`, 8 runs summed; each
`spin_N` of the generated C mapped to the defs that call it, `data/tmp/rewrite/spinmap.py`).

1. **The pieces ran twice.** At the default threads scr took about as long as at `--threads 1`
   (0.095 s against 0.116 s, user time = wall time): of the three pieces after the first, two
   were left to the main thread, and their tasks' work was thrown away.
   - Window misses: scr is sparse (one record per 1.7 kb of chr22), so a piece spans 8.3-8.7 Mb.
     The plan's two reads (`ahead()` on from the first line, `ahead()` back from the last, 4 MiB
     each) cover 2 x 4.13 Mb; a record in the gap made the task dirty.
   - Refused merges (seen once the windows covered): scr's three copies of each indel, with
     different padding, normalize to the same record. The last copy in piece S (input POS
     26633021) and the first in T (26633024) both get key 26633027. T ran from the phantom
     key l = its first line's POS (26633024), and `merge.ok` asks S's buffered keys to be at most
     l: refused, though splicing was correct (T's first write was 26633027). The same happens
     whenever left trims move a record's key past the next line's POS (scr30, 30 copies: 11 of
     39 pieces).
2. **The String path**: scr takes it for no record (scr30: about 300 calls of `decoded` in 207k
   records). With an INFO/END entry, every rewritten record does (below).
3. **Single thread** (scr30, 207k records, 0.71 s): the line's cut, twice (`NF.line`, then
   `NX.line`: 13%); `BY.grow` (9.5%: the rewritten line's buffer started at `BY.empty(0n)` and
   doubled about three times a line, `NR.depth` running its 29 strict steps each time; then
   one 4 MiB output buffer per task run); the byte copies (7%); refcounting (12%); the
   normalizer's steps (6%); INFO's scans (4%).

## What changed

1. **The phantom** (`norm.bend`, `plan.first`): a task's phantom key is its first line's POS plus
   the piece's length, above any key the task can write first (an item's key is at most its
   line's POS plus its REF's length). So the first run stops, UNSORTED against the phantom, at
   its first write, and fb-tasks' retry runs the piece again from that key: the highest phantom
   the merge can take. The first run reads only the lines up to its first write (2-3 lines on
   HG002 at `-w 1000`).
2. **The first run's output buffer** (`task.start`, `task.run1`): 64 KiB (it grows if the run goes
   on); the rerun reserves `task.res` as before. With the piece's size for both runs, every task
   paid a second 4 MiB block: chr22 at `--threads 1` was 5% slower.
3. **Windows for a sparse piece** (`plan.two`): when the first and last lines are on one CHROM
   more than 2 `ahead()` letters apart and the span is at most 4 `ahead()`, the two reads are the
   span's halves, overlapping by 2 `margin()` (each at most 2 `ahead()` + `margin()` + 1 letters,
   an 8 MiB block). Pieces within 2 `ahead()` keep their 4 MiB windows, so dense files read as
   before; the halves cover everything the old pair covered.
4. **Buffers made at their size**: `NX.write`'s buffer with room for the line and 24 bytes (the
   new line is at most a byte longer: one more POS digit; the alleles only lose bases), and
   `NR.cut_tail`'s (the sorting buffer's tail, moved when a record is inserted before buffered
   ones) with room for the tail, as `take` already did.

No law, spec or contract change. Not touched: `norm_split.bend`, `norm_seq.bend`, `task.res`.

## Proofs

- `proof_e_task_buf.bend`: `two_win` (two `plan.win` reads: within 2^31 letters, of bytes
  contigs) and `two_ok` (`plan.two`, either branch), used by `reqs.if`; `plcp` and `last_b` take
  the phantom as a parameter. `proof_e_task_piece.bend`: the piece lemma's witness for the
  phantom (it was already existential). About 50 lines.
- `proof_e_task_one.bend`: `run1_ok` takes the room as a parameter (`ST.run0_ok` was generic in
  it); `retry_ok` and `retry_r` pass 65536 and `task.res`.
- `proof_c_text.bend` (the writer's start buffer `BY.empty(d0)`, with `empty_ok_td` and
  `proof_b_lines_room.bend`'s `dg_le`) and `proof_b_run_add.bend` (`mid.k1`, `mid_t`: the tail's
  buffer, as `proof_b_run_take.bend` does for `take`).
- Every change kept the statements the rest of the proofs use; each took one or two check rounds.

## Timings

`data/tmp/rewrite/bench.sh` and `bench2.sh`: each run under `data/tmp/bench.lock`, `nice -n 19`,
CPUs 0-15, output to /dev/null, `-c w`, 3 rounds, main (03c3ed4), this branch's base (d4a14ba) and
the final build interleaved; bcftools 1.24 beside them. 23:13 to 23:30; load average 2.1 to 2.7
(other agents' checks; no other timing ran). Wall seconds (min-max of 3), peak RSS.

| input | main | base | final | bcftools |
|---|---|---|---|---|
| scr (HG002 chr22 indels scrambled, seed of `data/scr.vcf`) | 0.104-0.107 | 0.094-0.099 | **0.060-0.066** | 0.047-0.053 |
| scr2 (`scramble.py`, 3 copies, seed 7) | 0.094-0.098 | 0.096-0.099 | **0.061-0.066** | 0.045-0.055 |
| scr1 (1 copy, seed 9: one task piece) | 0.052-0.055 | 0.051-0.052 | 0.051-0.052 | 0.020-0.022 |
| scr30 (30 copies, seed 11, 142 MB) | 0.690-0.698 | 0.371-0.379 | **0.195-0.197** | 0.420-0.427 |
| scr, valid END on every record | 8.28-8.56 | 6.86-6.93 | 3.57-3.63 | 0.053-0.055 |
| scr, END with 2% POS-1 | 8.30-8.52 | 6.80-6.88 | 3.47-3.59 | 0.053-0.057 |
| scr, `,<NON_REF>` on every ALT | 0.392-0.394 | 0.032-0.034 | 0.033 | 0.038-0.045 |
| scr as `<NON_REF>` blocks with END | 0.150-0.153 | 0.025-0.028 | 0.026-0.028 | (fails: exit 255) |
| scr, `--threads 1` | 0.114-0.115 | 0.115-0.117 | **0.092-0.094** | |
| scr2, `--threads 1` | 0.112-0.115 | 0.114-0.116 | **0.091-0.093** | |
| HG002 chr22 | 0.047-0.052 | 0.048 | 0.046-0.049 | 0.072-0.078 |
| HG002 chr22, `--threads 1` | 0.087-0.089 | 0.089-0.093 | 0.088-0.096 | |
| HG002 whole genome | 1.24-1.28 (332 MB) | 1.26-1.30 (332 MB) | 1.24-1.27 (340 MB) | |
| HG002 whole genome, `--threads 1` | 5.27-5.31 (45 MB) | 5.50-5.56 (45 MB) | 5.50-5.57 (65 MB) | |

The END files gain only from the parallel side (pieces no longer run twice); their records still
take the String path (not done, below). The whole genome at `--threads 1` is 4% over main on both
the base and the final build: fb-end's cost (its section), not this branch's.

**Memory: the halves windows cost 10-20 MB.** A scratch build without them (`fb_nohalf`, `plan.two`
always the old pair): whole genome 333 MB default and 45 MB at `--threads 1`, against 343 and 65
MB with them; no time difference on the genome. On scr they are what makes the pieces clean
(0.091-0.094 s without them, 0.061-0.068 with; `--threads 1` 0.109-0.111 against 0.091-0.095).
`notes/memory.md` chose windows of at most 4 MiB; the halves bring 8 MiB blocks back for sparse
pieces only. For the lead to keep or drop (one condition in `plan.reqs.if`); the phantom and the
buffer changes do not depend on it.

## Checks

- Gate (`data/tmp/rewrite/gate.sh`, each step through `test/bcheck.sh`): `examples.bend` TODOs only,
  `main.bend` "rely on unsafe" only, `PROOF.bend` ALL PROOFS CHECK with `--check-only` and
  `--verdict`.
- Same as main's build (stdout, stderr, exit code), private output dirs
  (`data/tmp/rewrite/suite.sh`): `same.sh` 128, `par.sh` 312, `threads.sh` 2128 (usage errors and
  thread counts OK), `out.sh` OK, `index.sh` ALL PASS, `split.sh` 80 as bcftools.
- `data/tmp/rewrite/cmp.sh`: 140 runs, all the same as main: scr, scr2, scr1, scr30, the END and
  gVCF shapes above (and scr2 with END first in INFO), chr22 and fb-end's four chr22 files, each
  under `-c e`, `-c w`, `--threads 1/3/16`, `-w 1/50/100000/100000000` and `-m -any`.
- Whole genome (`wg_cmp.sh`, under the lock): `-c w`, `-c e`, `--threads 1`, `--threads 4` the same
  as main.
- Pieces left to the main thread (instrumented build): scr and scr2 2 → 0, scr30 13 → 1, chr22
  0 → 0.

## Not done

- **END on the rewrite path** (brief item 2; END.md fix 1's second half). Not done: it does not
  fit with the rest in this branch. What it needs: `NX.line` takes fb-end's `ends` (one valid END
  entry, found with its value's bytes) in place of `NF.noend`; the writer copies INFO in three
  pieces (up to the value, `Nat.show` of the new end, the rest); and a new splice lemma,
  `Info.set_end(INFO, e) == take(INFO, a) ++ show(e) ++ drop(INFO, b)` for the one END entry's
  digits a .. b, by induction over the entries (as `proof_b_end_key.bend`'s `info_end`). Then the
  pre side's mirror and inversion (`proof_c_pre_pair`, `_inv`), `fix_info`, `rebuild_fix` (which
  now uses `set_end_id`), and the text lemmas (`TXT`, `tx_eq`) take the spliced INFO. Estimate
  1,000-1,500 lines. A shortcut without the splice (keep INFO when the end does not change) covers
  almost nothing: the end stays only without a shift and a right trim, and nearly every scrambled
  record has one. The cost it would remove: scr with a valid END on every record takes 3.6 s
  (main 6.9 s) against 0.063 s without END, every record on the String path.
- **The second cut**: `NF.line` cuts the line and answers Slow; `NX.line` cuts it again (about 6%
  single thread). Handing the cut over changes `NF.Pr`, which phase B's and C's inversions read.
- **The scratch buffer**: the rewritten line is written to its own buffer, then copied into the
  output (phase C's decision 3). Writing it in place changes `proof_b_run_add`/`_bl`.
- **The first piece**: Q handles the first piece itself (header and about 5,300 records on scr),
  a quarter of scr's records on the critical path.
- **Dense scrambles**: scr30 still leaves one piece of 39 to the main thread: a true crossing (a
  record in T sorts before one buffered in S).

# fb-memory: -m memory (speed phase, 2026-10-31)

Brief: `notes/briefs/SPEED_MEMORY.md` (driver review 10, decision 14). Commits 19804ee, ff49b8b.
Files: `norm_run.bend`, `norm_split.bend`, `proof_b_run_num.bend`, `proof_b_run_buf.bend`,
`proof_b_lines_room.bend`, `proof_s_w.bend`, `docs/USAGE.md`. No law or spec change. Scratch:
`data/tmp/memory/` (generators `gen.py`, `gen2.py`; instrumented build `ibuild.sh` + `instr.py`;
`bench.sh`, `suite.sh`, `ident.sh`).

## Where the memory goes

Measured with a build that counts fresh heap per block class, the live peak of big blocks, and
each big block's call site (`instr.py`). A packed buffer costs about one byte per byte; a block
class is a power of two, and the runtime keeps freed blocks per class (notes/memory.md), so the
heap is the sum of each class's peak.

- **`NR.room` asked for twice the bytes needed, then rounded up to a power of two**: blocks 2 to
  4 times what they hold. This was most of the "12 bytes per byte of records".
- **The splitter's buffer** holds all of a line's records (h200: 80 MB in a 256 MB block).
- **The run's output buffer** holds this step's output plus the texts waiting in the `-w`
  window. Split records of one line all wait (none is ready until a line `w` bases on), so h200's
  80 MB of records sit there whole; w30 (consecutive positions, 30 records each) keeps about
  240 MB of records in the window. The spec requires this (bcftools keeps the same records,
  in binary).
- **The step-end copy** (`NR.take`) copies the waiting texts into a new buffer while the old one
  goes to the driver: the window twice at a step boundary.
- **Tasks** (every thread count; `--threads 1` is batches of one piece) hold their piece's whole
  output until the merge (105 MB per 3.5 MB piece on w30), and a growing buffer leaves a block
  parked in every size it passed through, one per concurrent task. On w30 at the default
  threads: live peak 1.3 GB against 2.5 GB committed.

## What changed

`NR.room` (and the splitter's copy) asks for `NR.want(n)`: 2n below 64 MiB, n from there. Exactly n
everywhere halved the large blocks but made small buffers grow through every size, which on w5
(16-32 MB task buffers at 16 tasks) cost 900 to 1150 MB; skipping a size below 64 MiB keeps w5
as it was. Proofs: `NM.want_ge` (n <= want(n) when n * 2 fits), used in `room_c` and
`room_ok.k`; `room_if` in `proof_s_w.bend` follows.

## Timings

`data/tmp/memory/bench.sh`: fb_base (5636de8, the branch's base) and fb_new interleaved with
bcftools 1.24, three rounds, 00:27 to 00:53, each run under `data/tmp/bench.lock`, `nice -n 19`,
`taskset -c 0-15`, `-c w`, to a file. Load 2 to 7 (other agents' checks). Wall s / peak RSS MB.
Output md5 identical between the two builds in every pair.

| input | threads | base | new | bcftools |
|---|---|---|---|---|
| h200: 1 line, 100k samples GT, 200 ALTs | 1 | 2.38-2.48 / 958 | 2.25-2.40 / 574 | 0.40 / 120 |
| | default | 2.37-2.53 / 958 | 2.26-2.39 / 574 | |
| | 16 | 2.38-2.51 / 960 | 2.37-2.41 / 574 | |
| w30: 3000 lines in a row, 2000 samples, 30 ALTs | 1 | 59.0-61.8 / 1569 | 59.4-61.3 / 1187 | 19.2-20.1 / 157 |
| | default | 50.2-51.9 / 2393 | 49.7-52.7 / 2007 | |
| | 16 | 49.7-51.7 / 2390 | 50.9-51.6 / 2010 | |
| w5: 12,000 lines, 2000 samples, 5 ALTs | 1 | 23.3-23.4 / 219 | 21.5-22.6 / 219 | 4.1-4.4 / 46 |
| | default | 14.1-14.9 / 900 | 13.7-14.3 / 899 | |
| | 16 | 13.6-14.7 / 895 | 14.0-14.2 / 899 | |
| cohort `-m -any` | default | 1.08-1.64 / 325 | 1.10-1.66 / 324 | |
| joined `-m -any` | default | 1.03-1.68 / 319 | 1.06-1.12 / 321 | |
| HG002 whole genome `-m -any` | default | 3.15-3.91 / 389 | 2.94-3.14 / 390 | |
| HG002 whole genome | default | 2.19-2.58 / 333 | 2.36-2.48 / 334 | |

(The reviewer's bcftools figure for one 410 KB line, 2.2 s and 553 MB, is not what bcftools 1.24
gives on `gen.py wide h200 1 200 100000` here: 0.40 s, 120 MB.)

## What did not pay (measured on scratch builds, not kept)

- **An earlier yield** (the sequential pump ends the step once this step wrote 4 MiB and at least
  as much as waits): no change (sparse 30-ALT file, 281 against 282 MB). Every piece runs as a
  task, at every thread count, and a task holds its output until the merge; the pump only runs
  the seams and redone pieces. A yield inside a task makes it dirty (`task.adv`).
- **Smaller pieces** (driver, `piece()` 1 MiB / 512 KiB): w30 at the default 2242 to 2232 / 1287
  MB, but cohort 1.15 to 4.20 / 5.19 s and HG002 1.97 to 2.50 / 2.68 s.
- **Streaming a line's records** (the brief's lead): needs a new `Src` form holding the line and
  the next ALT, in every function over sources and in about 45 proof files that match `SP`. It
  would save the splitter's buffer only: 128 MB on h200 now, nothing on w30 or w5 (a line's
  records there are 40-240 KB). The records still wait in the window afterwards.
- **`NR.mid` from the back** (insert where the newest keys stop, after a read-only check that no
  older key is above the item's): w30k 13.5 to 13.2 s, w5k 5.4 to 4.6 s, h200 the same. On w30
  the check fails 80% of the time (a record moved left belongs before older items of the front
  list), so the old path still runs. Proof cost about that of `mid` today (`proof_b_run_ins`,
  `proof_b_run_add`: ~800 lines); not attempted.

## What is still slow, and why

- **w30 (2.5-3x bcftools)**: `NR.mid`, an item whose key is below the buffer's largest, rebuilds
  the whole buffer list (`append_ck`, `rev_ck`, `ins.start`) and moves ob's tail; split records
  of a line arrive out of key order (each ALT moves left by its own amount), so with 30,000 items
  waiting each such record costs O(buffer). About 45% of the profile. A cheaper insert needs the
  buffer's sortedness, which is not in `RunInv` (54 proof files use it).
- **w5 (3.5x bcftools)**: the splitter's per-sample writing (the `spin_*` writer functions, about
  60%), already the subject of `notes/split.md`'s "Splitter speed".
- **One line with many huge records** (1300 ALTs x 100k samples): `mid` moves the tail bytes of
  every record whose key is below the last: quadratic in the line's records (520 MB of records:
  hundreds of GB moved). Still does not finish; the fix is a buffer that does not keep texts in
  key order, a representation change.

## Checks

- Gate through `test/bcheck.sh` on ff49b8b: `PROOF.bend` ALL PROOFS CHECK (`--check-only` and
  `--verdict`), `examples.bend` 38 TODOs only, `main.bend` "rely on unsafe" as before.
- Against main's build (984688a), stdout, stderr and exit code (`data/tmp/memory/suite.sh`):
  `same.sh` 128, `par.sh` 312, `threads.sh` 2128 identical, `out.sh` OK, `index.sh` ALL PASS,
  `split.sh` 80 as bcftools; `ident.sh`: h200, w30, w5, w30k, w5k and the sparse file, `-c w` and
  `-c e`, `--threads` 1, default, 16: 36 of 36 identical.

# fb-fix11: driver review 11's fixes (2026-11-01)

Brief: `notes/briefs/FIX11.md` (reports `reviews/claude-driver11.md`, `reviews/gpt-driver11.md`).
Branch `speed-fix11` from b9c598a. Commits 0c01467 (the phantom), deb5571 (`NR.want`), and the docs.
No law, spec or contract change. Scratch: `data/tmp/fix11/` (builds `fb_*` from `mk.sh`/`var.sh`,
variant patches `p_*.py`, `bench.sh`, `cmp.sh`, `suite.sh`, `gate.sh`, `gen_ph.py`).

## 1. Plain and -m cohort files (the phantom)

**Where the time went.** fb-rewrite's phantom (first line's POS plus the piece's length) stops every
task's first run at its first write; on a dense file that write comes only once a line `-w` bases
on is read, so the task read those lines twice: about 6 of the cohort's 26 lines a piece (132 KB
lines, one every 170 bases), 0.6 ms a piece on the 1000 Genomes sub. Builds tried (one round each,
then three on the cohort):

| build | sub `--threads 1` | cohort `-m` `--threads 1` | scr | scr30 |
|---|---|---|---|---|
| main | 0.49-0.51 | 3.47-3.88 | 0.109-0.112 | 0.70-0.71 |
| speed (b9c598a) | 0.61-0.62 | 4.82-4.83 | 0.070-0.073 | 0.188-0.195 |
| old phantom (POS), task.res for both runs | 0.48-0.50 | 3.49-3.70 | 0.103-0.104 | 0.34-0.36 |
| **guessed phantom**, task.res for both runs | 0.48 | 3.47-3.71 | 0.068 | 0.192 |

**What changed** (`norm.bend`, `plan.first` and `plan.ph*`, `plan.est`): the phantom is the first
line's POS moved right by its REF and ALTs' left trim, computed on the plan's copy of the first
line's REF and ALT (common suffix cut, then common prefix but one base, the least over the ALTs).
That is the first item's key unless the item moves left. Two cases:
- The guess is above the task's first write (a left shift): the first run stops there, UNSORTED,
  and runs again from that key. That is what fb-rewrite's phantom always did.
- It equals the first write: the task runs once, from the same phantom fb-rewrite's retry would
  have used, so the merges scr and scr30 gained are kept.

On SNP-first pieces it is the POS, as on main. With one run again, the first run reserves
`task.res`, so 3a3c539's 64 KiB start is undone (it had cost sub 39 to 49 MB at `--threads 1`).

**Proofs.** The phantom is existential in the piece lemma (any value is correct), so only the new
reads needed a lemma: `proof_e_task_buf.bend`'s `first_b` (`plan.first` on a line with a tab is
`plan.last.k` with the phantom `PH`; `tab_b`, `ph.if`, `ph_b` hand the buffer back through
`F.find` and `Q.text`, about 70 lines). Also `proof_e_task_piece.bend`'s `g3` (witness `PH`) and
`proof_e_task_one.bend`'s `oneC` (room `task.res`). One check round.

## 2. NR.want on w30k

With n from 64 MiB, a window growing through 64-256 MiB parks a 128 MiB block. Variants (-m -any,
one round, MB at `--threads 1` / default):

| build | w30k | h200 | w30 |
|---|---|---|---|
| main | 796 / 847 | 952 / 954 | 1567 / 2384 |
| speed (2n below 64 MiB, n from there) | 926 / 972 | 568 / 571 | 1186 / 1996 |
| 1.5n from 64 MiB | 926 / 968 | 571 / 575 | |
| 2n below 128 MiB | 799 / 854 | 703 / 702 | |
| **2n below 256 MiB** (kept) | 800 / 843 | 694 / 703 | 1056 / 1872 |
| 2n below 256 MiB for NR.room, 64 MiB for the splitter's copy | 799 / 854 | 575 / 575 | 1056 / 1867 |

w5 is the same in all (217 / 877-902 MB). The last row is best everywhere, but it was not kept:
`proof_s_w.bend` proves the splitter's room equal to `NR.room` (`room_eq`, `put_eq`) and borrows
`proof_b_run_buf.bend`'s room and `put_bytes_t` lemmas through it; a separate policy needs those
lemmas over the growth (an estimated 150-300 lines) for 125 MB on h200 only. h200 stays well under
main's. Proof: `want_ge`'s constant.

## Timings

`data/tmp/fix11/bench.sh 3 main speed new`, 11:46 to 12:31; load 1.4 to 3.6 (another reviewer's
runs in /tmp; no other timing). Each run is under `data/tmp/bench.lock`, `nice -n 19`,
`taskset -c 0-15`, `-c w`, with output to a file (removed first, then a sync). The output md5 was
the same across the builds in every run. Wall s (min-max of 3; kg.gz 2 runs, bcftools 1), peak RSS MB.

| input | main | speed | new | bcftools |
|---|---|---|---|---|
| 1000 Genomes sub (800 MB) | 0.28-0.29 / 227-247 | 0.30-0.32 / 262-284 | 0.27-0.33 / 219-239 | 3.35-3.57 |
| sub, `--threads 1` | 0.63-0.66 / 39 | 0.75-0.78 / 49 | **0.59-0.61 / 39** | |
| cohort (218 MB) | 0.111-0.121 / 237 | 0.127-0.129 / 278 | 0.113-0.117 / 239 | |
| cohort, `--threads 1` | 0.31-0.34 / 51 | 0.31-0.41 / 51 | 0.28-0.33 / 51 | |
| cohort `-m -any` | 1.15-1.20 / 352-357 | 1.30-1.33 / 358-364 | **1.05-1.09 / 323-326** | 1.27-1.36 |
| cohort `-m -any`, `--threads 1` | 3.67-3.83 / 75 | 4.93-5.07 / 77 | **3.52-3.69 / 73-75** | |
| scr | 0.107-0.123 / 81-91 | 0.067-0.083 / 105-113 | 0.076-0.088 / 104-111 | 0.073-0.092 |
| scr, `--threads 1` | 0.127-0.130 / 39 | 0.099-0.108 / 60 | 0.101-0.108 / 59 | |
| scr30 | 0.72-0.73 / 238-253 | 0.21-0.23 / 234-244 | 0.21-0.24 / 231-242 | 0.51-0.53 |
| scr30, `--threads 1` | 0.86-0.88 / 47 | 0.70-0.71 / 37 | 0.70-0.71 / 37 | |
| scr, valid END on every record | 8.3-8.7 / 79-90 | 3.61-3.70 / 94-100 | 3.51-3.65 / 91-101 | (exit 255) |
| same, `--threads 1` | 8.3-8.7 / 39 | 6.68-6.70 / 55 | 6.73-6.78 / 55 | |
| HG002 chr22 | 0.065-0.066 / 130-141 | 0.057-0.071 / 131-139 | 0.052-0.065 / 130-140 | 0.113-0.117 |
| HG002 chr22, `--threads 1` | 0.095-0.106 / 39 | 0.100-0.113 / 39 | 0.094-0.095 / 39 | |
| HG002 whole genome | 2.33-2.51 / 329-334 | 2.30-2.48 / 341-344 | 2.27-2.36 / 336-344 | 8.77-8.80 |
| HG002 whole genome, `--threads 1` | 6.62-6.80 / 43 | 6.89-7.04 / 57-59 | 6.92-7.05 / 58-59 | |
| 1000 Genomes chr22 `.vcf.gz` | 6.82-6.98 / 311-325 | 6.79-6.98 / 406-411 | 6.79-6.82 / 313-316 | 67.8 / 18 |
| same, `--threads 1` | 11.9-12.2 / 102-105 | 12.4-12.6 / 105 | 11.0-11.1 / 105 | |
| h200 `-m -any` | 2.36-2.53 / 952-960 | 2.09-2.22 / 568-577 | 2.14-2.22 / 696-705 | |
| h200, `--threads 1` | 2.35-2.51 / 954-958 | 2.07-2.16 / 570-575 | 2.13-2.20 / 698-703 | |
| w30k `-m -any` | 11.7-12.2 / 855-863 | 11.7-11.8 / 982-989 | 11.7-12.2 / **849-856** | |
| w30k, `--threads 1` | 12.3-12.4 / 800-807 | 12.2-13.1 / 927-929 | 12.4-13.0 / **801** | |
| w5 `-m -any` | 13.8-13.9 / 879-896 | 13.7-13.8 / 910-930 | 13.8-14.6 / 879-902 | |
| w5, `--threads 1` | 22.2-22.8 / 217-219 | 21.5-23.0 / 218-221 | 21.6-23.2 / 217-219 | |
| w30 `-m -any` | 50.9-51.7 / 2385-2394 | 50.2-51.1 / 2005-2009 | 48.8-50.8 / 1866-1870 | |
| w30, `--threads 1` | 59.7-60.3 / 1568-1570 | 57.3-60.4 / 1186 | 57.5-60.4 / 1056-1058 | |

- The whole genome at `--threads 1` stays 4% slower and 15 MB larger than main, on speed and new
  alike: fb-end's END check and fb-rewrite's half windows (their sections), not this branch.
- The genome times here are above the README's (1.8 s, 6.0 s) for main's build too: they ran on
  another day, and this machine had other load. The README keeps its times and takes the
  memory figures.
- bcftools stops on the END scramble (exit 255).
- `-m` on one line with many large records, new build: 10,000 samples with 325 / 650 / 1,300 ALTs
  took 7.5 / 30.3 / 120.7 s (255 / 369 / 954 MB); bcftools 6.5 s on the last (USAGE).

## Checks

- Gate (`gate.sh`, each step through `test/bcheck.sh`): `examples.bend` 38 TODOs only, `main.bend`
  "rely on unsafe" only, `PROOF.bend` ALL PROOFS CHECK with `--check-only` and `--verdict`.
- Against main's build (984688a), stdout, stderr and exit code, private dirs (`suite.sh`):
  `same.sh` 128, `par.sh` 312, `threads.sh` 2128 identical (usage errors and thread counts OK),
  `out.sh` OK, `index.sh` ALL PASS, `split.sh` 80 as bcftools.
- `cmp.sh`, 191 runs against main's build, each file under `-c e`, `-c w`, `--threads 1/3/16`,
  `-w 1/50/100000/100000000`, and `-m -any` at the default and `--threads 1`. The files: scr, scr2,
  scr1, scr30, the END and gVCF scrambles, chr22 and its END and gVCF shapes, the 1000 Genomes sub,
  the cohort, and `gen_ph.py`'s ph2 and ph30 (scrambles with a second ALT, `<DEL>`, `*`, `.`, lower
  case, or a one-base ALT added, so that pieces start on every shape the guess reads). Also h200,
  w30k, w5k, sp30 (`-c e`/`-c w` x 3 thread counts), w30 and w5. All the same but one run: ph30 with
  `-w 100000000`. Main's build and this one both segfaulted there, and stderr differed. Rerun:
  main, speed and new all hit the 900 s timeout with the same stdout, stderr differing only in how
  far each got. This is not from this branch: a whole-file window over 141 MB with `ALT_DUP`
  lines is pathologically slow on main too, and its segfault was not looked into.

## Not done

- The splitter's own growth policy (above): 125 MB on h200, for its proofs.
- The README's `--threads 8` and `--threads 4` memory rows, and its times, were not re-measured
  (the brief asked for `--threads 1` and the default).

# fb-fix11b: driver review 11, round 2's fixes (2026-11-01)

Brief: `notes/briefs/FIX11B.md` (decisions 6-8 in `reviews/responses-driver11.md`). Branch
`speed-fix11b` from 8646585. No law, spec or contract change. Scratch: `data/tmp/fix11b/` (builds
`fb_main` from main 984688a, `fb_base` from 8646585, `fb_new`, `fb_b1k`; the reviewers' inputs and
mine in `in/`, their generators and `gen_big4k.py` in `gen/`; `bench.sh`, `cmp.sh`, `suite.sh`,
`gate.sh`, `findsf.sh`).

## 1. The phantom guess (decision 6)

fb-fix11's guess decoded the first line's REF and ALT into Strings (`Q.text`) whatever their size,
and `plan.trims` reversed REF and took its length again for every ALT. A 100,000-base REF with
500 symbolic ALTs first in a piece (GPT's `plan_long_500.vcf`) took 1.5 s at `--threads 1`
(main 0.06 s); 40 lines of 1 MB deletions or insertions (Claude's `gen_bigref.py`) were about 30%
slower than main.

Now (`norm.bend`, `plan.ph*`, `plan.est.n`, `plan.trims`): `plan.ph.t4` finds the tab after ALT
(t5) before anything is decoded, and the guess is taken only when `t5 - t3` (REF, ALT and a tab)
is at most `plan.big()` = 4096 bytes; else the phantom is POS. REF's reversal and length are
computed once, and `plan.trims` stops at a trim of 0 (most first lines: an SNP's trim is 0 at the
first ALT). Below the bound the guess's work is linear in the line's REF and ALT bytes.

Proof: the phantom is existential in the piece lemma, so only `proof_e_task_buf.bend`'s `PHI`
(now over t5), `ph.if`, `OKP` (the size test) and `ph_b` (one more `tab_b` rewrite) changed.
`plan.trims` matches the list before the count, which is how bend accepts the self-call as
decreasing (a mutually recursive helper was refused).

A 1 KiB bound (`fb_b1k`) was tried on `big4k.vcf` (mine: dense chr22 lines, 60% with REF+ALT bytes
of 3,700-4,500 and a left pad, so pieces start on both sides of 4 KiB): no faster than 4 KiB
(0.396-0.421 s against 0.390-0.440 s at `--threads 1`, main 0.375-0.397 s; 5 rounds). That 5%
against main is on fb_base too and not from the guess; 4 KiB was kept.

## 2. README's scrambled row (decision 7)

framebender and bcftools interleaved, 5 rounds, `data/scr.vcf -c w`: writing to a file (the
README's method), bcftools 0.066-0.087 s and framebender 0.064-0.082 s (10 runs of each over
`bench.sh` and a separate run); to `/dev/null`, bcftools 0.048-0.057 s and framebender
0.062-0.071 s (Claude's 0.047-0.052 / 0.060-0.069). The row now reads 0.07-0.09 / 0.06-0.08 s,
and the clause says such files are still somewhat slower when the output is not written to disk
(0.06 against 0.05 s) and that 30 copies in a row (scr30) take 0.21 s against bcftools' 0.51 s.

## 3. USAGE's many-ALT -m bullet (decision 8)

One line, 325 ALTs, GT:AD (`data/tmp/memory/gen.py manyalt`, which reproduces Grok's 10,000-sample
file byte for byte), `-c w -m -any`, default threads:

| samples | new | main | bcftools |
|---|---|---|---|
| 10,000 | 7.37-7.42 s / 257-259 MB | 7.48 s / 321 MB | 0.48 s / 86 MB |
| 100,000 | 74.7 s / 1379-1383 MB | 76.1 s / 1891 MB | 4.97 s / 642 MB |

(new 3 rounds, main and bcftools 1.) The bullet now gives both runs' time and memory.

## Timings

`data/tmp/fix11b/bench.sh 5`, 14:12 to 14:25, main / base / new interleaved (order rotated each
round), each run under `data/tmp/bench.lock`, `nice -n 19`, `taskset -c 0-15`, `-c w`, output to a
file. Load 4.3 at the start (this agent's own correctness runs had just ended), 1.2-1.9 after; no
other timing. Output md5 the same across the three builds on every input. Wall s (min-max of 5),
peak RSS MB.

| input | main | base (8646585) | new | bcftools |
|---|---|---|---|---|
| plan_long_500 (GPT) | 0.057-0.068 / 39-41 | 1.52-1.57 / 38-41 | **0.049-0.066 / 31-33** | |
| same, `--threads 1` | 0.056-0.078 / 37 | 1.50-1.56 / 37-41 | **0.047-0.059 / 29** | |
| plan_long_100 | 0.056-0.075 / 39-41 | 0.347-0.373 / 39-41 | 0.048-0.059 / 31-33 | |
| same, `--threads 1` | 0.056-0.077 / 37 | 0.345-0.363 / 37 | 0.048-0.065 / 29 | |
| plan_long_1 | 0.056-0.067 / 39-41 | 0.057-0.068 / 39-43 | 0.048-0.069 / 31-35 | |
| same, `--threads 1` | 0.056-0.065 / 37-41 | 0.056-0.074 / 37 | 0.049-0.067 / 29 | |
| bigdel, 1 MB deletions (Claude) | 2.23-2.36 / 645-648 | 2.93-3.02 / 641-646 | **2.23-2.36 / 643-646** | |
| same, `--threads 1` | 3.39-3.54 / 233 | 4.15-4.22 / 233 | **3.41-3.54 / 233** | |
| bigins, 1 MB insertions (Claude) | 1.53-1.54 / 479-484 | 2.13-2.18 / 477-482 | **1.51-1.57 / 479-482** | |
| same, `--threads 1` | 1.90-1.95 / 245 | 2.55-2.63 / 243-245 | **1.90-2.01 / 243** | |
| big4k (mine) | 0.291-0.310 / 77-83 | 0.302-0.331 / 79-81 | 0.304-0.322 / 77-79 | |
| same, `--threads 1` | 0.374-0.388 / 29 | 0.393-0.421 / 29 | 0.390-0.422 / 29-33 | |
| 1000 Genomes sub | 0.271-0.291 / 243-247 | 0.267-0.350 / 237-239 | 0.265-0.280 / 238-239 | |
| sub, `--threads 1` | 0.632-0.644 / 39 | 0.585-0.629 / 39 | 0.583-0.635 / 39-43 | |
| cohort | 0.109-0.121 / 238-241 | 0.112-0.120 / 238-239 | 0.110-0.119 / 237-239 | |
| cohort, `--threads 1` | 0.276-0.326 / 51-53 | 0.244-0.362 / 51 | 0.260-0.349 / 51 | |
| cohort `-m -any` | 1.14-1.26 / 356-363 | 1.03-1.13 / 325-330 | 0.98-1.14 / 324-331 | |
| cohort `-m -any`, `--threads 1` | 3.56-3.81 / 75 | 3.52-3.78 / 75-79 | 3.54-3.78 / 75 | |
| scr | 0.107-0.121 / 83-89 | 0.064-0.078 / 108-113 | 0.064-0.080 / 109-111 | 0.073-0.087 |
| scr, `--threads 1` | 0.117-0.141 / 39 | 0.094-0.111 / 59 | 0.095-0.114 / 59 | |
| scr30 | 0.701-0.724 / 247-249 | 0.200-0.222 / 241-243 | 0.207-0.223 / 242-243 | 0.509-0.534 |
| scr30, `--threads 1` | 0.842-0.870 / 47 | 0.692-0.719 / 37-41 | 0.696-0.706 / 37 | |

fb-fix11's results (cohort, sub, scr, scr30) are kept. The new build's 8 MB less on the
plan_long files is the 100,000-base REF no longer decoded.

## Checks

- Gate (`gate.sh`, each step through `test/bcheck.sh`): `examples.bend` 38 TODOs only, `main.bend`
  "rely on unsafe" only, `PROOF.bend` ALL PROOFS CHECK with `--check-only` and `--verdict`.
- Against main's build, private dirs (`suite.sh`): `same.sh` 128, `par.sh` 312, `threads.sh` 2128
  identical (usage errors and thread counts OK), `out.sh` OK, `index.sh` ALL PASS, `split.sh` 80
  as bcftools.
- `cmp.sh`, 239 runs, stdout, stderr and exit code against main's build: fb-fix11's set (ph30 with
  `-w 100000000` left out: it crashes or runs 900 s on main's build) plus the plan_long files
  (`-c e`/`-c w` x `--threads 1/3/16`, and `-m -any`), the 1 MB and 100 kb / 10 kb deletion and
  insertion files (`-c e`/`-c w` x default and `--threads 1`), big4k, and the 325-ALT `-m` line.
  All the same.

## Found, not fixed (predates the branch)

`data/kg/sub.vcf -c w -w 100000000` segfaults on main's build (984688a), on 8646585 and on this
branch alike, every time, at the default and at `--threads 1`, with `ulimit -s unlimited` too:
stderr ends "bend: memory fault (machine stack overflow?)", after 35,351 bytes of output (stdout
and stderr the same across the builds). It is in fb-fix11's run set too, whose `cmp.sh` compared
outputs but did not flag crashes; this branch's `cmp.sh` now prints CRASH lines. With the window
as large as the 800 MB file, something in the trusted part or the runtime recurses deeply;
not looked into further.

## Large -w crash (2026-11-01)

`data/kg/sub.vcf -c w -w 2000000` (and above) segfaults; `-w 1000000` works; same on every build
since the window became a byte buffer. Found by fb-fix11b, diagnosed by lb-tolist (lawful-bytes
`notes/tolist.md`). Two causes, one under the other:
- lawful-bytes' `to_list` recursed once per byte on the C stack. Fixed in lawful-bytes@0.1.1.0
  (constant stack, faster, less memory); framebender and lawful-fields moved to it.
- framebender's own switch to String mode under `-c w` (`norm_seq.to_ms` -> `norm_run.to_spec`)
  turns the whole pending output buffer into a String (`to_list`, `chars`, then `String.take`/
  `drop` per record). At `-w 2M` that buffer is over 134 MB, so `chars` overflows the stack, and
  with a larger stack the String would need tens of GB. Not fixed: documented in USAGE (`-w`).
  A fix would hand the buffered records to String mode without converting the buffer at once.
Other recursions whose depth grows with the input (lb-tolist's list, from the compiled C; 16-byte
frames, 2 GiB stack, so about 134M frames): `spec.items`/`append_ck`/`ins.go` per buffered record;
`norm_seq` `cat.go`/`take_w.go` and `pend.add`'s switch past 2^28 bytes; per character of one line
in `norm_line` and `norm_split`; `norm_fix` `al.go` per allele letter; main's `.fai` to text. Only
inputs far past real ones (a 100 MB line or allele, a 100 MB `.fai`) reach them.
