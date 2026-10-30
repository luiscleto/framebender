# Speed on INFO/END and gVCF lines: investigation (2026-10-30)

By the fb-end agent, read-only, on main ea683cd. Scheduled after the split branch lands (it reworks the machine). Scratch: `data/tmp/end/` (generators `gen_end.py`, `gen_gvcf.py`).

The END slowdown is entirely in the machine, and no law needs to change. Every record with an INFO/END entry leaves the bytes fast path and is decoded into a `String`. That costs a fixed amount per line rather than something that grows over the run. A second effect multiplies it when bad ENDs appear: any piece holding a BAD_END is done twice, once in parallel and again sequentially. Nothing tracked was edited (`git status` is clean). The scratch files are in `data/tmp/end/` and take 1.1 GB, mostly the 400k-record test files, which can be regenerated.

## Reproduction
All runs used `flock … nice -n 19 timeout … taskset -c 0-15` with `BEND_NO_TELEMETRY=1`, on a fresh `./build.sh` binary (`data/tmp/end/fb`), with `-c w`. The generator is `data/tmp/end/gen_end.py`. I didn't run the whole genome; the first 400k genome records (chr1 and part of chr2) stand in for it.

| input | 16 threads | `--threads 1` |
|---|---|---|
| chr22 | 0.056 s | 0.105 s |
| chr22, valid END on every record | 1.22 s | 3.27 s |
| chr22, END, 2% of them POS−1 | 4.60 s | 6.53 s |
| 400k genome records | 0.23 s | – |
| 400k genome records, valid END | 6.5 s | – |
| 400k genome records, END with 2% bad | 36.3 s | – |

At `--threads 1` the time is linear in the number of records (6k, 12k, 25k, 50k: about 65 µs each), so nothing grows within a run. Scaled up to the whole genome, valid END would take about 66 s and 2% bad END about 370 s, which is in line with the 419 s seen.

## Where the time goes
- **The fast path refuses END.** `norm_fast.bend`'s `noend` test (and `norm_fix.bend`'s copy for records that need rewriting) answers Slow for any INFO with an END entry. The line then takes `norm_seq.slow`: `text()` decodes the whole line into a `String`, then `J.pfs`, `cut`, `noend` and `scan`/`ikey` walk it. A gprof build at `--threads 1` counts, per record:
  - `bytes_to_list` and `chars`: 714 steps each, which is the line's length (about 700 bytes);
  - `cut_go`: 655 steps;
  - `ikey` and `ikeyT`: 98 steps each.

  There is exactly one `slow.try` per record and the reference window is never regrown, so the cost is the String path's fixed price per byte of line.
- **Pieces with a note are redone sequentially.** `merge.ok` (`norm.bend`) splices a task only if it wrote no notes (the notes' line numbers are counted from the task's own start). A BAD_END under `-c w` writes a note, and 2% bad puts one in nearly every 3.5 MB piece. The task's work is thrown away and Q does the piece again, so in the profile every line is decoded about 1.9 times.
- **gVCF is mostly a different case.** In real gVCF, END sits on `<NON_REF>`/`<*>` reference blocks, and variant lines carry `,<NON_REF>`. These records are out of scope, which is judged before BAD_END, and the fast path also sends symbolic ALTs to the String path. Measured on chr22: 0.64 s with `,<NON_REF>` added to every ALT, 0.35 s as short reference blocks (`data/tmp/end/gen_gvcf.py`). That is 6–11× slower, with no END check involved.

## Where the fix goes
It belongs to the machine: the fast-path code, its refinement proofs, and the parallel merge proofs. The science layer is fine as it is: `judge`'s order of checks, `Info.end_ok`, `Info.set_end` and `Rec.rebuild` stay as written. No law in `LAWS.bend` or `MACHINE.bend` changes, and neither does the contract. Only internal lemma statements inside proof files change, such as `proof_fast.bend`'s "Pass ⇒ Same", which assumes no END today.

## Proposed fix, cheapest first
1. **Check a valid END on bytes.** Replace `noend` with a byte scan that returns: no END, exactly one `END=<digits>`, or doubt. The value is read with the existing `num` reader (the same one POS uses) and must equal POS + len(REF) − 1, computed in U32. If it matches, the record passes as it does today. Anything else (two ENDs, `END=.`, a mismatch, an overflow) still goes Slow, so no outcome moves.
   - Proofs: a scan lemma linking the result to `B.Info.ends` / `Info.end_ok`, adapted from `proof_b_cut_ne*.bend` (about 700 lines today), reusing `proof_b_cut_nat.bend` for the digits. Then restate the Pass⇒Same lemma in `proof_fast.bend` / `proof_b_cut_pair.bend` with `end_ok` true.
   - Estimate: 800–1,300 lines, about the size of the earlier "pre" area in `notes/rewrite.md`.
   - It removes the valid-END slowdown. The same scan can then replace `NF.noend` in `norm_fix.bend`, so records that need rewriting also get `Info.set_end` on bytes; that is about 400–800 more lines (`proof_b_cut_fx.bend`).
2. **Judge BAD_END and Skipped on bytes.** Add outcomes to the fast path's `Pre`: BAD_END (an END entry whose value is wrong), and out of scope (not malformed, but some ALT allele is not all letters), both passed through at the input POS. Only CHROM and POS need decoding, for the note. The second outcome is the one that matters for gVCF.
   - Proofs: the Skipped side is `Rec.malformed` false and `Text.any_not_letters` true on bytes; then a new case in the bytes-advance proofs (`proof_b_adv*`) for the new `Pre` outcomes.
   - Estimate: 600–1,000 lines.
3. **Let tasks keep their notes.** Allow `merge.ok` to splice a task with warnings by renumbering their line numbers and appending them after S's notes. This is the change that removes the redo when bad ENDs (or any warnings) are spread through the file.
   - Proofs: in the merge proofs (`proof_e_merge_*`, about 2,000 lines today): the renumbering, how `notes` combine, and the stop and `-c e` interaction.
   - Estimate: 500–1,000 lines, and the riskiest of the three.

I'd do 1 and 2 first, once the split branch lands: together they bring both END and gVCF lines back onto bytes. Item 3 matters only for files with many warnings.
