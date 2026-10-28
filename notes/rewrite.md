# Rewritten records on bytes (phase C): plan

Brief: `notes/briefs/REWRITE.md`. Branch `rewrite` (= `main`, a357701).

Status (2026-10-28): plan approved by the lead with the four recommendations; step 2 (code) done
and checked; step 3 (proofs) done: `PROOF.bend` prints ALL PROOFS CHECK with `--check-only` (22 s)
and with `--verdict` (36 s), no `?TODO` in its import graph.

## Step 3: the proofs

`fast.pre`'s `Slow` branch (`norm.bend`'s `fix`) is proven in both of phase B's proofs: the
machine's step (`proof_b_adv_fast.bend`, `F.pre`, now `proof_c_adv.bend`'s `fix_ok`) and the
budget (`proof_b_budget_fast.bend`, now `proof_c_bud.bend`'s `fix_bud`). Those two call sites and
their imports are the only edits to phase B's files; no statement changed. About 13,800 lines in
39 files `proof_c_*.bend`:

| area | files | by |
|---|---|---|
| defs | `proof_c_defs` (the code without buffers: `NZ`, `ALK`, `VW`, `TXT`'s pieces) | me |
| tan | `proof_c_tan*` (NX.norm is `tan.bend`'s `var_in` on the window) | sub-agent (pc-tan) |
| pre | `proof_c_pre*` (NX.line's facts: the cut, POS, alleles, no END, no stale key, tabs) | sub-agent (pc-pre) |
| text | `proof_c_text*`, `proof_c_txt*` (the writer's bytes; the alleles' letters, the new POS) | me; `txt` by pc-tan |
| adv | `proof_c_adv`, `_advf`, `_cache`, `_hit`, `_hitl`, `_take`, `_tk`, `_judge`, `_run` | me |
| budget | `proof_c_bud*` | sub-agent (pc-pre) |

The take (`proof_c_tk.bend`) follows phase B's fast hit (`proof_b_adv_hit.bend`'s `fhit`):
`run_tick`, `NR.fix_done` as `run.bend`'s `body_line` of `Res{Normalized, q, t, False}`
(`proof_c_run.bend`), then `SL.went` with the judge `L.judge(fa, body) = RW(w, v, body)`
(`proof_c_judge.bend`'s `fix_res`, the slow path's `J.fast` answer through the window law). The
written bytes are `rebuild(fields(body), v, w) ++ term` (`proof_c_take.bend`'s `new_text`, from
`proof_c_text_l.bend`'s `tx_eq`); when the new line has the old line's length and bytes the code
takes the decoded path, and `ne_len_t`/`ne_eq_t` give `String.eq(t, body) = False` otherwise.

Statements of my own areas that the sub-agents changed (none below the laws): `norm_var` dropped
two unused hypotheses; `fix_info` states INFO as field 7 of the line's fields (`F7`), and
`fix_tabs` (the five tabs) was added. `proof_c_text.bend`'s failed writes go through one lemma
(`wrF`) so the kernel does not normalize the text (`--verdict` overflowed its stack before).

## Step 2: the code and its checks

Files: `norm_fix.bend` (new: the tests, the stale-key scan, the normalizer, the writer),
`norm.bend` (`fix`: `fast.pre`'s `Slow` branch now tries it before `decoded`), `norm_run.bend`
(`NR.fix_done`). The binary: `data/tmp/fb_fix`.

Timings (2026-10-28 06:30, final build `data/tmp/fb_final`, `-c w`, to a file, nice, nothing else
running; this build, `main`'s build (`data/tmp/fb_ref`) and bcftools interleaved, 2 passes in
opposite orders: chr22 15 rounds, scr 5, whole genome 7):

| input | this build | `main` | bcftools 1.24 |
|---|---|---|---|
| `scr.vcf` | 0.148-0.167 s | 5.24-5.38 s | 0.075-0.094 s |
| chr22 | 0.115-0.199 s, median 0.144 | 0.115-0.169 s, median 0.147 | 0.112-0.139 s, median 0.125 |
| whole genome | 6.97-10.17 s, median 7.95 | 7.69-10.19 s, median 9.19 | 8.40-8.55 s |

The whole genome's rounds vary by about 3 s for both framebender builds (disk); chr22's by about
+-30 ms. On chr22 the two builds are the same within the noise; scr is 35 times faster than `main`
and about 2 times bcftools.

Checks (all repeated on the final build):
- `test/compare.sh` (bcftools): whole genome 0, chr22 0, scr 0, a second scramble (`scr2`, 6,913 records from
  `hg002.chr22.indels.vcf`, seed 5) 0, `test/edge/sorted.vcf` 1 (the `<DEL>` record).
- `data/tmp/rw/cmp.sh data/tmp/fb_fix`: stdout, stderr and exit code identical to `main`'s binary
  (`data/tmp/fb_ref`) on all 128 runs: every `test/edge/*.vcf`, chr22, scr, the 24 inputs of
  phase A (`data/tmp/edge2`), and 8 new inputs (`data/tmp/rw/gen_rw.py` on its own FASTA
  `data/tmp/rw/rw.fa`: repeats at a contig's start, tandem repeats, lower-case, IUPAC and N
  stretches, a 6 kb CA repeat; records with 1-17 ALTs, `*`, ALT equal to REF up to case, IUPAC
  in ALT, N, REF mismatch, POS with a leading zero, 8, 9 and 10 columns, INFO with each stale key
  and near misses (`AAA`, `CIGARX`, `HOMLE`, `AA` without `=`), empty INFO entries, CRLF, CR at
  INFO's end, CHROM changes and a CHROM coming back), each under `-c e` and `-c w`, and `-w 1`,
  `-w 5`, `-w 300` on 9 of them.
- Tiny-limit build (the final code with the output buffer at 4 KB, the run's half-full mark at
  2 KB and the line and piece bounds at 300 bytes, in `norm.bend` and `norm_fix.bend`, so the
  writer's guards, `fix.fits` and the String mode are taken often): the same 128 runs identical
  to `main` (143 s). The reads are unchanged by this path (it reads the cached window only), so
  phase B's read-capped builds were not redone.
- The gate: `examples.bend` (TODOs only from LAWS.bend, as before), `main.bend` (unsafe only),
  `PROOF.bend --check-only` and `--verdict`: ALL PROOFS CHECK, each through `test/bcheck.sh`.

## Where the time goes

`data/scr.vcf`: 20,739 records, all biallelic, 685 bytes a line on average, of which INFO is 581.
Run alone (python, `chr22.fa`): 19,743 records move left (median 3 bases, 90% at most 18, max
141), 20,365 lose a base on the right, 6,713 on the left, 4,119 have a lower-case allele.

Timings (`main`'s binary `data/tmp/fb_ref`, `-c w`, to a file, nice, nothing else running,
3 interleaved rounds, 2026-10-28):

| input | framebender | bcftools 1.24 |
|---|---|---|
| `scr.vcf` | 5.33-5.38 s | 0.056-0.070 s |
| framebender's own output of `scr.vcf` (the same records, already normal: all take the fast path) | 0.092-0.098 s | 0.046-0.050 s |

So the records themselves cost 0.1 s on the fast path; the other 5.2 s are the slow path,
about 250 µs a record.

Profile: gprof on `fb_pg`, the generated C of `main.bend` built with `clang -O3 -pg`
(14.8 s under gprof, `--threads 1`; output identical to `fb_ref`'s apart from the command line in
the header). Shares of the samples:

| | share | what |
|---|---|---|
| `term_drop` + `span_fade` + `rfc_wrap` | 66% | reference counting of shared Strings |
| `String.split` (with the refcounting it causes) | 32% | 44% of all `span_fade` calls |
| `String.length` | 10% | about two walks of the whole line a record |
| `String.append` | 9% | `body ++ term`, joins |
| `J.noend.go` | 4% | INFO's END scan on the decoded line |
| normalizer and window decoding (`tan.*`, `List.take/length`, `chars`, `to_list`) | about 10% | 66,571 `var_in` calls: 3.2 tries a record (the window grows 0, 1, 3, 7, ...) |

The splits are mostly INFO's. For a record that changes, `J.fast` calls `B.Rec.fields(body)` (the
whole line), `Rec.rebuild` calls `Info.set_end` (INFO split at `;`, each entry split at `=`), and
`Rec.stale` calls `Info.has` four times (CIGAR, HOMLEN, HOMSEQ, AA; `||` evaluates all four),
each splitting INFO again. With INFO at 85% of the line, that is about 5 to 6 copies of the line
per record, all of them shared walks.

## The two directions, judged

- **A cheaper slow path** (Strings, less sharing): a code-local `stale` and `set_end` that scan
  INFO once in place, as `J.noend` does, would remove most of the splits: 5.3 s to perhaps
  2.5-3 s. Every remaining pass is still per character on a decoded line (decode, `ends_cr`,
  `c7`, `noend`, the join, `++ term`, `put_str`); at 250 µs a record now, it would stay
  10-50 times slower than bcftools. Not enough.
- **A bytes path for rewritten records**: the line is never decoded. The fields, INFO and the
  output stay bytes; only the alleles and a few reference letters are looked at. The floor is
  the fast path's 0.1 s. Chosen.
- In between (bytes for the line, but the normalizer as `tan.bend`'s `var_in` on small decoded
  lists): saves the normalizer's proof, but `var_in` on lists (shared walks, `List.get` into the
  window at every step, `init` by `take`) costs about 10-20 µs a record, so scr would end near
  0.3-0.5 s. The normalizer on bytes is a closed form over three counters (below), so its proof
  is the price of the last 3-4x. I propose doing it.

## Design

New code file `norm_fix.bend` (`NX`); small changes in `norm.bend` (one branch) and
`norm_run.bend` (one entry point). Nothing in the laws, the contract, the driver or `../lawful-*`.

**When.** A body line whose fast-path tests fail (`NF.line` gives `Slow`) now tries the fix path
before `decoded`:

1. `NX.line(b, s)` cuts the line again (`NF.cut`) and tests, on its own bytes:
   - POS: 1-9 digits, no leading zero (`NF.num`, as the fast path);
   - REF and every ALT (at most 16): one or more of A, C, G, T, N **in either case**;
   - no two alleles equal up to case (`(x ^ y) & 0xDF`, as `refeq` compares);
   - INFO has no END entry (`NF.noend`), and no entry with key CIGAR, HOMLEN, HOMSEQ or AA (a
     new scan of the same kind, `NX.nostale`); if INFO is the last field, the line does not end
     in CR (as the fast path).
2. CHROM is the run's (`Run.same`), the cached window is a `WKnown` of that contig, holds REF,
   REF lies within the contig, and REF equals the window's letters up to case (`against`, as
   the fast path: `WHit`).
3. The normalizer runs on the bytes (below). It needs the reference letters left of POS; if it
   would read before the cached window's start, it gives up.
4. If the variant does not change and every allele is upper case (`J.fast` would say `Same`),
   it gives up too (cannot happen after `NF.line` failed, except with more than 16 ALTs, which
   step 1 already refuses).

Any failure, and `WNeed`/`WMiss`, goes to `decoded`, exactly as today. The fix path asks no
reads of its own, so the read budget is unchanged.

**The normalizer on bytes.** Tan's algorithm as `tan.bend` runs it (`right`, then `left`), with
the alleles kept as three counters instead of lists. Write `a_i` for allele i's bytes (REF is
i = 0), `L_i` for its length, `R_k` for the k reference letters before POS (window bytes
`pos-1-k .. pos-2`). After k shifts and t trims on the right and d trims on the left, every
allele is

    allele_i(k, t, d) = drop(take(R_k ++ a_i, L_i - t), d)        at position pos - k + d

because a shift puts the reference base before the variant in front of every allele and drops its
last base (`R_{k+1} = b <> R_k`), and a trim drops the last base. So:

- `right` is a loop on (k, t) with the same fuel as `tan.right` (`pos + total`), testing the
  last base of each allele (byte `L_i - t - 1` of `R_k ++ a_i`: a window byte or a line byte), the
  lengths (`L_i - t >= 2`), and `pos - k >= 2`; the base it shifts in is window byte
  `pos - 2 - k`;
- `left` is a loop on d with `tan.left`'s fuel, testing the first bases (byte d of each);
- bases are compared as codes: `code(x)` gives 0-4 for A, C, G, T and everything else (N), the
  same map as `Base.of_fasta` (which agrees with `Base.of_letter` on the allele letters);
- each step reads at most 17 bytes; scr's records take about 10 steps.

**Writing.** The new line is built in a small scratch buffer: bytes `s .. e0` (CHROM and its
tab), `Nat.show` of the new POS, bytes `e1 .. e2` (tab, ID, tab), the new REF's letters, a tab,
the new ALTs' letters with commas, bytes `e4 .. lf` (tab, QUAL to the end of the line, LF). The
letters are `Base.letter` of the codes. INFO is copied as it is: with no END entry,
`Info.set_end` gives INFO back.

Then `NR.fix_done` does what the slow path's `NR.body_line` does for `Normalized` with a new
text, in the same run: bump (changed), no notes (no stale key), `same_run` with
`Ck{newpos, pos, line, Some{Nat.show(pos)}, n'}` and the scratch buffer as a `Raw` source
(`s = 0`). The run then copies those bytes into the output buffer as for any `Raw` text, so
`norm_run.bend`'s `add`/`flush` and their proofs are unchanged. Before that, the slow path's size
test (`res_fits`: the new text within `2^30 - ol`) is made on n', with the slow path's outcome
(`to_str`) if it fails.

**Cost.** Per record: the failed `NF.line` (already paid today), a second cut, the tests, about
10 normalizer steps, a copy of the line into the scratch buffer and one into the output. Expected
1-3 µs a record. Lines that go to `decoded` pay one more cut and test than today (under 1 µs).

## The refinement argument (fix path vs the String path)

Let L be the line's bytes `s .. lf`, `body` its text without terminator, `fs = J.pfs(body)`, and w
the cached window's answer `Known{clen, A, raw}`. Claim: when the fix path takes L, the run state
after `NR.fix_done` is the one the slow path reaches when `J.fast(Some w, fs, body)` gives
`Other{Some r}`, then `body.res` (fits) and `body_done`.

1. Fields, POS, INFO without END, CR: as the fast path's steps 1, 2, 4, 5 (`notes/bytes.md`). `fs`
   is `[f0 .. f6, ""]` and `end_ok` holds.
2. Not malformed, in scope: REF and ALTs are non-empty letters (either case).
3. Alleles: `Allele.read(f3) = Some v_0`, `Alleles.read(alts) = Some [v_1 ..]` with
   `v_i = map(code, a_i)` as bases. `Alleles.distinct` holds: two alleles with equal bases are
   equal up to case as bytes, which step 1 excludes.
4. REF check: the window holds REF within the contig, and equal up to case means equal bases
   (`Base.of_fasta` of the window letter and `Base.of_letter` of REF's), so
   `ref_check(...) = Some True`.
5. Normal form: `V.var_in(A, Bases.of_fasta(raw), v)` is `Some w'` with w' = the counters' variant
   (the normalizer lemma below). Not `Same` (step 4 of "When"), so `J.fast` gives
   `Other{Some{Res{Normalized, pos(w'), rebuild(fields(body), v, w'), stale(fields(body), v, w')}}}`.
6. Text: with no END entry, `Info.set_end(INFO, e) = INFO`; `rebuild` replaces fields 1, 3, 4 and
   joins with tabs, so `rebuild(...) ++ term` is the scratch buffer's text.
7. Stale: false, both when `same_var` (only the case changed) and when not (no stale key).
8. The run: CHROM is the run's (`Run.same`), so `keyed` takes `same_run`; `normalized`'s
   `Own{t ++ term}` and the scratch buffer's `Raw` bytes put the same bytes in the output and give
   the same item (`txt_len`), and `item(k, inpos, at, n)` is `Ck{pos(w'), pos, line,
   Some{f1}, n'}` with `f1 = Nat.show(pos)`.
9. The slow path would judge with its own window; the existing argument (any truthful answer
   that gives `Some` gives the spec's result) covers the cached one, as for `WHit`.

## What has to be proven

New statements, by area (files `proof_c_<area>*.bend`, notes `notes/rewrite_<area>.md`):

| area | statement | reuses | estimate |
|---|---|---|---|
| tan | the bytes normalizer (on mirrors of the line and the window) gives `V.var_in(off, Bases.of_fasta(raw), v)`; in two levels: a list-level loop on (k, t, d) equals `tan.right`/`tan.left` (`inits`, `shifted`, `tails`, `lasts_eq`, `firsts_eq`, `all_long` on the closed form), then the byte loop equals the list loop (each read is a list element) | `proof_var*` list lemmas | 1,500-2,500 lines |
| pre | `NX.line` passing gives the cut, POS, letters either case, distinct up to case, no END, no stale key: `J.pfs` shape, `Allele.read`/`Alleles.read` as codes, `Alleles.distinct`, `Info.has` false for the 4 keys | `proof_b_cut*` (cut, num, noend), `proof_b_alleles*` | 800-1,300 |
| text | the scratch buffer is `enc(rebuild(fields(body), v, w') ++ term)`: `set_end` without END is INFO, `join(put(...split...))` is the splice, `Allele.show` of codes is the written letters, `Nat.show` | `proof_fast` (`join_split`, `rebuild_same`) | 600-1,000 |
| adv | `fast.pre`'s `Slow` branch: the fix path's outcome is `line_step` of the line (a `fix_judge` like `hit_judge`, the REF check either case like `against_hit`, `fix_done` as `body_line` of the result), and the declined cases are today's `decoded` | `proof_b_adv_hit`, `_fast`, `_slow`, `proof_b_cache_hit` | 800-1,200 |
| budget | the new branch is one `Went` per line and asks nothing | `proof_b_budget_fast` | 100-400 |

Total about 4,000-6,500 lines, against phase B's 57,000. Nothing in `norm_run.bend`'s proofs
changes (the scratch buffer is a `Raw` source). The statements below the laws stay as they are; if
one has to change, it goes to the lead first.

Order: I write the code first (step 2), check outputs and timings, then fix each area's exact
statements in skeleton files with `?TODO` deliverables (as phase B did). The four areas tan, pre,
text and adv are independent once the statements are fixed: I propose to dispatch tan and pre to
two Herdr sub-agents, and do text, adv and budget myself, assembling at the end.

## Expected gain

| input | today | expected | bcftools |
|---|---|---|---|
| `scr.vcf` | 5.33-5.38 s | 0.12-0.2 s (floor 0.095 s) | 0.056-0.070 s |
| chr22 | 0.12-0.16 s | unchanged (only lines that fail `NF.line` pay a second cut) | 0.12-0.14 s |
| whole genome | 9.1-9.7 s | unchanged | 8.5-8.6 s |

## Checks planned

- `test/compare.sh`: chr22 0, scr 0, `test/edge/sorted.vcf` 1, whole genome 0.
- Byte-identical stdout, stderr and exit code against `data/tmp/fb_ref` on every `test/edge/*.vcf`,
  chr22 and scr (`-c e`, `-c w`; `-w 1`, `-w 5`, `-w 300` on some), plus new inputs for this
  path: multi-allelic records (2-17 ALTs), `*`, lower and mixed case, N in REF and in the
  reference, IUPAC letters in the reference, REF mismatch, alleles equal up to case, records near
  a contig's start (shift to POS 1) and near the window's start, long moves (longer than the
  margin), CHROM changes, CRLF, INFO with END and with each stale key, and records that move
  before already written ones (UNSORTED, `-w` small).
- The tiny-limit builds of phase B (the path reads the cached window directly).
- The gate (`check.sh`'s four steps), each through `test/bcheck.sh`.

## For the lead to decide

1. The bytes path with the normalizer on bytes (above), rather than `var_in` on decoded lists
   (proof about 1,500-2,500 lines smaller, scr about 0.3-0.5 s instead of 0.12-0.2 s).
2. The scope: lower case and up to 16 ALTs in (lower case is 20% of scr); records with a stale
   key in INFO, an END entry, or a window that does not reach far enough left stay on the String
   path.
3. The scratch buffer as a `Raw` source (one more copy of each rewritten line, no change to the
   run's proofs) rather than a new `Txt` variant (one copy less, changes `proof_b_run_add`/`_bl`).
4. Two Herdr sub-agents (tan, pre) once the statements are fixed.

## For the lead (end of step 3)

1. Files to commit: `norm.bend`, `norm_run.bend`, `norm_fix.bend`, `proof_b_adv_fast.bend`,
   `proof_b_budget_fast.bend` (call sites only), the 39 `proof_c_*.bend`, `notes/rewrite*.md`,
   `notes/briefs/REWRITE*.md`. Nothing else in the tree is mine.
2. `proof_c_pre_str.bend` copies a few `proof_fast.bend` lemmas, and `proof_c_txt_lem.bend` copies
   phase B's `pos31`/`four_pow`/`sum32` (to keep LAWS.bend out of their import graphs while they
   were checked alone); both could import the originals instead. Harmless as is.
3. Two rebuilds of `main.bend` from the same sources gave binaries of the same size that differ in
   about 32k bytes (`data/tmp/fb_fix`, 04:59, against `data/tmp/fb_final`, 06:08). Both pass the
   same 128 runs; the final checks and timings use `fb_final`.
