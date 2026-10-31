# Splitting multiallelic records (phase I): what bcftools does, and the draft laws

Brief: `notes/briefs/SPLIT.md`. Branch `split` (worktree `../framebender-split`), on 36990fc.
Steps 1 and 2: laws accepted after round 3. Step 3: approved spec installed; prototype timed; stage 2
approved; milestone (1), the byte splitter and its proof, done (below). Scratch in `data/tmp/split/` (not
committed): the toy reference, the cases, `run.sh`, `gen_ex.py` (writes the examples), and in
`draft/` the science files with the proposed change applied (`draft_r1/`, `draft_r2/`: earlier
rounds'). The draft type-checks, and its 107 examples evaluate.

## Law change: the step bound with -m (option (a), accepted)

**Status.** Accepted by the owner and the three reviewers (`reviews/*-split-bound.md`, decisions
29-36). Installed in `MACHINE.bend` as `splits.of(B.Args.parse(argv))` and `split_room`; the
budget proofs that charge the split records are in progress. The fit below is corrected per
decisions 29-34.

**What the bound is.** Law `machine` (MACHINE.bend) says the program finishes "within bound steps
and bound reads", where

    bound = pieces + 3 + args length + (VCF length + 1) × (FASTA length + 3)

and MACHINE.bend's comment states its purpose: "A bound for the proof (the machine must stop and
cannot read without end); not a speed target." The proof (the budget, `proof_b_budget_*`,
`proof_b_bud_*`, and the threads machine's `proof_e_bud_*`) gives every input line that can ask
for reads an allowance `LA = 2 RW + 2 ZW` (RW = 1 + max(1, |REF|), ZW = 2 + the longest contig)
and shows the steps and reads stay within the sum, which fits `bound`.

**Why it no longer fits with -m.** A split line's records are not input lines, and each record
may ask for its own reads (it is normalized on its own). Charging each record a full `LA`, as the
budget charges a line, does not fit the bound:

- Example: a 10-base contig (`|FASTA|` = 14), one line `1 1 . <10-base REF> <100 one-base ALTs>
  . . .` (about 223 bytes). Charged per record: 100 × 46 = 4600. That line's share of the bound
  is about 224 × 17 = 3808.
- In general the charge grows like (pieces × |REF|), which is quadratic in the line's length,
  while the bound grows like (line length × |FASTA|). With a short FASTA, no constant factor
  covers it.

The real machine reads far less (the records share POS and REF, their windows nest, and after the
first record the window is held), so the law is very likely still true. Proving that needs a new
amortised argument about the window across all the records of a line, in the byte and String
modes, the fast path and the threads machine. That is a large proof with a real risk of a late
dead end. Option (a) keeps the per-record charge simple and gives the bound room for it.

**The change (only with -m).** Without `-m` the bound stays exactly as it is. As installed:

```
def splits.of(m: Maybe<&2, B.Cfg>) -> Bool          # the parsed command line's -m
def split_room(sp: Bool, +vcf: String) -> Nat       # (|vcf| + 1)^2 with -m, else 0
def bound(+argv, fasta, +vcf, cs) -> Nat:
  ... as before ... + split_room(splits.of(B.Args.parse(argv)), vcf)
```

The comment in MACHINE.bend gains decision 35's sentence: "With -m, plus (VCF length + 1)
squared, so that each record of a split line (one per ALT) can be charged a line's allowance."
The plain statement of law `machine` in docs/LAWS.md does not mention the formula and does not
change.

**Why it is still only a proof bound.** It changes no output, message or exit code, and no step
the machine takes; it only gives the proof's allowance room. It is still finite and computed from
the inputs before the run (the machine still must stop, and still cannot read without end). The
machine's real use is unchanged: a split line costs its records' reads, which in practice are
almost always served by the window the first record asked for.

**The fit, with margin** (corrected per decisions 29-34). V = VCF length, F = FASTA length.
- Lines are measured as the proof does: a line of text length `t` counts `n = t + 1`, so
  `Σn ≤ V + 1` and `Σn² ≤ (V + 1)²`. A candidate line (`-m`, not MALFORMED, two or more ALTs; k
  ALTs, REF of R bytes) has `R + 2k + 8 ≤ t` (ID, QUAL, FILTER, INFO may be empty, and the last
  line may have no LF: `c⇥1⇥⇥A⇥C,G⇥⇥⇥` is 13 bytes), so `a = 1 + k ≤ n/2` and `2aR ≤ n²/4`.
- Charge: every candidate line gets `1 + k` allowances, split or not (overcharging a refused or
  passed-through line is harmless): `a × LA ≤ 2aR + a(2FM + 6)` with `FM ≤ F`. The first
  allowance is the line's own, already in `(V + 1)(F + 3)`; the extra `k` allowances and the
  displaced hand-outs (the existing term is spent in full: `(V + 1)(FM + 2)` for the windows and
  `V + 1` for hand-outs) are charged to the square.
- Output: a split record's text is no longer than its line's (a lemma to prove), and the output
  step uses `out_len`'s constants (21 per record, output counted twice on a stop).
- Total extra ≤ `(V + 1)²/3 + 13(V + 1)/12` when the file has a line: about **3 times margin**
  under the square (decision 31; the draft's 3.9 was wrong). The full square is kept (36).
- Example where the line's share of the old bound is short (32): REF of 100 `A`s, ALTs
  `A,C,G,T,N,AA,AC,AG,AT,AN`: charge 2460 against 2363.

Option (b), proving the amortised bound under the current law, stays possible later. It would not
change the law back; the larger bound would only be looser than needed.

**Unrelated, already done (no law change): the pump's fuel.** With `-m` a split line makes records
during the pump, so the pump's one fuel could run out and cost unpaid `Ask[]` steps. The pump now
has two fuels: the input's, and the records', refilled from the state when spent (`pump.r`,
`pump.fill` in norm_seq.bend). With the measure ordered by the input, then the records, neither
runs out (`proof_b_drive_pump.bend`, `pumpL`/`pumpR`, invariant `LX`).

## Law change: CR (accepted, installed)

During milestone (2), the proof of `twice_run` under `-m` failed: the law was false as approved.
The lead kept `twice_run` whole and changed `split_when` instead. The three reviewers accepted the
change (`reviews/*-split-cr.md`, decisions 24-28 in `reviews/responses-split-law.md`). It is
installed in `types.bend` and `LAWS.bend` and proven (the draft was `data/tmp/split/draft_cr/`).

**The counterexample** (`data/tmp/split/cr/t2.vcf`, reference `ACGTACGTACGTACGTACGT`). The header
defines `END` as `Number=A`, and the one body line is

    1	05	.	A	C,G	.	.	END=5\r,6          (\r: a CR byte inside the line)

- Run 1 (`norm -c w -m -any`) split it. Record 1's INFO is `END=5\r`, which is not a number:
  BAD_END, passed as it came, written as `1	05	.	A	C	.	.	END=5\r` and LF.
- Run 2 reads that text back as body `…END=5` with a CR LF terminator. END is now fine, so the
  record is normalized and POS `05` is rewritten as `5`. Both runs exit 0, and the bodies differ.
- **Cause.** A value cut from the middle of a comma list can end a record in a bare CR. An input
  line cannot: the reader takes CR LF as the terminator. Read back, the CR becomes part of the
  terminator, so run 2 judges a different line.

**The change.** With `-m`, a line to split (not MALFORMED, two or more ALTs) whose body holds a CR
byte anywhere is not split. The body is the line without its terminator (LF, or CR LF), so a CR
just before the final LF is the terminator's, and `\r\r\n` is refused. It gets a new code,
`BAD_CR`.
- **Precedence.** `BAD_CR` comes first in `split_problem` (before ALT_DUP); it is a property of the
  whole line. Decision 7's order is unchanged: if `judge`'s outcome for the whole line stops the
  run, that outcome comes first (`unsplit_in`). So on `t2.vcf`, `-c e` stops with BAD_END (the
  whole line's END is `5\r,6`), as without `-m`.
- **Handling** is as for every split refusal. Under `-c w` the line passes as it came, with a
  warning `BAD_CR <chrom> <pos> line N<TAB>carriage return inside the line; not split`. Under
  `-c e` the run stops.
- **Unchanged:** lines with one ALT (a CR or not), runs without `-m`, and every other split law.
  The statement of `split_when` (`refusal(parts) == Some{split_problem}`) is unchanged; its
  definitions gain one case each:
  - `types.bend`: `Code` gains `BadCr` ("BAD_CR", with the detail above); `Text.has_cr`;
    `Rec.parts` passes `Text.has_cr(body)` (the whole body, decision 28) to `Rec.parts.if`, which
    checks it first, through a new `Rec.parts.cr`.
  - `LAWS.bend`: `split_problem`'s list starts with `Bool.pick(…, B.Text.has_cr(body),
    Some{B.BadCr{}}, None{})`.
- **Why it keeps `twice_run` whole.** No record of a split line holds a CR, so every record reads
  back as written. A refused line is passed as it came, and reads back as itself.

**Plain statement** (docs/LAWS.md, and the `split_when` row of the laws table): "With `-m`, a
well-formed line with two or more ALTs is split exactly when none of these holds: a carriage
return anywhere in the line other than the one just before its final LF (`BAD_CR`); two equal
ALTs (`ALT_DUP`); … (the rest as now). Otherwise the line is refused. A whole-line outcome that
stops the run is reported first; otherwise the message names `BAD_CR`, if it holds, and then the
first of the later reasons, reading the line left to right."

**Differences from bcftools**, a new row:

| case | bcftools 1.24 | framebender | why |
|---|---|---|---|
| a line to split with a CR inside (`t2.vcf`, `in.vcf`) | splits it. Typed numbers drop the CR (`END=5\r,6` with `Integer`: `END=5`, `END=6`, POS `05` read as 5). Strings keep it: `in.vcf` (`AF=0.1\r,0.2`, `String`) gives a record ending in `0.1\r`, which bcftools' own second run reads as `0.1`, so bcftools is not idempotent there | `BAD_CR`, not split (passed as it came under `-c w`) | a CR inside a line is not valid VCF; cutting a value at a CR can leave a record ending in CR, which a second run reads as a CRLF ending |

**Examples** (in `examples.bend`):
- `parts` of `t2.vcf`'s line and of `1 2 . C A,G . . AF=0.1\r,0.2`: `Unsplit{BAD_CR}`.
  `split_problem` gives `Some{BAD_CR}`.
- `1 2 . C A . . AF=0.1\r` (one ALT): `Whole`, as before.
- The AF line, `-c w`: passed as it came, warning `BAD_CR` (line 6), exit 0. `-c e`: stops with
  `BAD_CR`.
- `t2.vcf`'s line, `-c e`: stops with BAD_END (decision 7). `-c w`: passed as it came with
  `BAD_CR`, and running again on that output gives the same body (`twice_run`).

**Machine.** The byte splitter counts CR bytes in the body (`go.nocr`, `norm_split.bend`) and hands
a line with one to the String path; its proof against `B.Rec.parts` covers that guard
(`proof_s_drv.bend`).

## Open leads

**Pieces redone on the main thread (deferred until `-m` lands; a machine design change to the
phase-E proofs).** With `-m` on the cohort, 16 threads are no faster than 8 (1.8 s; one thread
5.5 s). The main thread is busy 1.4-1.6 s of that, so it is the bottleneck. A scratch build
(`data/tmp/split/dirty/tree`, not in the tree) in which a task says why its piece came back
found where its work comes from:
- **Cohort `-m`:** 62 pieces; 6 left to the main thread.
  - 3 are empty pieces (length 0), and cost nothing.
  - 3 are tasks whose own run stopped with UNSORTED. A task starts as if the last record written
    had its first line's POS. In all three, that first line holds an insertion whose record
    normalizes one base left: `20051835 G A,GCG` gives record `20051834 A AGC`;
    `20059895 T G,TAT` gives `20059894 C CTA`; `20113389 G C,GGG` gives `20113388 C CGG`. Inside
    the task the record is below that stand-in, so it looks unsorted. In the real run it is not.
  - Each of these pieces (about 25 lines, about 75 ms with `-m`) is then redone by the main
    thread. With the first line of every other piece (about 3 ms each, also split there), this is
    most of the serial time.
- **Not caused by `-m`:** the cohort already split (no `-m`) has 7 such pieces and 4 empty ones.
  `joined.vcf` with `-m` has 6 merge refusals and 13 empty pieces.
- **The lead:** let a task start from a lower stand-in key and leave the UNSORTED check to the
  merge, which already makes it. That changes the task's start state and the phase-E proofs
  (`proof_e_task_*`, the merge).

**Output reserve (done, kept).** A task now reserves twice its piece's size for output under `-m`
(`task.res`, `norm.bend`); without `-m`, the piece's size as before. Memory blocks come in powers
of two, so any reserve over 4 MiB takes an 8 MiB block. Measured against the build without it (3
rounds, the same outputs, the same times):
- **Cohort `-m`:** 494-500 MB to 353-358 MB. Its output is 1.32 times its input, so each 4 MiB
  buffer used to grow into an 8 MiB block while still holding the 4 MiB one.
- **Lighter files pay for the larger block:** `-m` on joined 276-281 to 316-322 MB; `-m` on HG002
  chr22 139-142 to 179-181 MB.
- **Without `-m`:** unchanged.

Kept: heavy multiallelic cohorts are what `-m` is for. Halving the pieces under `-m` might save
memory everywhere, at the cost of more first lines on the main thread; it is untested.

## Stage 2, milestone (2): the machine integration (in progress)

**State.** main (47e2aa5, phase J: `-W`) is merged into the working tree (file-wise; `types.bend`
and `proof_f_args.bend` resolved by hand: the `-m` parsing and `-W` side by side). Build
`data/tmp/split/fb_m3`.

**Machine changes in this milestone** (no approved law changed beyond the CR change):
- The pump has two fuels (`norm_seq.bend`: `pump`, `pump.r`, `pump.fill`): the input's, and
  the records', refilled from the state when spent. With `-m` a split line makes records during
  the pump, so one fuel could run out; with two, the measure ordered by the input, then the
  records, never runs out (`proof_b_drive_pump.bend`, `pumpL`/`pumpR`, invariant `LX`). Cost:
  none measurable.
- `-m` reserves twice the piece size for a task (`norm.bend`, `task.res`), as approved.

**Proof design changes** (internal definitions, no law):
- `S.Moved` (byte mode to byte mode) also says the definitions of the text still to come are
  kept: `DEFS(p2, cs) == DEFS(p, cs)`. Six places build it; each had the fact at hand.
- `S.Kept`, when the first source is a record buffer (`SPP`, `SRP`), says the plain sources are
  those after it: `plain(s2) == plain(rest)`. It holds by reduction at every place.
- The threads task invariant (`proof_e_task_loop.bend`): `Trk` carries `DEFS(p, cs) == dfs` and
  the run through the pending records (`RG`); `Hold` says the piece is Q's only *plain* source
  (records of a split line may sit in front, which the machine's `src_b` skips); the task state's
  own definitions field is kept apart from the batch's.
- The feeding guarantee `Fed` (`proof_e_qif_fed.bend`) says the fed state keeps the definitions
  and the record sources.

**Proof status.** Everything checks except the sequential step budget: `PROOF.bend` has 27 holes,
all in `proof_b_budget_*` and `proof_b_bud_*` (fb-budget, branch `split-budget`). The threads
machine's 8 holes are closed (`wrap` 4, `wrap_col` 2, `wrap_clean` 1, `mach_asm` 1), and so are the
threads machine's 14 budget holes (`proof_e_bud_*`: the step's `W.dfs_of`, the batch's definitions
`StP.dfs(p) == dfs` from `PhaseOK`, WF's widened ninth fact, `S.report` with `DEFS`, the record
sources in `where_eq`, the edge's fuel 4096) and the sequential assembly (`proof_b_assemble`'s
`machine_go`/`machine_h`: the report with `L.defs(concat cs)`, as `start_ok` gives it).
The bound of decisions 29-36 is installed in `MACHINE.bend` (`splits.of`, `split_room`); the start
lemmas (`bud_need`, `start_need`) meet it by `need <= old bound <= bound` until the budget charges
the split records. Phase B's potential now charges them (fb-budget's `BN.ALL`/`XA`/`WAX`,
cherry-picked as 840fe0b): the threads machine's budget follows it (`proof_e_bud_fed`: `stK`
carries the opts, `all_lines`; `proof_e_bud_comb`: the merged state's `XA` is within Q's, `xa_app`,
the opts kept along the edge, `fed_o`). `proof_e_bud_start.start_need` is phase B's
`start_fit` (split-budget b27752d; it checks once split-budget is merged) (the start fit with the threads machine's 12 per piece of 256 bytes, `K`, and the
output under the square: `BR.out_len` is false under `-m`, data/tmp/split/outlen/gen.py).

Done in earlier stretches: `proof_f_out` (the `-m` parser states, the `-W` record); `wrap_mc` (the
merge: "in the body" comes from `segok`'s first conjunct, so the state's `DEFS` is its field);
`wrap_clean` (the edge's fuel is 4096 since milestone 1, so the four generated levels E3..E0
became one lemma recursive on the fuel, `Ef`, with the level below as a hypothesis, `IHE`);
`wrap_col`'s `wf_args` and `none_chunk`; `seg_drain`'s `drain` (a split line's records go
through the phase-1 chain one by one: the chain is now stated for "the line's other records,
then the lines after", `pieces_drain`, `drain_body`; the hand-off to phase 2 lifts the records
first, `parP`).

**Q's definitions field and the batch's (done).** The threads machine runs a batch's tasks, and
merges them, with Q's own definitions field at that step (`norm.bend`, `dfs_of`); the invariant
states the tasks' facts (`BatchOK`) over the batch's `dfs`. The proof now ties the two (internal
definitions only, no law):
- `WD.InvW` starts with `EofD(eof, S.DEFS(p, held ++ cs), dfs)`: until Q has the end of the
  file, Q's definitions of the whole rest are the batch's (after it, no batch starts, so nothing
  is claimed). Collecting and asking (`BColP`, `BAskP`) also say `S.StP.dfs(p) == dfs`: a batch
  starts only at a quiet Q, which is in the body (`qb_defs`), so there the field is `S.DEFS`.
- Every Q step keeps `S.DEFS`. `S.Moved` says it in every mode now (it said so only for byte mode
  to byte mode), and `AdvG`'s Ended and Yield cases say it too; the String-mode advance lemmas had
  the fact at hand (`defs_body`, `hdd`, `defs_keep`). Whole steps get it from a new layer,
  `proof_e_wrap_qd.bend` (as `proof_e_wrap_qx.bend` does for the options): `st_defs` is `S.DEFS`
  read on the machine's own state, equal to it on a picture (`mk_defs`), so the fact joins phase
  B's step guarantee (`StepG2`) without changing it; out, finish, idle, the pump along `AdvG`,
  feeding, answers and pieces. A step that ends the run claims nothing.
- `OutG` (the end of a step) says the field and `S.DEFS` are kept; the edge chain `ED.Ch` says
  `S.DEFS` is kept in every mode.
- The merge (`merge_k`, `mok_state`) takes Q's field as it is (`dfs2`): when the merge is taken,
  the task's run is in the body, so `dfs2` is Q's `S.DEFS`, which is the batch's.
- `wstart` takes `dfs == L.defs(concat cs)`, from a start lemma that also gives the start state's
  `S.DEFS` (`DST.start_ok_gd`; phase B's `start_ok` is unchanged); `machine_h` instantiates it.

**Tests** (all on `fb_m3`):
- Spec against machine (`specrun/vs_all.sh`): 150 of 150 identical (28 fuzz files and the two
  CR cases, five option sets each).
- bcftools 1.24 `-c w -m -any` (`cmp_m.sh`): cohort 3,341 records, 0 differing; HG002 chr22
  50,861, 0; HG002 whole genome 4,096,123, 0; scrambled set 20,739, 0; joined `sub.vcf` and
  `data/kg/sub.vcf` 57,534 each, 12 differing (the symbolic SVs bcftools realigns, as without
  `-m`).
- Well-formed fuzz (`test/split.sh`, new, with `test/gen_split.py`): 100 seeds, both
  `--multi-overlaps` settings, 200 of 200 the same as bcftools.
- `test/same.sh` 128 identical; `test/par.sh` 312 identical against main's build (`fb_ref`; the
  old default `fb_seq` predates the UNSORTED check); `test/threads.sh` 2,128 identical;
  `-m` with every `--threads` (`thr_m.sh`) 1,092 identical; `test/out.sh` OK (in a fresh
  directory: the old one had a stale cache); `test/index.sh` ALL PASS, with new `-m` cases
  (`-m` with `-W` on chr22, the scrambled file and the edge cases).

**Timings** (`bench/m2.sh`, under the bench lock, `taskset -c 0-15`, three rounds):

| run | framebender | bcftools |
|---|---|---|
| cohort, `-m -any` | 1.76-1.81 s, 349 MB | 1.31-1.46 s |
| joined `sub.vcf`, `-m -any` | 1.23-1.29 s | 3.46-3.63 s |
| HG002 chr22, `-m -any` | 0.08 s | 0.12-0.13 s |
| HG002 whole genome, `-m -any` | 2.43-2.48 s | 8.09-8.15 s |
| HG002 whole genome, no `-m` (main: 1.74-1.79 s) | 1.78-1.84 s | |
| joined, no `-m` (main: 0.27-0.28 s) | 0.29-0.30 s | |

Milestone 1's build took 1.77-1.84 s and 488-491 MB on the cohort; the reserve change brings
the memory to 349 MB at the same speed.

## Stage 2, milestone (1): the byte splitter and its proof

The approved plan (after the prototype timing below): the byte splitter is the main path and
the String path is the fallback for refusals and odd shapes. Milestone (1) is the byte
splitter and its proof that it equals `B.Rec.parts`. Milestone (2) is the machine
integration, the run laws and the split laws. The machine already calls the splitter
(`norm_seq.bend`, unproven), so the integration below can be timed.

### The byte splitter (`norm_split.bend`, module `NS`)

`NS.split(b, s, lf, over0, defs)` takes the line at `s` with its LF at `lf`. It returns the
buffer back, together with either the records' bytes (`Some`) or `None`. A `None` means the
String path decides, and it calls `B.Rec.parts` itself.
- **The checks.** One pass cuts the body at tabs (`cut`, lawful-fields' `cut` structure
  with a faster find). The line is split only if:
  - it has eight fields or more, CHROM is not empty, POS is digits (`FC.digits`) and REF is
    letters (`letters`), so it is not MALFORMED;
  - it has two or more ALTs, none empty, no two equal up to case (`distinct`).
  Anything else is `None`.
- **What it reads once per line.** Each INFO entry's and each FORMAT key's `Number`
  (`ikinds`, `fkinds`, using `B.Tags.find` on the key's text).
- **What it writes.** One record per ALT, written from the line's bytes into a buffer of
  their own:
  - CHROM to REF, that ALT, QUAL, FILTER;
  - INFO with each per-allele value cut (`B.Vals.split`);
  - FORMAT;
  - each sample with its genotype rewritten (`B.Gt.split`) and its per-allele values cut;
  - the line's terminator (LF, or CR LF).
  A refusal (`B.Refuse`: an undefined tag, a bad count, a bad genotype) clears the flag, and
  the answer is `None`.
- **Size.** 1,064 lines.

Changes made while proving (none changes the output; the harness below checks this):
- INFO's lone `.`: the special case was removed. A `.` INFO is cut at `;` like any other, and
  gives one entry, as `B.Info.split` reads it.
- REF uses `letters` only (the old `every` loop was removed); POS uses `FC.digits`; numbers in
  genotypes use `FC.num`. Each now has a lawful-fields law to stand on.
- `pick` guards its index (`j <= k`), so a value list shorter than the count can never be read
  past its end.
- `cut` is lawful-fields' `cut` structure (`cut.next`, `cut.go`, `cut.ends`, then `rgs`), with
  the fast find kept. `count` and `nth` keep their own find loops.
- The cost of these changes on the cohort, single-threaded: about +5% (v4 5.4-5.6 s, v8
  5.7-6.0 s; 16 threads: 1.7 s against 1.85 s). Two variants were rejected:
  - `FC.cut` directly: about 11% slower.
  - `count` and `nth` through `cut.ends`: 10 s.

### The proof

The top theorem, `proof_s_drv.bend`'s `split_t`:
- **Assumptions.**
  - The buffer is `C.BT(len, t)` with `D.ok`.
  - `s <= lf < len`, and the byte at `lf` is 10 (LF).
  - `bd` is 2^32. It is kept abstract (`hbd`), so the checker never evaluates
    `Nat.pow(2n, 32n)`.
- **Conclusion.** `NS.split(C.BT(len, t), s, lf, o0, defs)` gives one of two answers:
  - `Out{C.BT(len, t), None}`: the line comes back unchanged; or
  - `Out{C.BT(len, t), Some{C.BT(l2, t2)}}` with `D.ok`, and some `ps` such that both hold:
    - `B.Rec.parts(defs, Opts{s, w, True, o0, args}, Line.body(L)) == Pieces{ps}`, where `L`
      is `B.Text.line` of the bytes `s .. lf-1`;
    - the text of the new buffer is `Norm.recs_text(ps, Line.term(L))`: each piece followed by
      the line's terminator, which is what the machine reads next.
- **Not covered here.** The proof does not claim the splitter takes every line that
  `B.Rec.parts` splits. A `None` is always allowed, and the String path then gives
  `B.Rec.parts`' answer. The harness below measures how often that happens: on every input
  tried, never.

Modules (18 files, 6,800 lines; all check with `test/bcheck.sh`; `--verdict` passes on
`proof_s_drv.bend`, which imports all of them):

| module | what it proves |
|---|---|
| `proof_s_w`, `proof_s_wt`, `proof_s_ws` | the writer: a model (`Wm`) the buffer mirrors, the text its writes stand for, and a step relation `WS` that composes |
| `proof_s_top` | the writes' start (an empty buffer) and end (the last flush, `out.of`) |
| `proof_s_cut`, `proof_s_scan` | `cut` is lawful-fields' `cut`: its ranges' text is `String.split`; `count`, `nth` |
| `proof_s_read`, `proof_s_dup` | text reads; `letters` is `Text.is_letters`; `distinct` is `Alts.distinct` |
| `proof_s_kinds` | the INFO and FORMAT kinds (`Number` lookups) |
| `proof_s_vals`, `proof_s_gtspec`, `proof_s_tok`, `proof_s_gt` | per-allele values (`Vals.split`); genotypes (`Gt.split`) |
| `proof_s_info`, `proof_s_fmt` | INFO (`Info.split`), FORMAT and one sample (`Fmt.split`) |
| `proof_s_rec` | one record is `Rec.piece` with the terminator; all records; `Parts.of` (generated by `data/tmp/split/tools/genrec.py`) |
| `proof_s_line` | `Text.line`'s body and terminator as byte ranges; `Rec.parts` of a line that passes the checks (`parts_eq`) |
| `proof_s_drv` | the driver (`go.*`) and `split_t` (generated by `data/tmp/split/tools/gendrv.py`) |

Notes for the next proofs:
- A def with `Nat.pow(2n, 32n)` in its context crashes the checker's error printer. The driver
  carries the bound wrapped (`type BW`), and only one small def (`recs`) unwraps it.
- `case _` after a nested list pattern does not split the fallback far enough. The driver
  matches one field at a time (`gf .. gf7`).

### Checks

- **Differential harness** (`data/tmp/split/diff`): `NS.split` against `B.Rec.parts`, both
  compiled, on every line of 10 inputs (toy cases, 20 cohort lines, 40 joined lines, 7
  fuzz files) with both `--multi-overlaps` settings: 0 differences in 20 runs. Not one line
  that `B.Rec.parts` splits was left to the String path.
- **Spec against machine** (`specrun/vs.sh`: `L.run` compiled, against `fb_split`): 28 fuzz
  files with 5 option sets each, 140 of 140 the same (stdout, stderr, exit code).
- **bcftools 1.24** (`cmp_m.sh`, `-c w -m -any`):
  - cohort: 3,341 records each, 0 differing;
  - HG002 chr22: 50,861 records each, 0 differing;
  - joined: 57,534 records each, 12 differing. All 12 are symbolic SVs (`<DEL>`, `<DUP>`,
    `<DEL:ME>`) that bcftools realigns and framebender passes through (README,
    docs/LAWS.md). Main's build without `-m` differs on the same records in the same way.
- **Without `-m`** (`reg/same.sh`, against main's build at 36990fc, `fb_base`): 126 of 126
  runs identical (stdout, stderr, exit code). The script's old default reference,
  `data/tmp/fb_ref`, is an older build (Oct 28). It writes no records before an
  `UNKNOWN_CHROM` stop where main, the spec and this build write 49
  (`e2_chromchange`). The default now points at `fb_base`.

### Timing of the unproven integration

`bench/integ.sh` (via `bench/m1.sh`), under `flock data/tmp/bench.lock`, `nice -n 19`,
`taskset -c 0-15`, default threads. Three rounds, interleaved, one run at a time, each
output deleted after its run (`bench/m1.out` has the raw lines). `fb_split` is this branch's
build: the proven splitter, with the machine integration not yet proven.

| run | rounds 1-3 | peak RSS |
|---|---|---|
| `fb_split norm -c w -m -any` cohort.vcf | 1.86, 1.81, 1.78 s | 485-488 MB |
| bcftools `norm -c w -m -any` cohort.vcf | 1.33, 1.39, 1.29 s | 15 MB |
| `fb_split norm -c w -m -any` joined.vcf | 1.20, 1.25, 1.19 s | 258-264 MB |
| bcftools `norm -c w -m -any` joined.vcf | 3.64, 3.76, 3.65 s | 15 MB |
| `fb_split norm -c w -m -any` HG002 chr22 | 0.08, 0.09, 0.07 s | 129-133 MB |
| bcftools `norm -c w -m -any` HG002 chr22 | 0.13, 0.12, 0.13 s | 15 MB |
| `fb_split norm -c w` joined.vcf (no `-m`) | 0.28, 0.29, 0.28 s | 226-228 MB |
| `fb_base` (main) `norm -c w` joined.vcf | 0.27, 0.29, 0.28 s | 225-227 MB |

- **Cohort** (every line multiallelic, 3,202 samples with PL): 1.8 s against bcftools'
  1.3 s, 1.4 times its time. The String prototype took 387 s. Single-threaded, the splitter
  build takes 5.7-6.0 s (v8 timing above).
- **Joined `sub.vcf`** (4% multiallelic, GT only): 1.2 s against 3.7 s, 3 times faster than
  bcftools.
- **HG002 chr22**: 0.08 s against 0.13 s.
- **Without `-m`**: no change against main.
- **Memory**: 486 MB on the cohort, against 252 MB for main on the already split file. The
  records' buffers are held as pieces; milestone (2) will look at this with the growth noted
  below.

### Why the prototype's time per line grew with the file

The String prototype took 4.85 s per 100 lines on 100 cohort lines but 26 s per 100 lines on
1,500. Findings:
- **Not the threads, not the heap patch.** On 100, 300 and 600 lines: 5.0, 19.9 and 70.8 s,
  the same with one thread (4.9, 19.6, 70.7 s) and the same with the heap patch built in.
- **Not the content.** The same 100 lines repeated 3 and 6 times: 4.9, 19.9 and 73.4 s.
  Decoding and writing back alone (`copy`) stays linear: 0.84, 2.45 and 4.99 s.
- **The work is linear; each step gets slower.** gprof on 100 and 300 lines
  (`bench/pg100`, `bench/pg300`): every call count grows 2.9 times, as the lines do. The
  cost per call grows too: `String.append` 2.6 times, `rfc_wrap` 1.5, `span_fade` 1.4,
  `term_drop` 1.2. The runtime's freeing (`term_drop`, `span_fade`, `rfc_wrap`) is 74% of
  the time at 100 lines. The String split's churn of small terms scatters the heap, and
  every access slows as the file goes on.
- **The code that stays does not show it.** The machine (`fb_base`, main's build) on lines
  that take its String path, 1, 3 and 6 times over, is linear:
  - out of scope (`<DEL>`): 0.24, 0.43, 0.68 s;
  - REF mismatches: 0.54, 1.54, 3.02 s.
  Its reader, window and String path keep a constant time per line at these sizes. The
  byte splitter builds no Strings.
- **One thing to watch.** The machine's peak memory grows with the file on these inputs:
  102, 185, 335 MB (`<DEL>`) and 120, 196, 360 MB (mismatches), for 15, 45 and 91 MB of
  output. It is not a time problem here. I will check it in milestone (2), where the split
  records are fed back as pieces.

## Step 3: prototype timing (decisions 14, 19)

The laws were accepted after round 3. The approved spec (the round-3 draft) is installed in
`types.bend`, `run.bend` and `LAWS.bend`; the machine and the proofs do not build against it
yet. Before any machine proof, an unproven prototype of the String split path was timed.

**Prototype.** Everything is in `data/tmp/split/proto/`, built with `bend -o` and clang, with
no heap patch.
- `proto.bend` reads a VCF with `File.read` (4 MiB Strings), keeps the header's `Defs`,
  splits every body line with two or more ALTs, and writes the records.
- Three modes:
  - `spec`: `B.Rec.parts` as written.
  - `fast`: `fast.bend`'s `F.parts`. It looks up each INFO tag's and FORMAT key's Number once
    per line, splits each sample column once, and uses `match` instead of `Bool.pick`. The
    spec's `Bool.pick` evaluates both branches strictly, so `B.Rec.piece.field` runs
    `Info.split` and `Fmt.split` on every field.
  - `copy`: decode to String and write back, with no split. This is the floor of any String
    path.
- `spec` and `fast` write byte-identical output on every file, and the same records as
  `bcftools norm -m -any` (without `-f`) on 20 cohort lines and 40 joined lines.

**Inputs** (`data/tmp/split/gen/`):
- `cohort.vcf`: `cohort.py`, seed 7. 1,500 lines, all multiallelic: 2 or 3 ALTs, SNPs and
  insertions. 3,202 phased samples, GT:AD:DP:GQ:PL. About 140 KB per line, 218 MB.
- `joined.vcf`: `bcftools norm -m +any data/kg/sub.vcf`. 57,534 -> 55,310 lines, 2,224
  multiallelic, 766 MB, GT only.
- `joined_multi.vcf`: the header and the 2,224 multiallelic lines, 32 MB.
- `cohort_split.vcf`, `joined_split.vcf`: the two files split by bcftools without `-f`. These
  are the records the machine sees after splitting.

**Method.** `bench/full.sh`, under `flock data/tmp/bench.lock`, `nice -n 19`,
`taskset -c 0-15`. Two rounds, interleaved, one run at a time, output to a file deleted after
each run. `bench/full.txt` holds the raw lines.

| run | round 1 | round 2 | peak RSS |
|---|---|---|---|
| bcftools `norm -c w -m -any -f` cohort.vcf | 1.35 s | 1.30 s | 15 MB |
| proto `fast` cohort.vcf | 386.2 s | 387.8 s | 267 MB |
| proto `spec` cohort.vcf | 393.7 s | 389.0 s | 262 MB |
| proto `copy` cohort.vcf (no split) | 12.4 s | 12.1 s | 226 MB |
| fb_base (main, 36990fc) `norm -c w -f` cohort_split.vcf | 0.25 s | 0.24 s | 252 MB |
| bcftools `norm -c w -m -any -f` joined.vcf | 3.48 s | 3.64 s | 15 MB |
| proto `fast` joined_multi.vcf | 20.9 s | 21.1 s | 330 MB |
| proto `spec` joined_multi.vcf | 67.6 s | 70.4 s | 326 MB |
| proto `copy` joined_multi.vcf (no split) | 1.66 s | 1.73 s | 215 MB |
| fb_base `norm -c w -f` joined_split.vcf | 0.37 s | 0.31 s | 268 MB |

**Stage 1 (String path) estimates.** The split lines' cost on the String path, plus the
machine on the split records:

| file | bcftools | String path (`fast`) | String path (`spec`) |
|---|---|---|---|
| cohort | 1.3 s | about 387 s (290x) | about 390 s |
| joined `sub.vcf` | 3.5 s | about 21 s (6x) | about 70 s (20x) |

**Findings.**
- Even with no split at all, decoding a line to a String and writing it back runs at about
  18 MB/s. That is 9 times bcftools' time on the cohort, before any work.
- Splitting on Strings costs 12 to 30 times the copy floor.
- Once-per-line lookup helps where the header has many tags (joined: 100 INFO definitions,
  3.3x faster), and not at all on the cohort.
- On the cohort, the time per line grows with the file: the 100-line probe ran at 4.85 s per
  100 lines, against 26 s per 100 lines over 1,500 lines. I did not chase this (the prototype
  has no heap patch, `notes/memory.md`): the conclusion holds at either rate.
- On already split records, the machine is far faster than bcftools: 0.25 s against 1.3 s on
  the cohort, 0.3 s against 3.5 s on joined. Its byte path is not the problem.

**Recommendation: stage 2 is required.**
- A String split path cannot come near bcftools on cohort data (more than 100 times slower).
  It is 6-20 times slower even on a GT-only cohort with 4% multiallelic lines.
- The split has to run on packed bytes, as `norm_fix.bend` rewrites records. A byte splitter
  writes the records for each ALT into a new buffer; the machine handles that buffer as a
  piece of lines, with the line number held for its records; the existing fast path and
  rewriter then normalize them at byte speed.
- The String path stays as the fallback for lines the byte splitter does not take: refusals,
  undefined tags, odd shapes.
- With the machine's speed above, framebender should then be at least as fast as bcftools.

This changes the plan's order and size. Stage 1's String path for every split line is not
worth proving as the main path. The work becomes:
- the byte splitter and its refinement proof against `B.Rec.parts`, about phase C's size
  (12,000-16,000 lines);
- the machine (pieces fed back as lines, the held line number, `Defs` in the state, the
  parallel tasks);
- the run laws;
- the 19 split laws on the spec.

That is about 20,000-27,000 lines of proofs in all, against the 7,000-11,000 planned.

## Round 3 changes

Round 2 review: `reviews/responses-split-law.md`, "Round 2" (decisions 17-23) and
`*-split-law-r2.md`. No blockers. Per item:

17. **GT `.` and G values.** `B.Gt.ploidy` is now `B.Gt.copies`.
    - A GT names one copy per allele, one plus its separators: `1` and `.` are one copy, `./.`
      is two.
    - No GT value: two copies only.
    - A lone `.` (many tools write it for any no-call) accepts either count, n+1 (one copy) or
      (n+1)(n+2)/2 (two). `B.Vals.copies` picks the one the count says; the two never coincide
      for n >= 2.
    - Examples: `pl_dotgt` (`.` with 6 values: two copies), `pl_dot_hap` (`.:7,8,9` ->
      `.:7,8` / `.:7,9`, as bcftools), `pl_dot_bad` (4 values: BAD_COUNT), and `hap_dot_over`
      (`2:7,8,9` under `--multi-overlaps .` -> `.:7,8` and `1:7,9`, which reads as one copy
      again).
18. **`split_change` on records written.** The law is now per record: for record i+1 whose
    outcome does not stop the run, its text as written (`written`, the item's text in
    `out_items`), read back, makes exactly ALT i+1's change. The pairing with ALTs is stated on
    its own; the output order is `sorted`'s. Examples `split_change1`, `split_change2`,
    `written_moves`.
19. **Prototype timing** (plan, step 2): the spec as written against a version that looks up
    each FORMAT key's Number once per line and splits each column once. If the second is kept,
    it comes with a small proof that it gives the same records.
20. **ALT_DUP with `-m`.**
    - The wording now says that for `A <*>,<*>` or `A *,*` `judge` gives Skipped, so `-m` refuses
      a line that passes without `-m`. The refusal stays.
    - The split's refusal is the new code `DupAlts`, written ALT_DUP with "not split" at the end.
      `judge`'s own ALT_DUP is unchanged.
    - Examples `dup_sym`, `run_dup_sym_w`, `render_dup`; `run_dup_e` still stops with the
      plain ALT_DUP (the whole line's outcome comes first).
21. **New law `whole_malformed`**: a MALFORMED line is `Whole` under `-m` (example `mal`).
22. **Documented** ("Where framebender differs"): under `-c w`, a line that cannot be split and
    whose whole-line problem does not stop the run (REF_MISMATCH, BAD_END) reports only the
    split's code. Example `run_unsplit_mismatch_w`.
23. **`split_format_values`'s wording**: one copy gives REF's and ALT's values; two copies or no
    GT value give the three genotype values; a lone `.` GT goes by its count. More than two
    copies is refused, not split.

Also: decision 4 is amended to match the experiment, so spaces are trimmed and tabs are not
(all three reviewers). `split_when` keeps the exact code (all three).

## Round 2 changes

Round 1 review: `reviews/responses-split-law.md` (decisions 1-16) and `claude-`, `gpt-`,
`grok-split-law.md`. Per item:

1. **`sample_value` gave `Some ""` for a missing column.** The FORMAT laws now read samples
   with `sample_column` / `sample_at` (`List.get` on the fields): `None` when the line has no
   such column. Example `ex_order` and every FORMAT law use them.
2. **Which lines split.** New law `split_when`: with `-m`, a line that is not MALFORMED and has
   two or more ALTs is `Pieces` exactly when `split_problem(defs, body)` is `None`, and
   `Unsplit{c}` with `c` exactly `split_problem`'s code otherwise. `split_problem` is written in
   LAWS.bend as a list of checks read left to right (ALT_DUP; each INFO entry; each sample's
   values), with the named `B.Vals.expected_count(num, n, ploidy)`, not `Vals.idx`. 41 examples
   check it against `B.Rec.parts`, one per case.
3. **Lone `.`, exact counts, every occurrence, exact GT text.**
   - The lone `.` is in the laws: `split_info_kept` and `split_format_kept` copy a value `.`.
   - An A/R/G value must have exactly `expected_count` values (`split_when`; `IA=1,2,9` is
     BAD_COUNT, example `c_ia3`). The values laws give exactly `lifted`'s list.
   - INFO laws quantify over entry positions (`List.get(info_entries(body), e)`), FORMAT laws
     over key positions, so every occurrence is covered, duplicates included.
   - `split_gt` now requires the written GT to be well written (`gt_view`: each allele `.` or
     digits without leading zeros), so with `split_phase` the text is fixed exactly. The input's
     alleles must be the same (`01/2`, `+1/2` are BAD_GT).
4. **Header values trimmed.** `Hdr.trim` drops spaces around each piece's key and value and
   around the definition. Experiment (row 33): htslib reads `ID=IA, Number=A`, `Number=A ,`,
   `ID=IC ,` and `Number= A` as Number A. It does **not** trim tabs: `Number=A\t,` reads as "no
   Number", and a tab after a comma makes the line unreadable. So framebender trims spaces only,
   as htslib does; a tab leaves the Number unread, which is now UNDEFINED_TAG (item 9). One case
   where framebender is more lenient: a space before the closing `>` makes htslib drop the line;
   framebender reads it.
5. **Ploidy from GT.** `B.Gt.ploidy`: the number of alleles in the sample's GT; 2 when the
   sample has no GT value or it is `.` (round 3: `.` changed, item 17). `B.Vals.expected_count(G, n, p)`: n+1 for one copy,
   (n+1)(n+2)/2 for two, none above two (BAD_COUNT: a scope limit, documented). INFO G stays
   diploid only. Examples `pl_nogt`, `pl_dotgt`, `pl_gtafter` (GT after PL in FORMAT),
   `c_pl_dip3`, `c_pl_hap6`, `c_pl_trip`.
6. **`split_valid` and `split_change` on the text.** Each is now about the records of a split
   line. `split_valid`: if the line is a valid variant, every record is. `split_normalized`:
   if `judge` would normalize the whole line, it normalizes every record. `split_change`: the
   records as written, read back from their text, together make the line's change, in ALT
   order. The `B.Var`-only versions are gone.
7. **Unsplit after the stopping outcomes.** `unsplit_in`: on `Unsplit{c}`, if `judge`'s outcome
   for the whole line stops the run (MALFORMED, UNKNOWN_CHROM, a problem under `-c e`), that
   outcome comes first; otherwise `c`. Example `run_unknown_w`: an unknown CHROM with an
   undefined tag stops with UNKNOWN_CHROM under `-c w`.
8. **Duplicate ALTs.** `B.Rec.parts` refuses two ALTs equal ignoring case with `ALT_DUP`. For
   letter ALTs, by item 7, that is also what `judge` gives the whole line; for symbolic ones it
   is not (round 3, item 20). An ALT equal to REF still splits,
   and its record is ALT_DUP. Examples `dup`, `dup_case`, `altref`, `run_dup_e`.
9. **Missing or unread Number.** `B.Num` gains `NumUnknown`: no Number, or anything but A, R, G,
   `.`, `P` or a count (so VCF 4.4's LA, LR, LG, row 33). A tag with an unread Number, with a
   value, in a line to split, is UNDEFINED_TAG. Examples `u_tab`, `u_nonum`, `u_lr`.
10. **UNDEFINED_TAG kept.** An INFO entry without a value (a flag) is copied whatever its
    definition (example `u_flag`), unless its tag is A, R or G (BAD_COUNT). `UndefinedTag` now
    carries the tag, and the message names it and the fix:
    `UNDEFINED_TAG <TAB> c1 <TAB> 25 <TAB> line 28 <TAB> INFO/XX has no usable header line (add one,
    e.g. with bcftools annotate -h); not split` (`B.Code.detail`; BAD_COUNT and BAD_GT add
    `not split`; every other message is unchanged, example `render_old`). The VCF reserved-key
    table (AC, AF: A; AD: R; PL: G) is not used: noted under "Later".
11. **Empty INFO entries** (`;;`, a trailing or leading `;`) are kept as they are in every
    record (examples `empty1`, `empty2`). bcftools drops them (row 34).
12. **Old statements kept visibly.**
    - `items(fasta, vcf)` keeps its old definition, word for word. The new one is
      `out_items(fasta, vcf, o)`, which `sorted`, `grouped_in` and `no_unsorted` read.
    - New law `items_without_m`: without `-m`, `out_items(fasta, vcf, o) == items(fasta, vcf)`.
    - New law `biallelic_run`: on a file whose body lines have fewer than two ALTs,
      `run(fasta, vcf, o) == run(fasta, vcf, no_m(o))`. `no_m` keeps the recorded arguments, so
      the header's command line is the only difference in practice.
13. **END.** `split_info_kept`'s statement says the split copies the entry, and `judge` then
    rewrites END by the existing END rule.
14. **Speed.**
    - `Got.join` now builds from the right, so each text is copied once (linear).
    - The plan has an unproven prototype of the split path, timed before any machine proof, on
      a heavy synthetic cohort (GT:AD:DP:GQ:PL, 3,202 samples, dense multiallelic lines) and on
      the joined `sub.vcf`, against `bcftools norm -m -any`. The stage-2 decision is made then.
    - That timing comes after round 2, not in this round.
15. **Parallel tasks** get the header's `Defs`, parsed once, in their fresh state (plan).
16. **Minor.**
    - `usage()` shows `-m -any|-both|-`.
    - The `Summary` and `Cnt` comments say "records", not "body lines".
    - The window paragraph says what UNSORTED depends on.
    - The phase loss no longer overstates (PS and order are kept).
    - Rows 10 and 23 are corrected.
    - New rows: GT without a header line (bcftools drops it; framebender keeps it), the VCF 4.4
      leading phase mark (htslib refuses it: a VCF parse error), allele numbers with leading
      zeros, empty INFO entries.
    - The docs plan lists polyploid G, the summary's counts, one REF_MISMATCH warning per
      record, and a worked PL example for n = 2.

## Summary

- **What bcftools 1.24 does** (`norm -m -any -f ref.fa`):
  - Each record with two or more ALTs becomes one record per ALT, in ALT order, *before*
    normalization.
  - Each new record is then normalized on its own and goes into the same sorting buffer as
    every other record (sorted by POS, equal POS in arrival order).
  - Genotypes are rewritten with one rule (below).
  - INFO and FORMAT values are cut by the header's `Number` (A, R, G); everything else is copied.
  - Where the input doesn't fit that scheme, bcftools stops on some cases, guesses on others,
    silently drops data on some, and crashes on a few (rows 10, 16-20, 23).
- **Proposal**:
  - Accept `-m -any`, `-m -both`, `-m -` (all three split every multiallelic record), the glued
    `-m-any`, `-m-both`, `-m-`, and `--multi-overlaps 0|.` (default `0`).
  - Joining (`-m +...`), `-m -snps`, `-m -indels` and `--keep-sum` are usage errors for now.
  - Splitting is defined on the text of a line, before `judge`. Each record is then judged as a
    line is today, so every existing law about one record applies to each.
  - Where bcftools guesses, drops or crashes, or where a record would not read back as written,
    framebender refuses the line instead:
    `UNDEFINED_TAG`, `BAD_COUNT`, `BAD_GT` (new), or `ALT_DUP`. These stop the run under
    `-c e`; under `-c w` the line passes through unsplit with a warning, unless the whole line
    stops the run anyway (UNKNOWN_CHROM).
- **The laws**: 19 new laws.
  - `split_when` fixes exactly which lines split and which are refused, with which code.
  - The others say what each record of a split line holds: one ALT each; the same site; the
    genotype rule; the values of its alleles; everything else copied.
  - Two laws link to the normal form: `split_normalized`, and `split_change`, which pairs each
    record written with its ALT.
  - Old statements stay visible: `items_without_m`, `biallelic_run`, `whole_malformed`.
  - `run` absorbs the change, so `law machine`, `threads` and `output` keep their statements.
- **Draft**: type-checks; 107 examples evaluate. They give bcftools' records on every case where
  the design agrees with bcftools, including a whole run (split, normalize, sort).
- **Size**: large. Stage 1 is 6,000-10,000 lines of proofs, most of them mechanical. A
  prototype timing comes first and decides on stage 2 (a bytes path).

## Terms

For a reader who is not a geneticist.

- **Allele**: one version of the DNA at a place. REF is the reference genome's version; each ALT
  is an alternative seen in the samples. Alleles are numbered 0 (REF), 1 (the first ALT), 2,
  ... ALT numbers count from 1.
- **Multiallelic record**: a record with two or more ALTs at one place, such as REF `C`,
  ALT `G,T`. Splitting writes it as two **biallelic** records: `C G` and `C T`.
- **Sample**: one individual. The 1000 Genomes panel has 3,202 sample columns.
- **Ploidy**: how many copies of a chromosome an individual has: two (**diploid**, most human
  chromosomes), one (**haploid**: X in males, Y, mitochondria), sometimes more (**polyploid**,
  in plants and some tumours).
- **Genotype** (FORMAT/GT): which allele each copy carries, written as allele numbers separated
  by `/` or `|`, one per copy. `0/1`: one copy REF, one copy ALT 1. `1/2`: one copy ALT 1, the
  other ALT 2. `2`: a haploid sample with ALT 2. `.`: a copy whose allele is unknown, so `./.`
  is a diploid no-call. Many tools write a lone `.` for a no-call of any ploidy.
- **Phased** (`|`): the order means something. `1|2` puts ALT 1 on one parental copy and ALT 2
  on the other, consistently with every phased genotype of the sample in the same phase set
  (FORMAT/PS). `/` says nothing about which copy is which.
- **INFO**: facts about the site, such as `AF=0.1,0.2` (frequency of each ALT). **FORMAT**:
  facts per sample, such as `AD=10,3,5` (reads for REF, ALT 1, ALT 2) or `PL` (how unlikely each
  possible genotype is).
- **Number** (in the header line defining a tag, `##INFO=<ID=AF,Number=A,...>`): how many
  values the tag has.
  - `A`: one per ALT.
  - `R`: one per allele, REF first.
  - `G`: one per possible genotype. For a diploid sample the order is 0/0, 0/1, 1/1, 0/2, 1/2,
    2/2, ...: genotype j/k (j <= k) is value number k(k+1)/2 + j, counting from 0. A haploid
    sample has one per allele.
  - A count: that many values. `.`: any number. `P`: one per copy.

  A, R and G say which values belong to which ALT, so they are what splitting needs.

Worked example (for docs/LAWS.md): REF `C`, ALTs `G,T` (n = 2), a diploid sample with
`PL=10,20,30,40,50,60`, the genotypes 0/0, 0/1, 1/1, 0/2, 1/2, 2/2 in that order.

- The record for ALT 1 (`C G`) keeps values 1, 2, 3, counting from 1: `10,20,30`. These are
  0/0, 0/1, 1/1.
- The record for ALT 2 (`C T`) keeps values 1, 4, 6: `10,40,60`. These are 0/0, 0/2, 2/2,
  which become that record's 0/0, 0/1, 1/1.
- A haploid sample (`GT=2`, `PL=7,8,9`, one value per allele) keeps REF's and the ALT's: `7,8`
  for ALT 1, `7,9` for ALT 2.

## Step 1: what bcftools 1.24 does

### Setup

`data/tmp/split/` holds:

- `ref.fa`: two contigs. `c1` = `ACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA`
  has a CA repeat at 9-16.
- `hdr.txt`: defines INFO `IA`/`FA`/`SA` (Number A: Integer, Float, String), `IR`/`SR` (R),
  `IG`/`SG` (G), `I1` (1), `I2` (2), `ID_` (.), `S1` (1, String), `FL` (Flag), `END`, and FORMAT
  `GT`, `AD` (R), `PL` (G), `FA`/`SA` (A), `SR` (R), `SG` (G), `DP` (1), `F2` (2).
- `run.sh CASE OPTS`: puts `hdr.txt` before `cases/CASE.body`, runs
  `bcftools norm --no-version OPTS -f ref.fa`, and prints the body, stderr and exit code.

Rows 33-35 use small files in `out/` with their own headers. I read `vcfnorm.c` of 1.24 to
choose the cases; every claim below is from a run.

### Findings

| # | case | what bcftools 1.24 does | command |
|---|---|---|---|
| 1 | order | Split first, one record per ALT in ALT order; then each is normalized on its own; then sorted by POS, stably. `12 ACA A,ACACA` gives `8 TCA T` and `8 T TCA`. `15 CAG CTG,C` gives `15 CAG C` then `16 A T`: ALT 1 trims to `16 A T`, so POS order puts ALT 2's record first. | `run.sh basic -m -any` |
| 2 | equal POS | Arrival order; a split line's records in ALT order (`8 T TCA` from an earlier line, then `8 TCA T`, `8 T TCA`). `-S lex` orders equal POS by REF+ALT. | `run.sh same -m -any` (`-S lex`) |
| 3 | without -m | Normalized as one variant, ALTs in order (`8 TCA T,TCACA`, GT `1/2`), as framebender does today. | `run.sh basic` |
| 4 | one ALT | Untouched by `-m` (`25 C G`). | `run.sh basic -m -any` |
| 5 | -m forms | `-m -any`, `-m -both`, `-m -`, `-m-any`, `--multiallelics -any` all split every multiallelic record. `-m -xyz`: "The argument to -m not recognised", exit 255. | `run.sh types -m -any` (etc.) |
| 6 | -snps, -indels | Split only if an ALT is a SNP (an indel) by htslib's classification. `GC AT,CC` splits under `-snps` (`CC` is a SNP of `GC`); `AG TC,A` does not. Under `-indels`, `CT GA,GAA` does not: htslib calls `CT`->`GAA` "other". | `run.sh types -m -snps`, `-m -indels` |
| 7 | joining (+) | `-m +any` merges records at the same POS. On row 1's output it rejoins the two `8` records and the three `21` records, not `15`/`16`, which normalization moved apart. | `bcftools norm -m +any out/basic_split.vcf` |
| 8 | -w | Split records share the window. With `-w 1`, `9 C G` is written before the split line's `8` records: unsorted output, no message. | `run.sh win -m -any -w 1` |
| 9 | GT | In the record for ALT i: allele `i` becomes `1`, `0` stays `0`, `.` stays `.`, another ALT becomes `0` (`--multi-overlaps 0`, the default) or `.` (`--multi-overlaps .`); separators and ploidy kept. Table below. | `run.sh gt -m -any` (`--multi-overlaps .`) |
| 10 | GT, allele above n | `1/4` with 2 ALTs: `1/0`, `0/0` (`1/.`, `./.` under `--multi-overlaps .`). Allele 4 is read as "another ALT". Without `-m`, `1/4` is written as it came, with no message. | `bcftools norm -m -any out/g.vcf` (from the `1/4` loop) |
| 11 | GT position | Split records have GT moved first (`AD:GT` -> `GT:AD`); without `-m` the order is kept. | `run.sh gt2 -m -any`, `run.sh gt2` |
| 12 | INFO A, R, G | `IA=1,2` -> `1` / `2`; `IR=10,11,12` -> `10,11` / `10,12`; `IG=0,1,2,3,4,5` -> `0,1,2` / `0,3,5`; strings likewise. Missing values inside a list are kept (`IA=1,.,3`, `IR=.,1,2,3`). | `run.sh info2 -m -any` |
| 13 | INFO other | Fixed numbers, `.` and flags are copied whole, whatever their count (`I1=1,2`, `I2=1`, `ID_=1,2,3,4`). `FL=1` is written `FL`. | `run.sh info2 -m -any`, `run.sh n_I2=1 -m -any` |
| 14 | numbers re-printed | Every Integer and Float is re-printed, with or without `-m`: `0.10` -> `0.1`, `2.5e-3` -> `0.0025`, `1e10` -> `1e+10`. | `run.sh info` |
| 15 | INFO lone `.` | String A/R/G `.` gives `.` in every record. | `run.sh n_SA=. -m -any` |
| 16 | INFO wrong count, numeric | Stops: "wrong number of fields in INFO/IA ... Use --force", exit 255, nothing written. This includes the lone `IA=.`, `FA=.`, `IR=.`, `IG=.`. | `run.sh n_IA=. -m -any` (`IA=1`, `IA=1,2,3`, ...) |
| 17 | INFO wrong count, String | No error: `SA=x` -> `x` / `.`; `SR=a,b` -> `a,b` / `.`; `SG=a,b,c` -> `a,b,c` / `.`; `SR=a,b,c,d` -> `a,b` / `a,c`. | `run.sh n_SA=x -m -any` (etc.) |
| 18 | INFO not in the header | Warning, then the entry is **dropped** from every record (`XX=1,2`; `AC=3,4;AF=0.1,0.2;AN=8`). Exit 0. | `run.sh undef1 -m -any`, `run.sh mis -m -any -c w` |
| 19 | key without a value | An undefined key alone (`XY`), or a defined non-flag written as a flag (`S1`, `IA`, `SA`, `I1`, `ID_`): **aborts** (`Assertion 'ret>0' failed`, core dump, exit 134). | `run.sh undef2 -m -any`, `run.sh n_IA -m -any` |
| 20 | header definitions | The first definition counts; the second line is dropped from the output header. Number after a quoted Description with commas is read. `Number=P` reads as `.`, copied. A record with the same INFO key twice keeps the first, drops the second. | `bcftools norm -m -any -f ref.fa out/hdr2.vcf` (`hdr3.vcf`), `out/raw_info.vcf` |
| 21 | FORMAT A, R, G | Per sample: `AD=1,2,3` -> `1,2` / `1,3`; `PL` with 6 values -> `0,1,2` / `0,3,5`; with 3 values (n+1) -> `7,8` / `7,9`; strings likewise; `DP`, `F2` copied. | `run.sh fmt -m -any` |
| 22 | FORMAT missing | A lone `.`: Integer/Float R becomes `.,.`; A, G and String stay `.`. Short sample columns are padded (`0/0` -> `0/0:.,.:.:.:.:.`), with or without `-m`. | `run.sh fmt -m -any` (samples 3, 5) |
| 23 | FORMAT wrong count | Numeric tags are checked against the largest count among the samples only. Every sample short: error. One sample short: filled (`AD 1,2` beside `3,4,5` -> `1,2` / `1,.`). Every sample with one value: copied **unsplit** (`AD=5` -> `5`, `5`). A sample's G with fewer values than another's is read as haploid (REF's and ALT i's): `PL=1,2,3,4` beside a 6-value PL gives `1,2` / `1,3`. A G count is never checked against the sample's GT: `GT=0/2`, `PL=7,8,9` gives diploid `0/0`, `0/1` with 2-value PLs. String A/R: `.`; String G: checked per sample. A FORMAT tag not in the header is **dropped**. | `run.sh f1 -m -any` ... `f18` |
| 24 | --keep-sum AD | REF's AD becomes REF's plus every other ALT's: `AD=1,2,3` -> `4,2` / `3,3`. | `run.sh fmt -m -any --keep-sum AD` |
| 25 | ID, QUAL, FILTER, END | Copied to every record. END is updated for a record normalization moves (`ACA A,<*>`, `END=14`: the `TCA T` record at 8 gets `END=10`). | `run.sh basic -m -any`, `run.sh sym -m -any -c w` |
| 26 | symbolic, `*`, `.`, breakend, IUPAC | Split like any ALT; the letter records normalized; `ACA *`, `<*>`, `<NON_REF>`, `A[c2:5[`, `.`, `R` written as they are, with none of the NON_ACGTN_ALT warnings bcftools gives the unsplit line. `<DEL>` realigned (a known difference). | `run.sh sym -m -any -c w` |
| 27 | duplicate ALT | `A C,C`: two records `A C` (`1/0`, `0/1`), no message. `A C,A`: a record `A A`, "Duplicate alleles" under `-c e`, one ALT_DUP warning under `-c w`. | `run.sh sym -m -any` (`-c w`) |
| 28 | REF mismatch | `-c e`: stops. `-c w`: one REF_MISMATCH warning per record, records unnormalized. `-c x`: all dropped. | `run.sh mis -m -any` (`-c w`, `-c x`) |
| 29 | case | Lower case kept (`a c,g` -> `a c`, `a g`). | `run.sh sym -m -any -c w` |
| 30 | no samples | Lines without FORMAT, or with no sample, split the same way. | `run.sh nogt -m -any` |
| 31 | stderr | `Lines total/split/joined/realigned/...: 4/3/0/3/...`. Total and split count input lines; realigned counts records changed. | any |
| 32 | real data | HG002 chr22: 577 multiallelic lines (all `1/2`, `2/1`; AD, ADALL Number=R) -> 50,861 records (from 50,284), 369 realigned. `data/kg/sub.vcf`: none (already split; 2,224 positions hold two or more records). | `bcftools norm -m -any -f data/chr22.fa data/hg002.chr22.vcf` |
| 33 | header spacing, Numbers | Spaces around keys and values are trimmed: `ID=IA, Number=A`, `Number=A ,`, `ID=IC ,`, `Number= A` all read as A. A space before the closing `>`: "Could not parse the header line", tag undefined. A tab after a comma: line unparseable. A tab before a comma (`Number=A\t,`): "no Number defined, assuming '.'". No Number, `Number=LR`, `Number=LG`, `Number=Q`: read as `.`, copied whole. | `bcftools norm -m -any out/trim1.vcf` (`trim2`, `local`) |
| 34 | empty INFO entries | Dropped: `IA=1,2;` -> `IA=1` / `IA=2`; `IA=1,2;;I1=4` -> `IA=1;I1=4`; `;IA=1,2` -> `IA=1`. | `bcftools norm -m -any out/empty.vcf` |
| 35 | GT forms | No `##FORMAT` line for GT: GT **dropped** from split records (`GT:AD` -> `AD`). A leading phase mark (VCF 4.4 `\|1\|2`, `/1/2`), a trailing or double separator (`1/2/`, `1//2`): "Couldn't read GT data", VCF parse error, with or without `-m`. Leading zeros and signs (`01/2`, `1/02`, `+1/2`): read as numbers, written `1/2`. | `bcftools norm -m -any out/nogtdef.vcf`, `out/g.vcf` loop |

Genotypes (row 9): `25 C G,T,A`. G is ALT 1, T is ALT 2, A is ALT 3. The last three columns
are under `--multi-overlaps .`.

| input | G | T | A | G (`.`) | T (`.`) | A (`.`) |
|---|---|---|---|---|---|---|
| `1/2` | `1/0` | `0/1` | `0/0` | `1/.` | `./1` | `./.` |
| `0/2` | `0/0` | `0/1` | `0/0` | `0/.` | `0/1` | `0/.` |
| `2/2` | `0/0` | `1/1` | `0/0` | `./.` | `1/1` | `./.` |
| `1\|2` | `1\|0` | `0\|1` | `0\|0` | `1\|.` | `.\|1` | `.\|.` |
| `2\|1` | `0\|1` | `1\|0` | `0\|0` | `.\|1` | `1\|.` | `.\|.` |
| `2` | `0` | `1` | `0` | `.` | `1` | `.` |
| `1` | `1` | `0` | `0` | `1` | `.` | `.` |
| `0` | `0` | `0` | `0` | `0` | `0` | `0` |
| `.` | `.` | `.` | `.` | `.` | `.` | `.` |
| `./.` | `./.` | `./.` | `./.` | `./.` | `./.` | `./.` |
| `.\|.` | `.\|.` | `.\|.` | `.\|.` | `.\|.` | `.\|.` | `.\|.` |
| `1/.` | `1/.` | `0/.` | `0/.` | `1/.` | `./.` | `./.` |
| `./2` | `./0` | `./1` | `./0` | `./.` | `./1` | `./.` |
| `.\|2` | `.\|0` | `.\|1` | `.\|0` | `.\|.` | `.\|1` | `.\|.` |
| `0/0` | `0/0` | `0/0` | `0/0` | `0/0` | `0/0` | `0/0` |
| `1/1` | `1/1` | `0/0` | `0/0` | `1/1` | `./.` | `./.` |
| `1/2/2` | `1/0/0` | `0/1/1` | `0/0/0` | `1/./.` | `./1/1` | `././.` |
| `0/0/3` | `0/0/0` | `0/0/0` | `0/0/1` | `0/0/.` | `0/0/.` | `0/0/1` |
| `2/1` | `0/1` | `1/0` | `0/0` | `./1` | `1/.` | `./.` |
| `1/3` | `1/0` | `0/0` | `0/1` | `1/.` | `./.` | `./1` |
| `3/3` | `0/0` | `0/0` | `1/1` | `./.` | `./.` | `1/1` |
| `0\|0` | `0\|0` | `0\|0` | `0\|0` | `0\|0` | `0\|0` | `0\|0` |

In short, bcftools' split is well defined where the input is well formed (rows 1-15, 21, 25),
and the draft reproduces it there exactly. Where the input is not well formed, it isn't:
undefined tags are dropped silently (18, 23, 35); wrong counts are filled or copied silently
(17, 23), or crash the program (19); an allele the record lacks becomes "another ALT" (10).

## Step 2: design

### Scope

In now:

- `-m -any`, `-m -both`, `-m -` and the glued `-m-any`, `-m-both`, `-m-`: split every record
  with two or more ALTs. The three types differ only when joining (row 5). The glued `-m-` is
  common in pipelines, as `-Oz` is. The long `--multiallelics` is not in, as `--output` is not.
- `--multi-overlaps 0|.` (default `0`, as bcftools; all three reviewers agreed). It is the only
  way to split `1/2` without a REF claim (see "What splitting loses"). Without `-m` it changes
  only the header's command line.

Out for now, a usage error:

- **Joining** (`-m +...`). It merges records from different lines (its own buffer, keyed by
  position) and inverts every field rule (filling, renumbering genotypes, choosing ID, QUAL,
  FILTER). It is not the inverse of splitting after normalization (row 7). It would need a
  review of its own.
- **`-m -snps`, `-m -indels`**: they depend on htslib's variant classification (row 6).
- **`--keep-sum AD`** (row 24): arithmetic on AD; easy to add later as its own law.
- **`-S lex`**, `--force`.
- **G values of more than two copies** (polyploid): BAD_COUNT. This is a scope limit, not bad
  data: VCF defines their order, but framebender does not implement it now.

Later, not now: when the header lacks a reserved key (VCF 4.3, sections 1.6.1-1.6.2: AC, AF A;
AD, ADF, ADR R; PL, GL, GP G), its Number could come from the spec's table instead of refusing
it.

### Where framebender differs from bcftools, and why

The rule is the project's usual one: identical records where the input means one thing; stop,
rather than guess, where it does not.

| case | bcftools 1.24 | framebender (proposed) | why |
|---|---|---|---|
| tag with a value, not defined in the header, in a line to split (rows 18, 23) | dropped silently | `UNDEFINED_TAG`, naming the tag and the fix | without a Number nobody knows which values belong to which ALT |
| tag defined without a Number, or with one not read (`LR`, `LG`, a tab after it) (row 33) | copied whole (read as `.`) | `UNDEFINED_TAG` | the same guess: `LR` values are per allele |
| undefined key without a value (row 19) | aborts | copied | a flag has no values to share |
| A/R/G tag written without a value (row 19) | aborts | `BAD_COUNT` | |
| A/R/G with the wrong count: numeric INFO (row 16) | stops | `BAD_COUNT` (same outcome under `-c e`) | |
| A/R/G with the wrong count: String (17), numeric FORMAT in some samples, all-one-value FORMAT (23) | filled, ignored or copied unsplit | `BAD_COUNT` | a guess written as data |
| G count against the sample's copies (23) | by count alone (`GT=0/2`, `PL=7,8,9`: `0/0:7,8`, `0/1:7,9`, `out/dip3.vcf`) | from GT: one allele (`1`), n+1 values; two (`0/1`, `./.`), (n+1)(n+2)/2; no GT value, two only; a lone `.`, either count; more than two, `BAD_COUNT` | VCF 4.3 §1.6.2; a lone `.` is written for no-calls of any ploidy |
| polyploid G (a `0/1/2` sample with a 10-value PL) | stops: "the tag PL has wrong number of fields" (`out/trip.vcf`) | `BAD_COUNT` | scope limit (above) |
| a sample with more values than FORMAT keys | stops (VCF parse error), with or without `-m` | `BAD_COUNT` (without `-m`, passed as today) | |
| GT allele above n (row 10) | read as another ALT | `BAD_GT` | it names an allele the record does not have |
| GT allele with a leading zero or sign (`01/2`, `+1/2`) (row 35) | read as a number | `BAD_GT` | not how VCF writes an allele; rare |
| leading phase mark `\|1\|2` (row 35) | parse error | `BAD_GT` with `-m` (without `-m`, passed as today) | htslib 1.24 does not read VCF 4.4's form either |
| duplicate ALTs `A C,C` (row 27) | two records `A C`, no message | `ALT_DUP` (with "not split" when it is the split's code), as without `-m` | the `1/0` and `0/1` records would claim REF on a copy that carries C |
| duplicate symbolic ALTs `A <*>,<*>` | two records, no message | `ALT_DUP`, not split (without `-m`: out of scope, passed) | the same genotype problem; so here `-m -c e` stops where no `-m` passes |
| GT without a `##FORMAT` line (row 35) | GT dropped | GT split and kept | GT is defined by the VCF spec; dropping loses the genotypes |
| empty INFO entries (row 34) | dropped | kept as they are | every byte is kept, as today |
| lone `.` for a numeric A/R/G INFO tag (row 16) | stops | `.` in every record | `.` is a missing value of any Number |
| lone `.` for a numeric R FORMAT tag (row 22) | `.,.` | `.` | both mean missing; `.` is what came |
| short sample column (row 22) | padded | kept short | as today |
| GT position in FORMAT (row 11) | moved first | kept | as today |
| numbers (row 14) | re-printed | copied as written | as today |
| same INFO key twice (row 20) | first kept, later dropped | each entry split by its tag | framebender does not decide which duplicate is right |
| duplicate header definition (row 20) | first counts; later line removed | first counts; header copied | as today |
| a space before `>` in a definition (row 33) | line not read, tag undefined | read | the space is not part of any value |
| `-w` too small for a move (row 8) | unsorted output | UNSORTED | as today |
| a line that cannot be split, under `-c w` | (see above) | passed unsplit, with a warning ending "not split"; the output can then hold multiallelic records | as every problem under `-c w` |

Order of outcomes for a line that cannot be split (`unsplit_in`): if `judge`'s outcome for the
whole line stops the run (MALFORMED, UNKNOWN_CHROM, any problem under `-c e`), that outcome
comes, as without `-m`; otherwise the split's code. Under `-c e` the user sees the same stop as
without `-m` whenever there is one; under `-c w` an unknown CHROM still stops. Under `-c w`, a
whole-line problem that does not stop the run (REF_MISMATCH, BAD_END) is not reported for such
a line: only the split's code is (one warning per line, as for every problem).

An ALT equal to REF (`A C,A`) still splits: its record `A A` is ALT_DUP, as in bcftools
(row 27).

### What splitting loses

In plain terms, for the biologist reviewing:

1. **Which ALTs one individual carries together.** A `1/2` genotype (one copy with ALT 1, the
   other with ALT 2) becomes `1/0` in ALT 1's record and `0/1` in ALT 2's.
   - Read alone, each record says the other copy carries the reference allele. That was not
     observed: it carries the other ALT.
   - With `--multi-overlaps .` the records say `1/.` and `./1` ("unknown here"). That is true,
     but no record says any more that this individual has no reference copy at the site.
2. **That the records were one site.** `1|2` becomes `1|0` and `0|1`. Each record keeps its
   order and the sample's PS (phase set), so phased haplotypes can still be rebuilt across the
   records. What is lost is that the two came from one record: a reader sees two sites at the
   same place.
3. **Values for other ALTs.** AD `10,3,5` becomes `10,3` and `10,5`. The reads for the other ALT
   are counted nowhere in the record, so AD no longer adds up to DP.
4. **Genotype values (PL, GL, GP).** The record for ALT i keeps genotypes 0/0, 0/i, i/i. The
   values of genotypes with other ALTs (1/2) are dropped. The most likely genotype of a `1/2`
   sample is then not among them, and GP no longer sums to 1.
5. **Site-level values copied whole.** INFO with a fixed Number, `.` or `P` (DP, AN, VEP's CSQ
   with one entry per ALT under `Number=.`) is copied to every record, including the parts
   about other ALTs. ID is copied too, though an rsID may name one ALT only.
6. **That the ALTs were seen together.** Joining (`-m +`) cannot undo a split once
   normalization has moved the records apart (row 7).

### The definitions and laws

The exact diff is Appendix A; Appendix B has the examples. In plain terms:

**Definitions.**

- **Options.** `B.Opts` gains `split` (`-m`) and `over0` (`--multi-overlaps 0`, the default).
  The parser keeps the options that decide the text in `B.Sci` (strict, split, over0), so its
  state keeps its shape. `-m`, `--multi-overlaps` and their values are recorded in
  `##framebender_normCommand`.
- **Header** (`B.Defs`, `L.defs(vcf)`): the INFO and FORMAT definitions before `#CHROM`.
  - Each definition gives an ID and a `Num`: A, R, G; Other (a count, `.`, `P`), copied;
    Unknown (none, or anything else), refused when a value needs it.
  - A definition is cut at commas outside double quotes, spaces trimmed around keys and values
    (`B.Hdr.trim`).
  - The first definition of an ID counts.
- **`B.Rec.parts(defs, o, body)`** gives `Whole` (no `-m`, MALFORMED, fewer than two ALTs),
  `Pieces` (one record per ALT, in ALT order) or `Unsplit{code}`.
  - Two ALTs equal ignoring case: `ALT_DUP` (code `DupAlts`: its message adds "not split").
  - The record for ALT i of n keeps every field except ALT (the i-th alone), INFO and the
    samples.
  - **INFO**, per entry:
    - an entry without a value (flag, empty, INFO `.`) is kept, unless its tag is A/R/G
      (`BAD_COUNT`);
    - with a value: an undefined or Unknown tag is `UNDEFINED_TAG`; Other is kept;
    - A/R/G: a lone `.` is kept; else exactly `expected_count(num, n, 2)` values, and the
      record keeps ALT i's (A), REF's and ALT i's (R), or genotypes 0/0, 0/i, i/i (G).
  - **Each sample**, per FORMAT key:
    - `GT` by the genotype rule;
    - any other key as INFO, except that the expected G count follows the copies the sample's
      GT names (`B.Gt.copies`): one allele, n+1 values (REF's and ALT i's); two alleles or no GT
      value, (n+1)(n+2)/2; a lone `.`, either, as the count says (`B.Vals.copies`); more than
      two, none;
    - more values than keys is `BAD_COUNT`; a short column stays short.
  - **Genotype rule** (`B.Gt.split`): separators kept. Each allele `.` stays `.`. A number
    from 0 to n, written without leading zeros, becomes `B.Gt.rule`'s: 0 stays 0, i becomes 1,
    another ALT becomes 0 (`over0`) or `.`. Anything else is `BAD_GT`.
  - The first refusal, read left to right, names the code (the same for every record, so the
    first record's).
- **The run** (LAWS.bend):
  - `run` passes `defs(vcf)` to `line_in`, and a body line goes to `body_in(B.Rec.parts(...))`.
  - `Whole` is today's `R.body_line(judge(...))`.
  - `Pieces` feeds each record to `R.body_line(judge(fa, p), ...)` as a line of its own, with
    the line's terminator, number, CHROM, POS (for messages) and input POS (for the window). It
    stops at the first record that stops the run.
  - `Unsplit` goes to `unsplit_in` (above).
  - `out_items(fasta, vcf, o)` gives one item per record written.

**New laws**, each with its plain statement. ALT numbers count from 1; in the Bend text, `i` is
the 0-based place of a record among a line's records, so record `i` is ALT `i+1`.

| law | in plain terms |
|---|---|
| `whole_without_m` | Without `-m`, every line is handled as one record, as before `-m` existed. |
| `items_without_m` | Without `-m`, the records written are the body lines, exactly as before (so `sorted`, `grouped_in`, `no_unsorted` say, without `-m`, what they said before). |
| `whole_biallelic` | With `-m`, a record with one ALT is handled as without `-m`. |
| `whole_malformed` | With `-m`, a MALFORMED line is handled as without `-m` (it stops the run). |
| `biallelic_run` | On a file with no multiallelic record, `-m` changes nothing: same output, messages and exit code, apart from the recorded command line. |
| `split_when` | With `-m`, a well-formed line with two or more ALTs is split exactly when none of these holds: a carriage return anywhere in the line other than the one just before its final LF (`BAD_CR`); two equal ALTs (`ALT_DUP`); an INFO entry with a value whose tag is undefined or has an unread Number (`UNDEFINED_TAG`); an A/R/G INFO entry without a value, or whose value is not `.` and has not the expected count (`BAD_COUNT`); in a sample, a GT allele that is not `.` or a number from 0 to n without leading zeros (`BAD_GT`), a value whose key is undefined or unread (`UNDEFINED_TAG`), an A/R/G value that is not `.` and has not the expected count for the copies its GT names (`BAD_COUNT`), or more values than keys (`BAD_COUNT`). Expected count: A, n; R, n+1; G, n+1 for one copy, (n+1)(n+2)/2 for two, either for a lone `.` GT. Otherwise the line is refused. A whole-line outcome that stops the run is reported first; otherwise the message names `BAD_CR`, if it holds, and then the first of the later reasons, reading the line left to right (ALTs, INFO, then each sample in FORMAT's order, its extra values last). |
| `split_alts` | One record per ALT, each with that ALT alone, in the input's ALT order. |
| `split_site` | Each record keeps CHROM, POS, ID, REF, QUAL, FILTER and FORMAT byte for byte, and its number of columns. |
| `split_valid` | If the line is a valid variant on its contig, so is every record; the laws of the normal form apply to each. |
| `split_normalized` | If the whole line would be normalized (no problem), every record is normalized. |
| `split_change` | The record for ALT a, as written (normalized, or passed as it came: any outcome that does not stop the run), read back from its text as a variant on the reference, makes exactly ALT a's change: the contig after ALT a. Where the records go in the output is `sorted`'s matter. |
| `split_gt` | In the record for ALT a, every genotype is well written and names, copy by copy: REF where the input named REF; the record's ALT (1) where the input named ALT a; REF (`--multi-overlaps 0`) or unknown (`.`) where the input named another ALT; unknown where the input's was unknown. |
| `split_phase` | ... with the input's separators, so its phasing and ploidy. |
| `split_info_keys` | Each record has the input's INFO keys, in order. |
| `split_info_values` | Every INFO entry with Number A, R or G and a value other than `.` gives, in the record for ALT a, exactly the values of that record's alleles: A, ALT a's; R, REF's and ALT a's; G, those of genotypes REF/REF, REF/ALT a, ALT a/ALT a (the input's 0/0, 0/a, a/a, at places k(k+1)/2+j), which become the record's 0/0, 0/1, 1/1. |
| `split_info_kept` | Every other INFO entry (a flag, an empty entry, a value `.`, a tag with a count, `.` or `P`) is copied by the split byte for byte. `judge` then rewrites END for a record normalization moves, by the END rule, as without `-m`. |
| `split_format_shape` | Each sample has as many values as in the input (no column if the input has none). |
| `split_format_values` | As `split_info_values`, per sample value other than GT. For G: a sample whose GT names one copy gives REF's and ALT a's values; two copies, or no GT value, the three genotype values; a lone `.` GT, whichever its count says. (More than two copies is refused, not split.) |
| `split_format_kept` | Every other sample value (other than GT): a value `.`, a tag with a count, `.` or `P`, is copied byte for byte. |

Nothing approved changes meaning:

- `items(fasta, vcf)` is unchanged.
- `sorted`, `grouped_in` and `no_unsorted` read `out_items(fasta, vcf, o)`, which is
  `items(fasta, vcf)` without `-m` (`items_without_m`). So each old statement is the new one's
  case without `-m`.
- `twice_run` holds unchanged: the output's records have one ALT each, or are lines passed with
  a problem, which pass again the same way. The output's header has the same definitions.
- `run` gains `+vcf` (it reads the file twice: for its lines and for `defs`), a linearity mark.

The summary's counts are of records after splitting ("N records" counts each split record), as
the `Summary` comment now says; bcftools' "total" counts input lines. The docs will say so.

### How `run` changes

- One input line may give several items, each judged as a line of its own and inserted into the
  sorting buffer in ALT order, with the input line's POS as input POS.
- Every rule of the window, the CHROM runs and UNSORTED applies to them as to any line.
  - Records of one line with equal output POS stay in ALT order, as in bcftools (row 2).
  - A record stops the run with UNSORTED exactly when it would be written after a record with a
    larger POS on the same CHROM, as any record does. bcftools writes it out of order (row 8).
  - `no_unsorted` gives a sufficient condition for this not to happen: sorted input whose
    records move left by less than `-w`.
- Messages for a record name the input line (its number, CHROM and POS as written). Under
  `-c w`, a REF mismatch gives one warning per record, each naming the same line, as bcftools
  does (row 28).

### `law machine`, `usage`, `threads`, `output`

Their statements stay as they are.

- `machine` says the program writes `L.run`, which now includes splitting.
- `usage` follows `B.Args.parse`.
- `threads` and `output` quantify over positions where the parser expects an option. The new
  options add two waiting states (after `-m`, after `--multi-overlaps`), where `--threads` or
  `-o` is that option's value and is refused, as after `-c` today. Their proofs gain the two
  states and show that `B.Args.expecting` is unchanged for every other prefix.

### The implementation and the proofs

1. **Spec**: the diff, `examples.bend` (Appendix B's 107 cases), docs/LAWS.md. The docs add
   the worked PL example (Terms), polyploid G as a scope limit, the summary's counts after
   splitting, one REF_MISMATCH warning per record under `-c w`, and multiallelic records left
   in the output by `-c w`.
2. **Prototype and timing, before any machine proof** (item 14, after round 2):
   - An unproven split path: decode, `B.Rec.parts` with linear output, each record through the
     String path's judge.
   - Timed against `bcftools norm -m -any` on a heavy synthetic cohort (GT:AD:DP:GQ:PL, 3,202
     samples, dense multiallelic lines, about 100 KB per line) and on the joined `sub.vcf`.
   - Two versions: the spec as written (which, for each of the n records, splits every column
     again and looks up every value's Number in the header), and one that looks up each FORMAT
     key's Number once per line and splits each column once. If the second is kept, it comes
     with a small proof that it gives the same records.
   - From that: stage 1 alone (the String path), or stage 2 too (split on packed bytes, at least
     for the common FORMAT shapes, with its refinement proof, about phase C's size).
3. **Code, stage 1.** Nothing changes without `-m`.
   - The machine parses the header's `Defs` once, as it reads the header lines, and keeps them
     with `split` and `over0` in its state. The parallel machine's tasks get that `Defs` in
     their fresh state; they do not parse it themselves (they see no header).
   - A body line with `-m` and a comma in its ALT field goes to the String path: `B.Rec.parts`
     (the spec's own function), then each record through the String path's judge and the run's
     bookkeeping.
   - The fast path (`norm_fast.bend`) and the rewriter (`norm_fix.bend`) refuse a line whose ALT
     field has a comma when `split` is on.
4. **Proofs.**
   - The 19 new laws on the spec, about 3,000-4,000 lines. `split_when` is the largest: the
     spec's refusal against `split_problem`.
   - `sorted`, `grouped_in`, `no_unsorted`, `twice_run` with several items per line, and
     `items_without_m`, `biallelic_run`: about 2,000-3,000 lines.
   - The machine: `Defs` and the two options through every proof that names `B.Opts` (17
     files) or the machine's state; the String path's split branch; one more condition for the
     fast path and the rewriter; the parser's two states. About 2,000-4,000 lines, much of it
     mechanical.
   - Total: 7,000-11,000 lines. For scale, phase F was 1,700 and phase C 15,600.

The `lawful-*` packages need no new law as far as I can see.

### Tests

- **Identity with bcftools** (`test/compare.sh` with `-m -any`, and with `--multi-overlaps .`).
  Before comparing, the script pads sample columns (as now) and maps bcftools' `.,.` for a
  missing numeric R value back to `.`.
  - HG002 chr22 (577 split lines) and the whole HG002 benchmark (47,781 multiallelic records).
  - `data/kg/sub.vcf` (no multiallelic record: `-m` changes nothing, `biallelic_run`).
  - The joined cohort file `bcftools norm -m +any data/kg/sub.vcf`, split back.
  - The scrambled set of HG002's multiallelic records.
  - A differential fuzz (`test/gen_split.py`): random well-formed multiallelic lines (every
    Number, ploidy, genotype form, missing values, symbolic ALTs, moves across the window),
    both tools, differences mapped as in the table above.
  - Generated cases for every row of the table, including each refusal and its code, and
    `-c e` / `-c w`.
- **Every `--threads`** (`test/threads.sh`, `test/par.sh`, `test/out.sh`, with `-m -any` cases),
  and `test/same.sh` without `-m` against the current build (byte-identical).
- **Speed and memory** against `bcftools norm -m -any -f` (`test/bench.sh`, one at a time): the
  synthetic heavy cohort, the joined `sub.vcf`, HG002 whole genome and chr22.

### Round 2 questions, answered

All three reviewers: trim spaces only (htslib's behaviour; decision 4 amended); a lone `.` GT
is one copy, with Claude's option taken (accept either count, decision 17); keep the exact
refusal code in `split_when`. No open question.

## Appendix A: the diff

Against 36990fc. Applied in `data/tmp/split/draft/` (`types.bend`, `run.bend`, `LAWS.bend`,
with `tan.bend` copied unchanged), where `test/bcheck.sh data/tmp/split/draft/LAWS.bend` reports
only the 32 laws as TODO (13 existing, 19 new) and no other error.

```diff
--- types.bend	2026-10-30 10:29:42.634168635 +0000
+++ types.bend	2026-10-30 12:11:44.529920745 +0000
@@ -624,6 +624,10 @@
   Unsorted{}
   NoHeader{}
   Stale{}
+  UndefinedTag{tag: String}
+  BadCount{}
+  BadGt{}
+  DupAlts{}
 
 def Code.name(c: Code) -> String:
   match c:
@@ -647,13 +651,38 @@
       "NO_HEADER"
     case Stale{}:
       "POSSIBLY_STALE"
+    case UndefinedTag{t}:
+      "UNDEFINED_TAG"
+    case BadCount{}:
+      "BAD_COUNT"
+    case BadGt{}:
+      "BAD_GT"
+    case DupAlts{}:
+      "ALT_DUP"
+
+# What a message adds after where it points: for a line -m could not split,
+# that it was not split, and for UNDEFINED_TAG the tag (INFO/XX or
+# FORMAT/XX) and how to fix it. Nothing for any other code.
+def Code.detail(c: Code) -> String:
+  match c:
+    case UndefinedTag{t}:
+      "\t" ++ t ++ " has no usable header line (add one, e.g. with bcftools annotate -h); not split"
+    case BadCount{}:
+      "\tnot split"
+    case BadGt{}:
+      "\tnot split"
+    case DupAlts{}:
+      "\tnot split"
+    case _:
+      ""
 
 # What happens to one body line (every line after the #CHROM line).
 #   Broken: MALFORMED, the run stops.
 #   Skipped: out of scope, passed through unchanged.
 #   NoContig: CHROM is not in the reference, the run stops.
 #   Problem: one of BAD_END, NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH; the run
-#     stops under -c e, the line is passed through under -c w.
+#     stops under -c e, the line is passed through under -c w. (-m adds
+#     UNDEFINED_TAG, BAD_COUNT and BAD_GT for a line it cannot split: B.Parts.)
 #   Normalized: the line is written in normal form.
 type Outcome is Data:
   Broken{}
@@ -678,8 +707,9 @@
 #   Stop: the run stops (exit code 1). For UNSORTED, at is the line that would
 #     come out of order and prev the line already written that it would have
 #     to come before (none when a CHROM comes back after another one).
-#   Summary: the run succeeded (exit code 0), with counts of body lines: all,
-#     changed by normalization, out of scope, passed through with a problem.
+#   Summary: the run succeeded (exit code 0), with counts of records (with
+#     -m, after splitting: each record of a split line counts): all, changed
+#     by normalization, out of scope, passed through with a problem.
 type Note is Data:
   Warning{code: Code, at: At}
   Stop{code: Code, at: Maybe<&2, At>, prev: Maybe<&2, At>}
@@ -700,23 +730,28 @@
 # The text of a message: one line.
 def Note.render(n: Note) -> String:
   match n:
-    case Warning{c, a}:
-      Code.name(c) ++ "\t" ++ At.show(a) ++ "\n"
-    case Stop{c, a, k}:
-      "error: " ++ Code.name(c) ++ At.show_maybe(a, "\t") ++ At.show_maybe(k, "\tbefore\t") ++ "\n"
+    case Warning{+c, a}:
+      Code.name(c) ++ "\t" ++ At.show(a) ++ Code.detail(c) ++ "\n"
+    case Stop{+c, a, k}:
+      "error: " ++ Code.name(c) ++ At.show_maybe(a, "\t") ++ At.show_maybe(k, "\tbefore\t") ++ Code.detail(c) ++ "\n"
     case Summary{n, ch, sk, wa}:
       "framebender: " ++ Nat.show(n) ++ " records, " ++ Nat.show(ch) ++ " changed, " ++ Nat.show(sk) ++ " out of scope, " ++ Nat.show(wa) ++ " passed with a problem\n"
 
 # The options of one run.
 #   strict: True for -c e (the default: a problem stops the run), False for -c w.
 #   w: the sorting window (-w, default 1000, at least 1).
+#   split: -m -any (or -m -both, -m -): a record with two or more ALTs is
+#     written as one record per ALT (B.Rec.parts).
+#   over0: --multi-overlaps 0 (the default): in the record for one ALT, a
+#     genotype's other ALTs become REF (0); False for --multi-overlaps '.':
+#     they become missing ('.').
 #   args: the command-line arguments that decide the output, recorded in the
 #     header: all those after "norm" except --threads, -o and -O and their
 #     values (which only size the program's work, or choose how and where the
 #     text is written), so the text is the same for every N, every output
 #     file and every output type.
 type Opts is Data:
-  Opts{strict: Bool, w: Nat, args: List<&2, String>}
+  Opts{strict: Bool, w: Nat, split: Bool, over0: Bool, args: List<&2, String>}
 
 # A parsed command line: the options, the FASTA path, the VCF path. The thread
 # count (--threads) and the output options (-o, -O) are not part of it (see
@@ -726,7 +761,7 @@
 
 # The usage message, printed on a usage error (exit code 2).
 def usage() -> String:
-  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"
+  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [-m -any|-both|-] [--multi-overlaps 0|.] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"
 
 # The largest thread count --threads accepts: a chosen limit, the most worker
 # threads Bend's runtime runs and the size of the driver's tables.
@@ -742,6 +777,8 @@
   PThr{}
   POut{}
   PType{}
+  PMulti{}
+  POver{}
 
 # An output type, as -O names it: v, plain VCF (z False), or z, VCF in BGZF
 # (z True), with a compression level from 0 to 9 (level, on htslib's scale;
@@ -826,11 +863,37 @@
   Bool.pick(Maybe<&2, OType>, String.eq(x, "z"), Some{OType{True{}, None{}}},
   Args.otype.lvl(String.starts_with(x, "z") && Nat.is_eq(String.length(x), 2n), Pos.read(String.drop(x, 1n)))))
 
+# The options read so far that decide the text: -c (strict), -m (split),
+# --multi-overlaps (over0).
+type Sci is Data:
+  Sci{strict: Bool, split: Bool, over0: Bool}
+
+def Sci.check(+x: String, s: Sci) -> Sci:
+  match s:
+    case Sci{+c, m, z}:
+      Sci{String.eq(x, "e") || (c && Bool.not(String.eq(x, "w"))), m, z}
+
+def Sci.multi(s: Sci) -> Sci:
+  match s:
+    case Sci{c, m, z}:
+      Sci{c, True{}, z}
+
+def Sci.over(+x: String, s: Sci) -> Sci:
+  match s:
+    case Sci{c, m, +z}:
+      Sci{c, m, String.eq(x, "0") || (z && Bool.not(String.eq(x, ".")))}
+
+# The values -m accepts: -any, -both and - (all three split every record with
+# two or more ALTs, as in bcftools 1.24). -snps, -indels and the joining forms
+# (+...) are not accepted.
+def Args.multi(+x: String) -> Bool:
+  String.eq(x, "-any") || String.eq(x, "-both") || String.eq(x, "-")
+
 # The command line read so far; ok turns False on any error. drv: the thread
 # count and the output options; keep: the arguments recorded in the header
 # (all but --threads, -o, -O and their values), in order.
 type ArgSt is Data:
-  ArgSt{pend: Pend, strict: Bool, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}
+  ArgSt{pend: Pend, sci: Sci, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}
 
 def Args.typ(m: Maybe<&2, OType>, st: ArgSt) -> ArgSt:
   match m st:
@@ -847,11 +910,14 @@
       Bool.pick(ArgSt, String.eq(x, "-f"), ArgSt{PRef{}, s, w, t, r, v, ok, kx},
       Bool.pick(ArgSt, String.eq(x, "-c"), ArgSt{PCheck{}, s, w, t, r, v, ok, kx},
       Bool.pick(ArgSt, String.eq(x, "-w"), ArgSt{PWin{}, s, w, t, r, v, ok, kx},
+      Bool.pick(ArgSt, String.eq(x, "-m"), ArgSt{PMulti{}, s, w, t, r, v, ok, kx},
+      Bool.pick(ArgSt, String.eq(x, "--multi-overlaps"), ArgSt{POver{}, s, w, t, r, v, ok, kx},
+      Bool.pick(ArgSt, String.starts_with(x, "-m"), ArgSt{PNone{}, Sci.multi(s), w, t, r, v, ok && Args.multi(String.drop(x, 2n)), kx},
       Bool.pick(ArgSt, String.eq(x, "--threads"), ArgSt{PThr{}, s, w, t, r, v, ok, k},
       Bool.pick(ArgSt, String.eq(x, "-o"), ArgSt{POut{}, s, w, t, r, v, ok, k},
       Bool.pick(ArgSt, String.eq(x, "-O"), ArgSt{PType{}, s, w, t, r, v, ok, k},
       Bool.pick(ArgSt, String.starts_with(x, "-O"), Args.typ(Args.otype(String.drop(x, 2n)), ArgSt{PType{}, s, w, t, r, v, ok, k}),
-      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx})))))))
+      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx}))))))))))
 
 def Args.win(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
   match m st:
@@ -875,8 +941,12 @@
       Args.word(x, ArgSt{PNone{}, s, w, t, r, v, ok, k})
     case ArgSt{PRef{}, s, w, t, r, v, ok, k}:
       ArgSt{PNone{}, s, w, t, Some{x}, v, ok && Maybe.is_none(&2, String, r), List.append(&2, String, k, [x])}
-    case ArgSt{PCheck{}, +s, w, t, r, v, ok, k}:
-      ArgSt{PNone{}, String.eq(x, "e") || (s && Bool.not(String.eq(x, "w"))), w, t, r, v, ok && (String.eq(x, "e") || String.eq(x, "w")), List.append(&2, String, k, [x])}
+    case ArgSt{PCheck{}, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, Sci.check(x, s), w, t, r, v, ok && (String.eq(x, "e") || String.eq(x, "w")), List.append(&2, String, k, [x])}
+    case ArgSt{PMulti{}, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, Sci.multi(s), w, t, r, v, ok && Args.multi(x), List.append(&2, String, k, [x])}
+    case ArgSt{POver{}, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, Sci.over(x, s), w, t, r, v, ok && (String.eq(x, "0") || String.eq(x, ".")), List.append(&2, String, k, [x])}
     case ArgSt{PWin{}, s, w, t, r, v, ok, k}:
       Args.win(Pos.read(x), ArgSt{PWin{}, s, w, t, r, v, ok, List.append(&2, String, k, [x])})
     case ArgSt{PThr{}, s, w, t, r, v, ok, k}:
@@ -895,14 +965,14 @@
 
 def Args.done(st: ArgSt) -> Maybe<&2, Cfg>:
   match st:
-    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
-      Some{Cfg{Opts{s, Maybe.default(&2, Nat, w, 1000n), k}, r, v}}
+    case ArgSt{PNone{}, Sci{c, m, z}, w, t, Some{r}, Some{v}, True{}, k}:
+      Some{Cfg{Opts{c, Maybe.default(&2, Nat, w, 1000n), m, z, k}, r, v}}
     case _:
       None{}
 
 # The state before the first argument after "norm".
 def Args.init() -> ArgSt:
-  ArgSt{PNone{}, True{}, None{}, Drv.none(), None{}, None{}, True{}, Nil{}}
+  ArgSt{PNone{}, Sci{True{}, False{}, True{}}, None{}, Drv.none(), None{}, None{}, True{}, Nil{}}
 
 def Args.done.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Cfg>:
   match ok:
@@ -913,10 +983,14 @@
 
 # The command line after the program name: "norm", then the options -f FASTA
 # (required), -c e or -c w (default e), -w N (N at least 1, default 1000),
+# -m X or the glued -mX (X: -any, -both or -; no -m: records are not split),
+# --multi-overlaps 0 or --multi-overlaps . (default 0; without -m it changes
+# nothing but the header's command line),
 # --threads N (N from 1 to Args.max_threads()), -o PATH (any word not ending
 # in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9) in any order, and one
-# VCF path. None for anything else (a usage error). For -c, -w, --threads, -o
-# and -O every one given must be valid, and the last one counts.
+# VCF path. None for anything else (a usage error). For -c, -w, -m,
+# --multi-overlaps, --threads, -o and -O every one given must be valid, and
+# the last one counts.
 def Args.parse(argv: List<&2, String>) -> Maybe<&2, Cfg>:
   match argv:
     case Nil{}:
@@ -1061,3 +1135,593 @@
       None{}
     case +cmd <> +rest:
       Args.output.if(String.eq(cmd, "norm"), rest)
+
+
+# ===========================================================================
+# Splitting multiallelic records (-m)
+# ===========================================================================
+
+# How many values an INFO or FORMAT tag has, as its header definition's
+# Number says (VCF 4.3, section 1.4.2): A, one per ALT allele; R, one per
+# allele, REF first; G, one per genotype; Other, a count (0 for a flag), '.'
+# (any number) or P (one per copy of the chromosome), which -m copies whole;
+# Unknown, no Number or one framebender does not read (such as VCF 4.4's LA,
+# LR, LG), which -m refuses to guess about.
+type Num is Data:
+  NumA{}
+  NumR{}
+  NumG{}
+  NumOther{}
+  NumUnknown{}
+
+# One INFO or FORMAT definition of the header: the tag's ID and its Number.
+type Tag is Data:
+  Tag{id: String, num: Num}
+
+# The header's definitions, in header order: the INFO tags, the FORMAT tags.
+type Defs is Data:
+  Defs{info: List<&2, Tag>, fmt: List<&2, Tag>}
+
+def Defs.info(d: Defs) -> List<&2, Tag>:
+  match d:
+    case Defs{i, f}:
+      i
+
+def Defs.fmt(d: Defs) -> List<&2, Tag>:
+  match d:
+    case Defs{i, f}:
+      f
+
+def Hdr.push(h: Char, ps: List<&2, String>) -> List<&2, String>:
+  match ps:
+    case Nil{}:
+      [SCon{h, SNil{}}]
+    case p <> t:
+      SCon{h, p} <> t
+
+def Hdr.cut.put(comma: Bool, h: Char, rest: List<&2, String>) -> List<&2, String>:
+  match comma:
+    case True{}:
+      "" <> rest
+    case False{}:
+      Hdr.push(h, rest)
+
+# A definition's text cut at every comma outside double quotes (q: inside
+# quotes; esc: inside quotes, after a backslash, so this character does not
+# end them). The Description of ##INFO=<ID=DP,Number=1,Description="a, b">
+# stays one piece.
+def Hdr.cut(s: String, +q: Bool, +esc: Bool) -> List<&2, String>:
+  match s:
+    case SNil{}:
+      [""]
+    case SCon{+h, t}:
+      +x = Char.code(h)
+      +quote = U32.is_eq(x, 34) && Bool.not(esc)
+      Hdr.cut.put(U32.is_eq(x, 44) && Bool.not(q), h,
+        Hdr.cut(t, Bool.pick(Bool, quote, Bool.not(q), q), q && Bool.not(esc) && U32.is_eq(x, 92)))
+
+def Hdr.ltrim.put(keep: Bool, h: Char, rest: String) -> String:
+  match keep:
+    case True{}:
+      SCon{h, rest}
+    case False{}:
+      rest
+
+def Hdr.ltrim.go(s: String, +keep: Bool) -> String:
+  match s:
+    case SNil{}:
+      SNil{}
+    case SCon{+h, t}:
+      +k = keep || Bool.not(U32.is_eq(Char.code(h), 32))
+      Hdr.ltrim.put(k, h, Hdr.ltrim.go(t, k))
+
+# Text without the spaces at its start and at its end (htslib 1.24 reads
+# "ID=IA, Number=A" and "Number = A " as Number A; a tab is not trimmed).
+def Hdr.trim(s: String) -> String:
+  String.reverse(Hdr.ltrim.go(String.reverse(Hdr.ltrim.go(s, False{})), False{}))
+
+def Hdr.value.put(hit: Bool, +p: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
+  match hit:
+    case True{}:
+      Some{Hdr.trim(String.drop(p, Nat.add(String.length(Info.key(p)), 1n)))}
+    case False{}:
+      rest
+
+# The value of the first piece "k=value" (key and value trimmed).
+def Hdr.value(ps: List<&2, String>, +k: String) -> Maybe<&2, String>:
+  match ps:
+    case Nil{}:
+      None{}
+    case +p <> t:
+      Hdr.value.put(String.eq(Hdr.trim(Info.key(p)), k) && Nat.is_lt(String.length(Info.key(p)), String.length(p)), p, Hdr.value(t, k))
+
+# A Number: A, R, G; '.', P or a count (digits) are Other; anything else, or
+# none, is Unknown.
+def Num.of(m: Maybe<&2, String>) -> Num:
+  match m:
+    case None{}:
+      NumUnknown{}
+    case Some{+v}:
+      Bool.pick(Num, String.eq(v, "A"), NumA{},
+      Bool.pick(Num, String.eq(v, "R"), NumR{},
+      Bool.pick(Num, String.eq(v, "G"), NumG{},
+      Bool.pick(Num, String.eq(v, ".") || String.eq(v, "P") || Maybe.is_some(&2, Nat, Pos.read(v)), NumOther{}, NumUnknown{}))))
+
+def Hdr.tag.of(m: Maybe<&2, String>, +ps: List<&2, String>) -> Maybe<&2, Tag>:
+  match m:
+    case None{}:
+      None{}
+    case Some{id}:
+      Some{Tag{id, Num.of(Hdr.value(ps, "Number"))}}
+
+# The tag a definition defines, from its text after '<' (one '>' at its end
+# dropped, after trimming): its first ID and its first Number. None without an
+# ID.
+def Hdr.tag(+s: String) -> Maybe<&2, Tag>:
+  +t = Hdr.trim(s)
+  +ps = Hdr.cut(Bool.pick(String, String.ends_with(t, ">"), String.take(t, Nat.sub(String.length(t), 1n)), t), False{}, False{})
+  Hdr.tag.of(Hdr.value(ps, "ID"), ps)
+
+def Defs.add_info(m: Maybe<&2, Tag>, d: Defs) -> Defs:
+  match m d:
+    case None{} _:
+      d
+    case Some{t} Defs{i, f}:
+      Defs{List.append(&2, Tag, i, [t]), f}
+
+def Defs.add_fmt(m: Maybe<&2, Tag>, d: Defs) -> Defs:
+  match m d:
+    case None{} _:
+      d
+    case Some{t} Defs{i, f}:
+      Defs{i, List.append(&2, Tag, f, [t])}
+
+# One more header line: "##INFO=<...>" adds an INFO tag, "##FORMAT=<...>" a
+# FORMAT tag; any other line changes nothing.
+def Defs.line(+d: Defs, +body: String) -> Defs:
+  Bool.pick(Defs, String.starts_with(body, "##INFO=<"), Defs.add_info(Hdr.tag(String.drop(body, 8n)), d),
+  Bool.pick(Defs, String.starts_with(body, "##FORMAT=<"), Defs.add_fmt(Hdr.tag(String.drop(body, 10n)), d), d))
+
+def Tags.find.put(hit: Bool, n: Num, rest: Maybe<&2, Num>) -> Maybe<&2, Num>:
+  match hit:
+    case True{}:
+      Some{n}
+    case False{}:
+      rest
+
+# The Number of tag k: its first definition counts (as in htslib 1.24); None
+# when the header does not define k.
+def Tags.find(ts: List<&2, Tag>, +k: String) -> Maybe<&2, Num>:
+  match ts:
+    case Nil{}:
+      None{}
+    case Tag{id, n} <> t:
+      Tags.find.put(String.eq(id, k), n, Tags.find(t, k))
+
+# The Number is A, R or G: the tag has values per allele or per genotype.
+def Num.per_allele(m: Maybe<&2, Num>) -> Bool:
+  match m:
+    case Some{NumA{}}:
+      True{}
+    case Some{NumR{}}:
+      True{}
+    case Some{NumG{}}:
+      True{}
+    case _:
+      False{}
+
+# A field of a split record (its text), or the reason the record cannot be
+# split.
+type Got is Data:
+  Got{s: String}
+  Refuse{c: Code}
+
+def Got.cat(a: Got, +sep: String, b: Got) -> Got:
+  match a b:
+    case Refuse{c} _:
+      Refuse{c}
+    case Got{x} Refuse{c}:
+      Refuse{c}
+    case Got{x} Got{y}:
+      Got{x ++ sep ++ y}
+
+def Got.join.put(g: Got, t: List<&2, Got>, +sep: String, rest: Got) -> Got:
+  match t:
+    case Nil{}:
+      g
+    case _:
+      Got.cat(g, sep, rest)
+
+# The texts joined with sep, from the right (each text is copied once); the
+# first refusal, if any.
+def Got.join(gs: List<&2, Got>, +sep: String) -> Got:
+  match gs:
+    case Nil{}:
+      Got{""}
+    case g <> +t:
+      Got.join.put(g, t, sep, Got.join(t, sep))
+
+def Got.of(m: Maybe<&2, String>, c: Code) -> Got:
+  match m:
+    case Some{x}:
+      Got{x}
+    case None{}:
+      Refuse{c}
+
+def Vals.pick.cons(m: Maybe<&2, String>, rest: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
+  match m rest:
+    case Some{x} Some{xs}:
+      Some{x <> xs}
+    case _ _:
+      None{}
+
+def Vals.pick(+vs: List<&2, String>, ks: List<&2, Nat>) -> Maybe<&2, List<&2, String>>:
+  match ks:
+    case Nil{}:
+      Some{Nil{}}
+    case k <> t:
+      Vals.pick.cons(List.get(&2, String, vs, k), Vals.pick(vs, t))
+
+# The place of genotype j/k (j <= k) among a diploid sample's G values:
+# k(k+1)/2 + j (VCF 4.3, section 1.6.2: 0/0, 0/1, 1/1, 0/2, 1/2, 2/2, ...).
+def Gt.index(j: Nat, +k: Nat) -> Nat:
+  Nat.add(Nat.div(Nat.mul(k, 1n+k), 2n), j)
+
+# The number of diploid genotypes of a record with n ALTs: (n+1)(n+2)/2.
+def Gt.count(+n: Nat) -> Nat:
+  Nat.div(Nat.mul(1n+n, 2n+n), 2n)
+
+# How many values a tag with Number A, R or G has in a record with n ALTs,
+# for ploidy p (the number of chromosome copies; INFO counts as 2): A, n; R,
+# n + 1; G, n + 1 when p is 1 (one value per allele), (n+1)(n+2)/2 when p is
+# 2 (one per diploid genotype). None for G with any other p (-m does not split
+# G values of more than two copies), and for any other Number.
+def Vals.expected_count(num: Num, +n: Nat, +p: Nat) -> Maybe<&2, Nat>:
+  match num:
+    case NumA{}:
+      Some{n}
+    case NumR{}:
+      Some{1n+n}
+    case NumG{}:
+      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(p, 1n), Some{1n+n},
+      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(p, 2n), Some{Gt.count(n)}, None{}))
+    case _:
+      None{}
+
+def Vals.fits(m: Maybe<&2, Nat>, +c: Nat) -> Bool:
+  match m:
+    case None{}:
+      False{}
+    case Some{x}:
+      Nat.is_eq(x, c)
+
+# Which values the record for ALT i keeps, for ploidy p: A, ALT i's (value
+# i - 1); R, REF's and ALT i's (0 and i); G with p = 1, REF's and ALT i's (0
+# and i); G with p = 2, those of the genotypes 0/0, 0/i and i/i.
+def Vals.idx(num: Num, +p: Nat, +i: Nat) -> List<&2, Nat>:
+  match num:
+    case NumA{}:
+      [Nat.sub(i, 1n)]
+    case NumR{}:
+      [0n, i]
+    case NumG{}:
+      Bool.pick(List<&2, Nat>, Nat.is_eq(p, 1n), [0n, i], [0n, Gt.index(0n, i), Gt.index(i, i)])
+    case _:
+      Nil{}
+
+def Vals.join(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, String>:
+  match m:
+    case None{}:
+      None{}
+    case Some{xs}:
+      Some{String.join(xs, ",")}
+
+# The number of copies c values are for, given what the sample's GT says
+# (Gt.copies): its count of copies; for a lone '.' GT (None), one copy when
+# there are n + 1 values, else two ((n+1)(n+2)/2 and n + 1 never coincide for
+# n >= 2, so the values kept are never in doubt).
+def Vals.copies(m: Maybe<&2, Nat>, +n: Nat, +c: Nat) -> Nat:
+  match m:
+    case Some{p}:
+      p
+    case None{}:
+      Bool.pick(Nat, Nat.is_eq(c, 1n+n), 1n, 2n)
+
+def Vals.keep(+num: Num, +n: Nat, +p: Nat, +i: Nat, +vs: List<&2, String>) -> Maybe<&2, String>:
+  Bool.pick(Maybe<&2, String>, Vals.fits(Vals.expected_count(num, n, p), List.length(&2, String, vs)),
+    Vals.join(Vals.pick(vs, Vals.idx(num, p, i))), None{})
+
+def Vals.split.if(missing: Bool, +num: Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, v: String) -> Maybe<&2, String>:
+  match missing:
+    case True{}:
+      Some{"."}
+    case False{}:
+      +vs = String.split(v, ',')
+      Vals.keep(num, n, Vals.copies(cp, n, List.length(&2, String, vs)), i, vs)
+
+# A per-allele value (comma-separated values) in the record for ALT i of n,
+# for the copies cp (Gt.copies; Some{2} in INFO): a lone '.' (the whole value
+# missing) stays '.'; else it must have expected_count values for its copies
+# (Vals.copies), and the record keeps those Vals.idx names, joined by commas.
+# None (BAD_COUNT) for any other count.
+def Vals.split(+num: Num, +n: Nat, cp: Maybe<&2, Nat>, +i: Nat, +v: String) -> Maybe<&2, String>:
+  Vals.split.if(String.eq(v, "."), num, n, cp, i, v)
+
+# An INFO entry with a value ("key=values"): UNDEFINED_TAG when the header
+# does not define its key, or defines it with an Unknown Number; kept as it
+# is for Number Other; per-allele values for A, R, G (ploidy 2).
+def Info.split.eq(m: Maybe<&2, Num>, +k: String, +e: String, +n: Nat, +i: Nat) -> Got:
+  match m:
+    case None{}:
+      Refuse{UndefinedTag{"INFO/" ++ k}}
+    case Some{NumUnknown{}}:
+      Refuse{UndefinedTag{"INFO/" ++ k}}
+    case Some{NumOther{}}:
+      Got{e}
+    case Some{num}:
+      Got.cat(Got{k}, "=", Got.of(Vals.split(num, n, Some{2n}, i, String.drop(e, Nat.add(String.length(k), 1n))), BadCount{}))
+
+# An INFO entry: an entry without '=' (a flag, an empty entry between two
+# ';') has no values to share and is kept, unless its tag is A, R or G
+# (BAD_COUNT); an entry with a value as Info.split.eq says.
+def Info.split.num(+m: Maybe<&2, Num>, +e: String, +n: Nat, +i: Nat) -> Got:
+  +k = Info.key(e)
+  Bool.pick(Got, String.eq(k, e), Bool.pick(Got, Num.per_allele(m), Refuse{BadCount{}}, Got{e}), Info.split.eq(m, k, e, n, i))
+
+def Info.split.go(es: List<&2, String>, +info: List<&2, Tag>, +n: Nat, +i: Nat) -> List<&2, Got>:
+  match es:
+    case Nil{}:
+      Nil{}
+    case +e <> t:
+      Info.split.num(Tags.find(info, Info.key(e)), e, n, i) <> Info.split.go(t, info, n, i)
+
+# INFO in the record for ALT i of n: each entry as Info.split.num says, in
+# order. A missing INFO ('.') is one entry without '=': kept.
+def Info.split(+info: String, +tags: List<&2, Tag>, +n: Nat, +i: Nat) -> Got:
+  Got.join(Info.split.go(String.split(info, ';'), tags, n, i), ";")
+
+# The allele a genotype names, in the record for ALT i: REF (0) stays REF;
+# ALT i becomes 1, the record's one ALT; any other ALT becomes REF under
+# --multi-overlaps 0 (over0, the default) or missing under
+# --multi-overlaps '.'; missing (None) stays missing.
+def Gt.rule(over0: Bool, +i: Nat, a: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
+  match a:
+    case None{}:
+      None{}
+    case Some{+x}:
+      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(x, 0n), Some{0n},
+      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(x, i), Some{1n},
+      Bool.pick(Maybe<&2, Nat>, over0, Some{0n}, None{})))
+
+def Gt.show(a: Maybe<&2, Nat>) -> String:
+  match a:
+    case None{}:
+      "."
+    case Some{x}:
+      Nat.show(x)
+
+def Text.all_digits(s: String) -> Bool:
+  match s:
+    case SNil{}:
+      True{}
+    case SCon{h, t}:
+      Char.is_digit(h) && Text.all_digits(t)
+
+# An allele number as VCF writes it: one or more digits, without leading
+# zeros ("0", "12"; not "", "01", "+1").
+def Gt.canon(+a: String) -> Bool:
+  Bool.not(String.is_empty(a)) && Text.all_digits(a) && (String.eq(a, "0") || Bool.not(String.starts_with(a, "0")))
+
+def Gt.num(m: Maybe<&2, Nat>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
+  match m:
+    case None{}:
+      Refuse{BadGt{}}
+    case Some{+a}:
+      Bool.pick(Got, Nat.is_le(a, n), Got{Gt.show(Gt.rule(over0, i, Some{a}))}, Refuse{BadGt{}})
+
+# One allele of a genotype as written, in the record for ALT i of n: '.'
+# stays '.'; a number from 0 to n written as Gt.canon says gives Gt.rule's
+# allele. BAD_GT for anything else.
+def Gt.allele(+over0: Bool, +n: Nat, +i: Nat, +a: String) -> Got:
+  Bool.pick(Got, String.eq(a, "."), Got{"."},
+    Bool.pick(Got, Gt.canon(a), Gt.num(Pos.read(a), over0, n, i), Refuse{BadGt{}}))
+
+def Gt.is_sep(c: Char) -> Bool:
+  +x = Char.code(c)
+  U32.is_eq(x, 47) || U32.is_eq(x, 124)
+
+# A genotype read from the right: the first allele's text, and the rest
+# (from the first separator on) as written in the record for one ALT.
+type Gp is Data:
+  Gp{tok: String, rest: Got}
+
+def Gt.go.put(sep: Bool, +h: Char, r: Gp, +over0: Bool, +n: Nat, +i: Nat) -> Gp:
+  match sep r:
+    case True{} Gp{tk, rs}:
+      Gp{"", Got.cat(Got.cat(Got{SCon{h, SNil{}}}, "", Gt.allele(over0, n, i, tk)), "", rs)}
+    case False{} Gp{tk, rs}:
+      Gp{SCon{h, tk}, rs}
+
+def Gt.go(s: String, +over0: Bool, +n: Nat, +i: Nat) -> Gp:
+  match s:
+    case SNil{}:
+      Gp{"", Got{""}}
+    case SCon{+h, t}:
+      Gt.go.put(Gt.is_sep(h), h, Gt.go(t, over0, n, i), over0, n, i)
+
+def Gt.split.of(r: Gp, +over0: Bool, +n: Nat, +i: Nat) -> Got:
+  match r:
+    case Gp{tk, rs}:
+      Got.cat(Gt.allele(over0, n, i, tk), "", rs)
+
+# A genotype (GT: alleles separated by '/', unphased, or '|', phased) in the
+# record for ALT i of n: each allele as Gt.allele says, every separator kept.
+# 1/2 becomes 1/0 for ALT 1 and 0/1 for ALT 2. (A leading separator, VCF
+# 4.4's "|0|1", is an empty allele: BAD_GT; htslib 1.24 refuses it too.)
+def Gt.split(+over0: Bool, +n: Nat, +i: Nat, g: String) -> Got:
+  Gt.split.of(Gt.go(g, over0, n, i), over0, n, i)
+
+def Gt.seps(s: String) -> Nat:
+  match s:
+    case SNil{}:
+      0n
+    case SCon{+h, t}:
+      Nat.add(Bool.pick(Nat, Gt.is_sep(h), 1n, 0n), Gt.seps(t))
+
+def Gt.copies.of(+g: String) -> Maybe<&2, Nat>:
+  Bool.pick(Maybe<&2, Nat>, String.eq(g, "."), None{}, Some{1n+Gt.seps(g)})
+
+# How many chromosome copies a sample's G values are for, from its GT: the
+# number of alleles GT names (one plus its separators: '1' and './.' are 1
+# and 2); Some{2} when the sample has no GT value (VCF 4.3, section 1.6.2:
+# without GT, G values are diploid); None for a lone '.' GT, written by many
+# tools for a no-call of any ploidy: one or two copies, as the count says
+# (Vals.copies).
+def Gt.copies(m: Maybe<&2, String>) -> Maybe<&2, Nat>:
+  match m:
+    case None{}:
+      Some{2n}
+    case Some{+g}:
+      Gt.copies.of(g)
+
+def Fmt.gt.put(hit: Bool, v: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
+  match hit:
+    case True{}:
+      Some{v}
+    case False{}:
+      rest
+
+# A sample's GT value: its value under FORMAT's first GT key, if it has one.
+def Fmt.gt(ks: List<&2, String>, vs: List<&2, String>) -> Maybe<&2, String>:
+  match ks vs:
+    case +k <> kt +v <> vt:
+      Fmt.gt.put(String.eq(k, "GT"), v, Fmt.gt(kt, vt))
+    case _ _:
+      None{}
+
+def Fmt.split.num(m: Maybe<&2, Num>, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> Got:
+  match m:
+    case None{}:
+      Refuse{UndefinedTag{"FORMAT/" ++ k}}
+    case Some{NumUnknown{}}:
+      Refuse{UndefinedTag{"FORMAT/" ++ k}}
+    case Some{NumOther{}}:
+      Got{v}
+    case Some{num}:
+      Got.of(Vals.split(num, n, p, i, v), BadCount{})
+
+def Fmt.split.one(+k: String, +v: String, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> Got:
+  Bool.pick(Got, String.eq(k, "GT"), Gt.split(over0, n, i, v), Fmt.split.num(Tags.find(fmt, k), k, v, n, p, i))
+
+def Fmt.split.go(ks: List<&2, String>, vs: List<&2, String>, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +p: Maybe<&2, Nat>, +i: Nat) -> List<&2, Got>:
+  match ks vs:
+    case _ Nil{}:
+      Nil{}
+    case Nil{} v <> t:
+      [Refuse{BadCount{}}]
+    case +k <> kt +v <> vt:
+      Fmt.split.one(k, v, fmt, over0, n, p, i) <> Fmt.split.go(kt, vt, fmt, over0, n, p, i)
+
+# One sample's column in the record for ALT i of n, read against the FORMAT
+# keys ks, in order: GT by Gt.split (GT needs no header line); a key the
+# header does not define, or defines with an Unknown Number, is
+# UNDEFINED_TAG; Number Other is kept; A, R, G give the values of the
+# record's alleles (Vals.split, for the sample's copies, Gt.copies). A
+# column with fewer values than keys keeps its length; more values than keys
+# is BAD_COUNT.
+def Fmt.split(+ks: List<&2, String>, +col: String, +fmt: List<&2, Tag>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
+  +vs = String.split(col, ':')
+  Got.join(Fmt.split.go(ks, vs, fmt, over0, n, Gt.copies(Fmt.gt(ks, vs)), i), ":")
+
+def Rec.piece.field(+j: Nat, +f: String, +a: String, +defs: Defs, +ks: List<&2, String>, +over0: Bool, +n: Nat, +i: Nat) -> Got:
+  Bool.pick(Got, Nat.is_eq(j, 4n), Got{a},
+  Bool.pick(Got, Nat.is_eq(j, 7n), Info.split(f, Defs.info(defs), n, i),
+  Bool.pick(Got, Nat.is_le(9n, j), Fmt.split(ks, f, Defs.fmt(defs), over0, n, i), Got{f})))
+
+def Rec.piece.go(fs: List<&2, String>, +j: Nat, +a: String, +defs: Defs, +ks: List<&2, String>, +over0: Bool, +n: Nat, +i: Nat) -> List<&2, Got>:
+  match fs:
+    case Nil{}:
+      Nil{}
+    case +f <> t:
+      Rec.piece.field(j, f, a, defs, ks, over0, n, i) <> Rec.piece.go(t, 1n+j, a, defs, ks, over0, n, i)
+
+# The record for ALT i (1 to n; a, its text) of a record with fields fs and n
+# ALTs: ALT is a alone; INFO and the samples are split (Info.split,
+# Fmt.split); every other field (CHROM, POS, ID, REF, QUAL, FILTER, FORMAT)
+# is kept.
+def Rec.piece(+fs: List<&2, String>, +a: String, +defs: Defs, +over0: Bool, +n: Nat, +i: Nat) -> Got:
+  Got.join(Rec.piece.go(fs, 0n, a, defs, String.split(Rec.field(fs, 8n), ':'), over0, n, i), "\t")
+
+def Rec.pieces.go(alts: List<&2, String>, +fs: List<&2, String>, +defs: Defs, +over0: Bool, +n: Nat, +i: Nat) -> List<&2, Got>:
+  match alts:
+    case Nil{}:
+      Nil{}
+    case +a <> t:
+      Rec.piece(fs, a, defs, over0, n, i) <> Rec.pieces.go(t, fs, defs, over0, n, 1n+i)
+
+def Alts.member(+x: String, xs: List<&2, String>) -> Bool:
+  match xs:
+    case Nil{}:
+      False{}
+    case y <> t:
+      String.eq(x, String.to_upper(y)) || Alts.member(x, t)
+
+# No two ALTs are equal, ignoring case.
+def Alts.distinct(xs: List<&2, String>) -> Bool:
+  match xs:
+    case Nil{}:
+      True{}
+    case x <> +t:
+      Bool.not(Alts.member(String.to_upper(x), t)) && Alts.distinct(t)
+
+# What -m does with one body line.
+#   Whole: the line is one record, handled as without -m.
+#   Pieces: one record per ALT, in ALT order (their texts).
+#   Unsplit: the line cannot be split (ALT_DUP, written DupAlts here so its
+#     message can add "not split"; UNDEFINED_TAG, BAD_COUNT or BAD_GT).
+type Parts is Data:
+  Whole{}
+  Pieces{ps: List<&2, String>}
+  Unsplit{c: Code}
+
+def Parts.cons(g: Got, rest: Parts) -> Parts:
+  match g rest:
+    case Refuse{c} _:
+      Unsplit{c}
+    case Got{x} Pieces{ps}:
+      Pieces{x <> ps}
+    case Got{x} r:
+      r
+
+def Parts.of(gs: List<&2, Got>) -> Parts:
+  match gs:
+    case Nil{}:
+      Pieces{Nil{}}
+    case g <> t:
+      Parts.cons(g, Parts.of(t))
+
+def Rec.parts.split(ok: Bool, +alts: List<&2, String>, +fs: List<&2, String>, +defs: Defs, +over0: Bool) -> Parts:
+  match ok:
+    case False{}:
+      Unsplit{DupAlts{}}
+    case True{}:
+      Parts.of(Rec.pieces.go(alts, fs, defs, over0, List.length(&2, String, alts), 1n))
+
+def Rec.parts.if(go: Bool, +defs: Defs, +over0: Bool, +fs: List<&2, String>) -> Parts:
+  match go:
+    case False{}:
+      Whole{}
+    case True{}:
+      +alts = Rec.alts(fs)
+      Rec.parts.split(Alts.distinct(alts), alts, fs, defs, over0)
+
+# What happens to a body line under the options o, given the header's
+# definitions: with -m (split), a line that is not MALFORMED and has two or
+# more ALTs is split into one record per ALT (Rec.piece), unless two of its
+# ALTs are equal (ALT_DUP) or a record refuses (the first refusal, reading the
+# records in ALT order and each left to right); any other line is Whole.
+def Rec.parts(+defs: Defs, o: Opts, +body: String) -> Parts:
+  match o:
+    case Opts{s, w, split, over0, args}:
+      +fs = Rec.fields(body)
+      Rec.parts.if(split && Bool.not(Rec.malformed(fs)) && Nat.is_le(2n, List.length(&2, String, Rec.alts(fs))), defs, over0, fs)
--- run.bend	2026-10-30 10:29:42.633168624 +0000
+++ run.bend	2026-10-30 11:40:01.320657595 +0000
@@ -36,7 +36,7 @@
 # the #CHROM line ends. No date, so the output is the same on every run.
 def added(o: B.Opts, +term: String) -> String:
   match o:
-    case B.Opts{s, w, args}:
+    case B.Opts{s, w, m, z, args}:
       "##framebender_normVersion=" ++ version() ++ term ++ "##framebender_normCommand=norm" ++ args_text(args) ++ term
 
 # The column-header line: its first field is exactly "#CHROM".
@@ -171,8 +171,8 @@
     case +x <> t:
       flush.put(flush.ok(last, Item.key(x)), x, last, flush(t, Some{x}))
 
-# Counts for the summary: body lines, changed, out of scope, passed through
-# with a problem.
+# Counts for the summary: records (with -m, each record of a split line),
+# changed, out of scope, passed through with a problem.
 type Cnt is Data:
   Cnt{lines: Nat, changed: Nat, skipped: Nat, warned: Nat}
 
@@ -278,14 +278,24 @@
 
 def Opts.w(o: B.Opts) -> Nat:
   match o:
-    case B.Opts{s, w, a}:
+    case B.Opts{s, w, m, z, a}:
       w
 
 def Opts.strict(o: B.Opts) -> Bool:
   match o:
-    case B.Opts{s, w, a}:
+    case B.Opts{s, w, m, z, a}:
       s
 
+def Opts.split(o: B.Opts) -> Bool:
+  match o:
+    case B.Opts{s, w, m, z, a}:
+      m
+
+def Opts.over0(o: B.Opts) -> Bool:
+  match o:
+    case B.Opts{s, w, m, z, a}:
+      z
+
 def problem_line(strict: Bool, +st: RunSt, +w: Nat, +c: B.Code, +l: B.Line, +at: B.At, +inpos: Nat) -> RunSt:
   match strict:
     case True{}:
--- LAWS.bend	2026-10-30 10:29:42.613168396 +0000
+++ LAWS.bend	2026-10-30 12:11:44.530808289 +0000
@@ -25,6 +25,7 @@
 # The laws, from the top:
 #   sorted, grouped_in, no_unsorted, twice_run   what run guarantees
 #   normalized_valid                              records normalized are valid
+#   whole_without_m ... split_format_values       splitting a record per ALT (-m)
 #   same_change ... shortest, unique              the normal form of one variant
 #   (MACHINE.bend: machine, usage)
 #
@@ -387,36 +388,104 @@
 # Definitions: the whole run
 # ==========================================================================
 
-def line_in(phase: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
+def piece_in(halted: Bool, +p: String, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) -> R.RunSt:
+  match halted:
+    case True{}:
+      st
+    case False{}:
+      R.body_line(judge(fa, p), st, o, B.Line{p, term}, at, inpos)
+
+# The records a split line gives, one after the other, each as a body line of
+# its own (judge), with the line's terminator, its place for messages and its
+# input POS; nothing happens once the run has stopped.
+def pieces_in(ps: List<&2, String>, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) -> R.RunSt:
+  match ps:
+    case Nil{}:
+      st
+    case +p <> t:
+      pieces_in(t, fa, o, piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos), term, at, inpos)
+
+# The outcome r stops the run: MALFORMED, UNKNOWN_CHROM, or a problem under
+# -c e (strict).
+def stops(r: B.Res, strict: Bool) -> Bool:
+  match r:
+    case B.Res{B.Broken{}, k, t, s}:
+      True{}
+    case B.Res{B.NoContig{}, k, t, s}:
+      True{}
+    case B.Res{B.Problem{c}, k, t, s}:
+      strict
+    case _:
+      False{}
+
+# A line -m cannot split (code c): if judge's outcome for the whole line
+# stops the run, that outcome comes first (as without -m); else c is a
+# problem: it stops the run under -c e, and under -c w the line is passed
+# through as it came, unsplit, with a warning.
+def unsplit_in(+r: B.Res, +c: B.Code, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
+  Bool.pick(R.RunSt, stops(r, R.Opts.strict(o)), R.body_line(r, st, o, l, at, inpos),
+    R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))
+
+# A body line, by what -m does with it (B.Rec.parts): Whole, judged as one
+# record (as without -m); Pieces, each record in ALT order; Unsplit, as
+# unsplit_in says.
+def body_in(pt: B.Parts, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) -> R.RunSt:
+  match pt:
+    case B.Whole{}:
+      R.body_line(judge(fa, B.Line.body(l)), st, o, l, at, inpos)
+    case B.Pieces{ps}:
+      pieces_in(ps, fa, o, st, B.Line.term(l), at, inpos)
+    case B.Unsplit{c}:
+      unsplit_in(judge(fa, B.Line.body(l)), c, o, st, l, at, inpos)
+
+def line_in(phase: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
   match phase:
     case False{}:
       R.head_line(R.is_chrom_line(B.Line.body(l)), st, o, l)
     case True{}:
       +fs = B.Rec.fields(B.Line.body(l))
       +at = {B.At{R.RunSt.n(st), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
-      R.body_line(judge(fa, B.Line.body(l)), st, o, l, at, B.Rec.pos(fs))
+      body_in(B.Rec.parts(defs, o, B.Line.body(l)), fa, o, st, l, at, B.Rec.pos(fs))
 
-def line_step.go(halted: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
+def line_step.go(halted: Bool, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
   match halted:
     case True{}:
       st
     case False{}:
-      line_in(R.RunSt.inbody(st), fa, o, R.tick(st), l)
+      line_in(R.RunSt.inbody(st), fa, defs, o, R.tick(st), l)
 
 # One more line of the file (nothing happens once the run has stopped).
-def line_step(+fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
-  line_step.go(R.RunSt.halt(st), fa, o, st, l)
+def line_step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line) -> R.RunSt:
+  line_step.go(R.RunSt.halt(st), fa, defs, o, st, l)
 
-def run.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, st: R.RunSt) -> R.RunSt:
+def run.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, st: R.RunSt) -> R.RunSt:
   match ls:
     case Nil{}:
       st
     case +l <> t:
-      run.go(t, fa, o, line_step(fa, o, st, l))
+      run.go(t, fa, defs, o, line_step(fa, defs, o, st, l))
+
+def defs.go(ls: List<&2, B.Line>, +done: Bool, +d: B.Defs) -> B.Defs:
+  match ls:
+    case Nil{}:
+      d
+    case +l <> t:
+      defs.go(t, done || R.is_chrom_line(B.Line.body(l)), Bool.pick(B.Defs, done, d, B.Defs.line(d, B.Line.body(l))))
+
+# The header's INFO and FORMAT definitions (B.Defs.line): those of the lines
+# before the #CHROM line.
+def defs(vcf: String) -> B.Defs:
+  defs.go(B.Text.lines(vcf), False{}, B.Defs{Nil{}, Nil{}})
 
 # The whole run, defined over the whole files. Line by line:
 #   - Header lines (up to the #CHROM line) are held, then written when the
 #     #CHROM line is read, with the two added lines just before it.
+#   - With -m, a body line with two or more ALTs is first split into one
+#     record per ALT (B.Rec.parts, reading the header's definitions); each
+#     record then goes through the rest of this rule in ALT order, as a line of
+#     its own with the line's number and input POS. A line that cannot be
+#     split (BAD_CR, ALT_DUP, UNDEFINED_TAG, BAD_COUNT, BAD_GT) is a problem, after
+#     any outcome of the whole line that stops the run (unsplit_in).
 #   - Each body line is judged (judge). If its outcome stops the run, the run
 #     stops without writing anything more. Else, if its CHROM differs from the
 #     current CHROM run, the whole buffer is written, and the run stops with
@@ -426,8 +495,8 @@
 #     whose key is below the last key written in this CHROM run stops the run
 #     with UNSORTED.
 #   - At the end of the file, the buffer is written.
-def run(fasta: String, vcf: String, o: B.Opts) -> R.Report:
-  R.finish(run.go(B.Text.lines(vcf), B.Fasta.parse(fasta), o, R.start_st()))
+def run(fasta: String, +vcf: String, o: B.Opts) -> R.Report:
+  R.finish(run.go(B.Text.lines(vcf), B.Fasta.parse(fasta), defs(vcf), o, R.start_st()))
 
 # ==========================================================================
 # Laws: what a run guarantees
@@ -445,6 +514,25 @@
   +fs = B.Rec.fields(B.Line.body(l))
   item_of(judge(fa, B.Line.body(l)), l, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
 
+def items.pieces(ps: List<&2, String>, +fa: List<&2, B.Contig>, +term: String, +n: Nat) -> List<&2, R.Item>:
+  match ps:
+    case Nil{}:
+      Nil{}
+    case +p <> t:
+      item(fa, B.Line{p, term}, n) <> items.pieces(t, fa, term, n)
+
+# The items a body line becomes: one (Whole), one per ALT in ALT order
+# (Pieces), or the line as it came (Unsplit, in a run that goes on: -c w).
+def items.line(pt: B.Parts, +fa: List<&2, B.Contig>, +l: B.Line, +n: Nat) -> List<&2, R.Item>:
+  match pt:
+    case B.Whole{}:
+      [item(fa, l, n)]
+    case B.Pieces{ps}:
+      items.pieces(ps, fa, B.Line.term(l), n)
+    case B.Unsplit{c}:
+      +fs = B.Rec.fields(B.Line.body(l))
+      [R.Item{B.Rec.pos(fs), B.Rec.pos(fs), B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Line.text(l)}]
+
 type ItSt is Data:
   ItSt{inbody: Bool, n: Nat, acc: List<&2, R.Item>}
 
@@ -473,6 +561,28 @@
 def items(fasta: String, vcf: String) -> List<&2, R.Item>:
   ItSt.acc(items.go(B.Text.lines(vcf), B.Fasta.parse(fasta), ItSt{False{}, 0n, Nil{}}))
 
+def out_items.step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, s: ItSt, +l: B.Line) -> ItSt:
+  match s:
+    case ItSt{i, +n, acc}:
+      match i:
+        case False{}:
+          ItSt{R.is_chrom_line(B.Line.body(l)), 1n+n, acc}
+        case True{}:
+          ItSt{True{}, 1n+n, List.append(&2, R.Item, acc, items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n))}
+
+def out_items.go(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, s: ItSt) -> ItSt:
+  match ls:
+    case Nil{}:
+      s
+    case +l <> t:
+      out_items.go(t, fa, defs, o, out_items.step(fa, defs, o, s, l))
+
+# The records a run writes as items, in input order: one per body line, or,
+# with -m, one per ALT of a split line, in ALT order. Without -m these are
+# items(fasta, vcf) (law items_without_m).
+def out_items(fasta: String, +vcf: String, o: B.Opts) -> List<&2, R.Item>:
+  ItSt.acc(out_items.go(B.Text.lines(vcf), B.Fasta.parse(fasta), defs(vcf), o, ItSt{False{}, 0n, Nil{}}))
+
 def head.step(done: Bool, +acc: String, +o: B.Opts, +l: B.Line) -> String:
   match done:
     case True{}:
@@ -562,14 +672,15 @@
       grouped.go(t, R.Item.chrom(x), Nil{})
 
 # Sorted output: a run that succeeds writes the header with the two added
-# lines, then the body lines grouped by CHROM (in input order) and, within each
-# CHROM, sorted by position, lines with equal positions in input order.
+# lines, then the records (the body lines, or with -m the records of split
+# lines) grouped by CHROM (in input order) and, within each CHROM, sorted by
+# position, records with equal positions in input order.
 law sorted:
   for fasta: String
   for vcf: String
   for o: B.Opts
   for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
-  {R.Report.out(run(fasta, vcf, o)) == head(vcf, o) ++ texts(gsort(items(fasta, vcf))) : String}
+  {R.Report.out(run(fasta, vcf, o)) == head(vcf, o) ++ texts(gsort(out_items(fasta, vcf, o))) : String}
 
 # A run that succeeds had each CHROM in one run (so the output is grouped too).
 law grouped_in:
@@ -577,7 +688,7 @@
   for vcf: String
   for o: B.Opts
   for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
-  {grouped(items(fasta, vcf)) == True{} : Bool}
+  {grouped(out_items(fasta, vcf, o)) == True{} : Bool}
 
 def ascending.go(xs: List<&2, R.Item>, +a: R.Item) -> Bool:
   match xs:
@@ -625,9 +736,9 @@
   for vcf: String
   for o: B.Opts
   for hw: {Nat.is_le(1n, R.Opts.w(o)) == True{} : Bool}
-  for hg: {grouped(items(fasta, vcf)) == True{} : Bool}
-  for ha: {ascending(items(fasta, vcf)) == True{} : Bool}
-  for hm: {small_moves(R.Opts.w(o), items(fasta, vcf)) == True{} : Bool}
+  for hg: {grouped(out_items(fasta, vcf, o)) == True{} : Bool}
+  for ha: {ascending(out_items(fasta, vcf, o)) == True{} : Bool}
+  for hm: {small_moves(R.Opts.w(o), out_items(fasta, vcf, o)) == True{} : Bool}
   {any_unsorted(R.Report.notes(run(fasta, vcf, o))) == False{} : Bool}
 
 def body.go(ls: List<&2, B.Line>, +inbody: Bool, +acc: String) -> String:
@@ -650,3 +761,734 @@
   for h: {R.Report.code(run(fasta, vcf, o)) == 0n : Nat}
   {(Nat.is_eq(R.Report.code(run(fasta, R.Report.out(run(fasta, vcf, o)), o)), 0n)
     && String.eq(body(R.Report.out(run(fasta, R.Report.out(run(fasta, vcf, o)), o))), body(R.Report.out(run(fasta, vcf, o))))) == True{} : Bool}
+
+# ==========================================================================
+# Definitions: splitting multiallelic records (-m)
+# ==========================================================================
+
+def alt_fields(ps: List<&2, String>) -> List<&2, String>:
+  match ps:
+    case Nil{}:
+      Nil{}
+    case p <> t:
+      B.Rec.field(B.Rec.fields(p), 4n) <> alt_fields(t)
+
+def same_fields(+fs: List<&2, String>, +gs: List<&2, String>, ks: List<&2, Nat>) -> Bool:
+  match ks:
+    case Nil{}:
+      True{}
+    case +k <> t:
+      String.eq(B.Rec.field(fs, k), B.Rec.field(gs, k)) && same_fields(fs, gs, t)
+
+# p has as many fields as fs and the same CHROM, POS, ID, REF, QUAL, FILTER
+# and FORMAT, byte for byte.
+def same_site(+fs: List<&2, String>, p: String) -> Bool:
+  +gs = B.Rec.fields(p)
+  Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)) && same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n])
+
+def all_same_site(+fs: List<&2, String>, ps: List<&2, String>) -> Bool:
+  match ps:
+    case Nil{}:
+      True{}
+    case p <> t:
+      same_site(fs, p) && all_same_site(fs, t)
+
+# The number of ALTs of a record.
+def n_alts(body: String) -> Nat:
+  List.length(&2, String, B.Rec.alts(B.Rec.fields(body)))
+
+# A record's INFO entries (separated by ';'), in order.
+def info_entries(body: String) -> List<&2, String>:
+  String.split(B.Rec.field(B.Rec.fields(body), 7n), ';')
+
+def info_keys.go(es: List<&2, String>) -> List<&2, String>:
+  match es:
+    case Nil{}:
+      Nil{}
+    case e <> t:
+      B.Info.key(e) <> info_keys.go(t)
+
+# The keys of a record's INFO entries, in order.
+def info_keys(body: String) -> List<&2, String>:
+  info_keys.go(info_entries(body))
+
+# The entry has a value: it has '=' ("key=values"; not a flag, not empty).
+def has_value(+e: String) -> Bool:
+  Nat.is_lt(String.length(B.Info.key(e)), String.length(e))
+
+# An entry's text after its first '='.
+def value_text(+e: String) -> String:
+  String.drop(e, Nat.add(String.length(B.Info.key(e)), 1n))
+
+# The values written in a value, separated by commas.
+def values(v: String) -> List<&2, String>:
+  String.split(v, ',')
+
+def entry_values(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
+  match m:
+    case None{}:
+      None{}
+    case Some{+e}:
+      Some{values(value_text(e))}
+
+def values_of(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
+  match m:
+    case None{}:
+      None{}
+    case Some{x}:
+      Some{values(x)}
+
+# The FORMAT keys of a record, in order.
+def format_keys(body: String) -> List<&2, String>:
+  String.split(B.Rec.field(B.Rec.fields(body), 8n), ':')
+
+def column_values(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
+  match m:
+    case None{}:
+      None{}
+    case Some{c}:
+      Some{String.split(c, ':')}
+
+# Sample s's column (0: the first sample), as its values; None when the line
+# has no such column.
+def sample_column(body: String, +s: Nat) -> Maybe<&2, List<&2, String>>:
+  column_values(List.get(&2, String, B.Rec.fields(body), Nat.add(9n, s)))
+
+def sample_at.of(m: Maybe<&2, List<&2, String>>, +j: Nat) -> Maybe<&2, String>:
+  match m:
+    case None{}:
+      None{}
+    case Some{vs}:
+      List.get(&2, String, vs, j)
+
+# Sample s's value for FORMAT's j-th key (0: the first); None when the line
+# has no such column, or the column is shorter.
+def sample_at(body: String, +s: Nat, +j: Nat) -> Maybe<&2, String>:
+  sample_at.of(sample_column(body, s), j)
+
+def len_of(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, Nat>:
+  match m:
+    case None{}:
+      None{}
+    case Some{vs}:
+      Some{List.length(&2, String, vs)}
+
+def copies_of(m: Maybe<&2, List<&2, String>>, +ks: List<&2, String>) -> Maybe<&2, Nat>:
+  match m:
+    case None{}:
+      Some{2n}
+    case Some{vs}:
+      B.Gt.copies(B.Fmt.gt(ks, vs))
+
+# How many copies sample s's GT says (B.Gt.copies: two without a GT value;
+# None, one or two by the count, for a lone '.').
+def sample_copies(+body: String, +s: Nat) -> Maybe<&2, Nat>:
+  copies_of(sample_column(body, s), format_keys(body))
+
+def gt_cut(xs: List<&2, String>) -> List<&2, String>:
+  match xs:
+    case Nil{}:
+      Nil{}
+    case x <> t:
+      List.append(&2, String, String.split(x, '|'), gt_cut(t))
+
+# The alleles of a genotype as written, in order (separated by '/' or '|').
+def gt_tokens(g: String) -> List<&2, String>:
+  gt_cut(String.split(g, '/'))
+
+def gt_read(+t: String) -> Maybe<&2, Nat>:
+  Bool.pick(Maybe<&2, Nat>, String.eq(t, "."), None{}, B.Pos.read(t))
+
+def gt_alleles.go(ts: List<&2, String>) -> List<&2, Maybe<&2, Nat>>:
+  match ts:
+    case Nil{}:
+      Nil{}
+    case t <> r:
+      gt_read(t) <> gt_alleles.go(r)
+
+# The alleles a genotype names, in order: a number (0 REF, 1, 2, ... the
+# ALTs), or None for '.' (missing).
+def gt_alleles(g: String) -> List<&2, Maybe<&2, Nat>>:
+  gt_alleles.go(gt_tokens(g))
+
+def gt_well.go(ts: List<&2, String>) -> Bool:
+  match ts:
+    case Nil{}:
+      True{}
+    case +t <> r:
+      (String.eq(t, ".") || B.Gt.canon(t)) && gt_well.go(r)
+
+# A genotype is written as VCF writes it: alleles separated by '/' or '|',
+# each '.' or a number without leading zeros.
+def gt_well(g: String) -> Bool:
+  gt_well.go(gt_tokens(g))
+
+def gt_view.if(ok: Bool, g: String) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
+  match ok:
+    case True{}:
+      Some{gt_alleles(g)}
+    case False{}:
+      None{}
+
+# A genotype value's alleles, if it is there and well written.
+def gt_view(m: Maybe<&2, String>) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
+  match m:
+    case None{}:
+      None{}
+    case Some{+g}:
+      gt_view.if(gt_well(g), g)
+
+def gt_seps.put(sep: Bool, h: Char, rest: String) -> String:
+  match sep:
+    case True{}:
+      SCon{h, rest}
+    case False{}:
+      rest
+
+# The separators of a genotype, in order ('/' unphased, '|' phased).
+def gt_seps(g: String) -> String:
+  match g:
+    case SNil{}:
+      SNil{}
+    case SCon{+h, t}:
+      gt_seps.put(B.Gt.is_sep(h), h, gt_seps(t))
+
+def seps_of(m: Maybe<&2, String>) -> Maybe<&2, String>:
+  match m:
+    case None{}:
+      None{}
+    case Some{g}:
+      Some{gt_seps(g)}
+
+def gt_rule_all(+over0: Bool, +i: Nat, xs: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
+  match xs:
+    case Nil{}:
+      Nil{}
+    case a <> t:
+      B.Gt.rule(over0, i, a) <> gt_rule_all(over0, i, t)
+
+# The value values vs give allele j (0 REF, 1 to n the ALTs): Number R, and G
+# of one copy, value j; Number A (no value for REF), value j - 1.
+def allele_value(num: B.Num, +vs: List<&2, String>, +j: Nat) -> Maybe<&2, String>:
+  match num:
+    case B.NumA{}:
+      Bool.pick(Maybe<&2, String>, Nat.is_eq(j, 0n), None{}, List.get(&2, String, vs, Nat.sub(j, 1n)))
+    case _:
+      List.get(&2, String, vs, j)
+
+# The value Number G values vs give genotype j/k (j <= k) of two copies (VCF
+# 4.3, section 1.6.2: value k(k+1)/2 + j).
+def genotype_value(+vs: List<&2, String>, +j: Nat, +k: Nat) -> Maybe<&2, String>:
+  List.get(&2, String, vs, Nat.add(Nat.div(Nat.mul(k, 1n+k), 2n), j))
+
+def somes(ms: List<&2, Maybe<&2, String>>) -> Maybe<&2, List<&2, String>>:
+  match ms:
+    case Nil{}:
+      Some{Nil{}}
+    case m <> t:
+      B.Vals.pick.cons(m, somes(t))
+
+# The values the record for ALT i gives a per-allele tag, from the input's
+# values vs, ALT i becoming the record's one ALT (allele 1), for ploidy p:
+#   A: the value of ALT i;
+#   R: the values of REF and of ALT i;
+#   G, one copy (p = 1): the values of REF and of ALT i;
+#   G, two copies: the values of genotypes REF/REF, REF/ALT i, ALT i/ALT i
+#     (0/0, 0/i, i/i), which become the record's 0/0, 0/1, 1/1.
+def lifted(num: B.Num, +p: Nat, +i: Nat, +vs: List<&2, String>) -> Maybe<&2, List<&2, String>>:
+  match num:
+    case B.NumA{}:
+      somes([allele_value(B.NumA{}, vs, i)])
+    case B.NumR{}:
+      somes([allele_value(B.NumR{}, vs, 0n), allele_value(B.NumR{}, vs, i)])
+    case B.NumG{}:
+      Bool.pick(Maybe<&2, List<&2, String>>, Nat.is_eq(p, 1n),
+        somes([allele_value(B.NumG{}, vs, 0n), allele_value(B.NumG{}, vs, i)]),
+        somes([genotype_value(vs, 0n, 0n), genotype_value(vs, 0n, i), genotype_value(vs, i, i)]))
+    case _:
+      Some{vs}
+
+def first_code.put(m: Maybe<&2, B.Code>, rest: Maybe<&2, B.Code>) -> Maybe<&2, B.Code>:
+  match m:
+    case Some{c}:
+      Some{c}
+    case None{}:
+      rest
+
+def first_code(ms: List<&2, Maybe<&2, B.Code>>) -> Maybe<&2, B.Code>:
+  match ms:
+    case Nil{}:
+      None{}
+    case m <> t:
+      first_code.put(m, first_code(t))
+
+# A per-allele value v is '.' or has the expected number of values for its
+# copies cp: expected_count(num, n, p), p the copies the sample's GT says,
+# and for a lone '.' GT either n + 1 (one copy) or (n+1)(n+2)/2 (two).
+def count_problem(num: B.Num, +n: Nat, cp: Maybe<&2, Nat>, +v: String) -> Maybe<&2, B.Code>:
+  +c = List.length(&2, String, values(v))
+  Bool.pick(Maybe<&2, B.Code>, String.eq(v, ".") || B.Vals.fits(B.Vals.expected_count(num, n, B.Vals.copies(cp, n, c)), c), None{}, Some{B.BadCount{}})
+
+def info_problem.of(m: Maybe<&2, B.Num>, +e: String, +n: Nat) -> Maybe<&2, B.Code>:
+  match m:
+    case None{}:
+      Some{B.UndefinedTag{"INFO/" ++ B.Info.key(e)}}
+    case Some{B.NumUnknown{}}:
+      Some{B.UndefinedTag{"INFO/" ++ B.Info.key(e)}}
+    case Some{B.NumOther{}}:
+      None{}
+    case Some{num}:
+      count_problem(num, n, Some{2n}, value_text(e))
+
+# What is wrong with an INFO entry, for a record with n ALTs: an entry
+# without a value (a flag, an empty entry) is fine unless its tag is A, R or
+# G (BAD_COUNT); an entry with a value whose tag the header does not define,
+# or defines with an Unknown Number, is UNDEFINED_TAG; an A, R or G value that
+# is not '.' and has not expected_count(Number, n, 2) values is BAD_COUNT.
+def info_problem(+m: Maybe<&2, B.Num>, +e: String, +n: Nat) -> Maybe<&2, B.Code>:
+  Bool.pick(Maybe<&2, B.Code>, has_value(e), info_problem.of(m, e, n),
+    Bool.pick(Maybe<&2, B.Code>, B.Num.per_allele(m), Some{B.BadCount{}}, None{}))
+
+def info_problems(es: List<&2, String>, +tags: List<&2, B.Tag>, +n: Nat) -> List<&2, Maybe<&2, B.Code>>:
+  match es:
+    case Nil{}:
+      Nil{}
+    case +e <> t:
+      info_problem(B.Tags.find(tags, B.Info.key(e)), e, n) <> info_problems(t, tags, n)
+
+def gt_ok.go(ts: List<&2, String>, +n: Nat) -> Bool:
+  match ts:
+    case Nil{}:
+      True{}
+    case +t <> r:
+      (String.eq(t, ".") || (B.Gt.canon(t) && Nat.is_le(Maybe.default(&2, Nat, B.Pos.read(t), 0n), n))) && gt_ok.go(r, n)
+
+# What is wrong with a genotype of a record with n ALTs: an allele that is
+# not '.' or a number from 0 to n without leading zeros is BAD_GT.
+def gt_problem(+n: Nat, g: String) -> Maybe<&2, B.Code>:
+  Bool.pick(Maybe<&2, B.Code>, gt_ok.go(gt_tokens(g), n), None{}, Some{B.BadGt{}})
+
+def format_problem(m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +p: Maybe<&2, Nat>) -> Maybe<&2, B.Code>:
+  match m:
+    case None{}:
+      Some{B.UndefinedTag{"FORMAT/" ++ k}}
+    case Some{B.NumUnknown{}}:
+      Some{B.UndefinedTag{"FORMAT/" ++ k}}
+    case Some{B.NumOther{}}:
+      None{}
+    case Some{num}:
+      count_problem(num, n, p, v)
+
+# What is wrong with one sample's values, read against the FORMAT keys, for
+# ploidy p: GT as gt_problem says; another key the header does not define,
+# or defines with an Unknown Number, is UNDEFINED_TAG; an A, R or G value
+# that is not '.' and has not expected_count(Number, n, p) values is
+# BAD_COUNT; a value with no key is BAD_COUNT.
+def sample_problems(ks: List<&2, String>, vs: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat, +p: Maybe<&2, Nat>) -> List<&2, Maybe<&2, B.Code>>:
+  match ks vs:
+    case _ Nil{}:
+      Nil{}
+    case Nil{} v <> t:
+      [Some{B.BadCount{}}]
+    case +k <> kt +v <> vt:
+      Bool.pick(Maybe<&2, B.Code>, String.eq(k, "GT"), gt_problem(n, v), format_problem(B.Tags.find(fmt, k), k, v, n, p))
+        <> sample_problems(kt, vt, fmt, n, p)
+
+def samples_problems(cols: List<&2, String>, +ks: List<&2, String>, +fmt: List<&2, B.Tag>, +n: Nat) -> List<&2, Maybe<&2, B.Code>>:
+  match cols:
+    case Nil{}:
+      Nil{}
+    case c <> t:
+      +vs = String.split(c, ':')
+      List.append(&2, Maybe<&2, B.Code>, sample_problems(ks, vs, fmt, n, B.Gt.copies(B.Fmt.gt(ks, vs))), samples_problems(t, ks, fmt, n))
+
+# Why a line cannot be split, the first reason reading it left to right; None
+# when it can be:
+#   ALT_DUP: two of its ALTs are equal (ignoring case);
+#   then its INFO entries, in order (info_problem);
+#   then its samples, in order, each value in FORMAT's order (sample_problems,
+#   the sample's copies from its GT, B.Gt.copies).
+def split_problem(+defs: B.Defs, +body: String) -> Maybe<&2, B.Code>:
+  +fs = B.Rec.fields(body)
+  +n = n_alts(body)
+  first_code(Bool.pick(Maybe<&2, B.Code>, B.Alts.distinct(B.Rec.alts(fs)), None{}, Some{B.DupAlts{}})
+    <> List.append(&2, Maybe<&2, B.Code>, info_problems(info_entries(body), B.Defs.info(defs), n),
+         samples_problems(List.drop(&2, String, fs, 9n), format_keys(body), B.Defs.fmt(defs), n)))
+
+# What B.Rec.parts says, as a refusal: Some{None} for Pieces, Some{Some{c}}
+# for Unsplit{c}, None for Whole.
+def refusal(pt: B.Parts) -> Maybe<&2, Maybe<&2, B.Code>>:
+  match pt:
+    case B.Whole{}:
+      None{}
+    case B.Pieces{ps}:
+      Some{None{}}
+    case B.Unsplit{c}:
+      Some{Some{c}}
+
+# The Number is Other (a count, '.', P).
+def is_other(m: Maybe<&2, B.Num>) -> Bool:
+  match m:
+    case Some{B.NumOther{}}:
+      True{}
+    case _:
+      False{}
+
+# The entry is copied whole by -m: it has no value (a flag, an empty entry,
+# INFO '.'), its value is '.', or its tag's Number is Other.
+def info_copied(+tags: List<&2, B.Tag>, +e: String) -> Bool:
+  Bool.not(has_value(e)) || String.eq(value_text(e), ".") || is_other(B.Tags.find(tags, B.Info.key(e)))
+
+# The value is copied by -m: it is '.', or its tag's Number is Other.
+def format_copied(+tags: List<&2, B.Tag>, +k: String, +v: String) -> Bool:
+  String.eq(v, ".") || is_other(B.Tags.find(tags, k))
+
+def per_allele_num(n: B.Num) -> Bool:
+  B.Num.per_allele(Some{n})
+
+def line_change.vars(r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +seq: List<&2, B.Base>, +pos: Nat) -> List<&2, List<&2, B.Base>>:
+  match r a:
+    case Some{ref} Some{alts}:
+      haps(seq, B.Var{pos, ref, alts})
+    case _ _:
+      Nil{}
+
+def line_change.contig(m: Maybe<&2, String>, +fs: List<&2, String>) -> List<&2, List<&2, B.Base>>:
+  match m:
+    case None{}:
+      Nil{}
+    case Some{raw}:
+      line_change.vars(B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), B.Bases.of_fasta(raw), B.Rec.pos(fs))
+
+# The change a record makes, read from its text: the contig after each of its
+# ALTs (haps), in order; nothing when it cannot be read as a variant.
+def line_change(+fa: List<&2, B.Contig>, body: String) -> List<&2, List<&2, B.Base>>:
+  +fs = B.Rec.fields(body)
+  line_change.contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs)
+
+def res_text(r: B.Res) -> String:
+  match r:
+    case B.Res{o, k, t, s}:
+      t
+
+# The text judge gives a record: what the run writes for it when its outcome
+# does not stop the run (normalized, or as it came; the item's text in
+# out_items, without the terminator).
+def written(+fa: List<&2, B.Contig>, p: String) -> String:
+  res_text(judge(fa, p))
+
+def one_of(m: Maybe<&2, List<&2, B.Base>>) -> List<&2, List<&2, B.Base>>:
+  match m:
+    case None{}:
+      Nil{}
+    case Some{x}:
+      [x]
+
+def all_line_valid(+fa: List<&2, B.Contig>, ps: List<&2, String>) -> Bool:
+  match ps:
+    case Nil{}:
+      True{}
+    case p <> t:
+      line_valid(fa, p) && all_line_valid(fa, t)
+
+def all_normalized(+fa: List<&2, B.Contig>, ps: List<&2, String>) -> Bool:
+  match ps:
+    case Nil{}:
+      True{}
+    case p <> t:
+      is_normalized(judge(fa, p)) && all_normalized(fa, t)
+
+def biallelic.go(ls: List<&2, B.Line>, +inbody: Bool) -> Bool:
+  match ls:
+    case Nil{}:
+      True{}
+    case +l <> t:
+      (Bool.not(inbody) || Nat.is_lt(n_alts(B.Line.body(l)), 2n)) && biallelic.go(t, inbody || R.is_chrom_line(B.Line.body(l)))
+
+# No body line has two or more ALTs.
+def biallelic(vcf: String) -> Bool:
+  biallelic.go(B.Text.lines(vcf), False{})
+
+# The options o without -m (everything else, the recorded arguments too,
+# kept).
+def no_m(o: B.Opts) -> B.Opts:
+  match o:
+    case B.Opts{s, w, m, z, a}:
+      B.Opts{s, w, False{}, z, a}
+
+# ==========================================================================
+# Laws: splitting multiallelic records (-m)
+# ==========================================================================
+
+# Without -m, every line is one record, handled as before -m existed.
+law whole_without_m:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for h: {R.Opts.split(o) == False{} : Bool}
+  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}
+
+# Without -m, the records written are the body lines, as before -m existed:
+# so sorted, grouped_in and no_unsorted say, without -m, what they said
+# before.
+law items_without_m:
+  for fasta: String
+  for vcf: String
+  for o: B.Opts
+  for h: {R.Opts.split(o) == False{} : Bool}
+  {out_items(fasta, vcf, o) == items(fasta, vcf) : List<&2, R.Item>}
+
+# With -m, a record with one ALT is handled as without -m.
+law whole_biallelic:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for h: {Nat.is_lt(n_alts(body), 2n) == True{} : Bool}
+  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}
+
+# A MALFORMED line is handled as without -m (it stops the run, MALFORMED).
+law whole_malformed:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for h: {B.Rec.malformed(B.Rec.fields(body)) == True{} : Bool}
+  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}
+
+# On a file whose body lines have one ALT each, -m changes nothing but the
+# arguments recorded in the header (no_m keeps them): the same output,
+# messages and exit code.
+law biallelic_run:
+  for fasta: String
+  for vcf: String
+  for o: B.Opts
+  for h: {biallelic(vcf) == True{} : Bool}
+  {run(fasta, vcf, o) == run(fasta, vcf, no_m(o)) : R.Report}
+
+# Which lines split: with -m, a line that is not MALFORMED and has two or
+# more ALTs is split exactly when split_problem finds nothing wrong with it,
+# and refused with exactly the code split_problem gives otherwise.
+law split_when:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for hs: {R.Opts.split(o) == True{} : Bool}
+  for hm: {B.Rec.malformed(B.Rec.fields(body)) == False{} : Bool}
+  for hn: {Nat.is_le(2n, n_alts(body)) == True{} : Bool}
+  {refusal(B.Rec.parts(defs, o, body)) == Some{split_problem(defs, body)} : Maybe<&2, Maybe<&2, B.Code>>}
+
+# One record per ALT: the records' ALT fields are the input's ALTs, one each,
+# in the input's order.
+law split_alts:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  {alt_fields(ps) == B.Rec.alts(B.Rec.fields(body)) : List<&2, String>}
+
+# Each record keeps the input's CHROM, POS, ID, REF, QUAL, FILTER and FORMAT,
+# and its number of fields (so its samples).
+law split_site:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  {all_same_site(B.Rec.fields(body), ps) == True{} : Bool}
+
+# If the line describes a valid variant on its contig, so does each record
+# (the line's POS and REF with one of its ALTs): so the laws of the normal
+# form, same_change ... unique, apply to each.
+law split_valid:
+  for fa: List<&2, B.Contig>
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for hv: {line_valid(fa, body) == True{} : Bool}
+  {all_line_valid(fa, ps) == True{} : Bool}
+
+# If the whole line would be normalized (no problem), every record is.
+law split_normalized:
+  for fa: List<&2, B.Contig>
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for hn: {is_normalized(judge(fa, body)) == True{} : Bool}
+  {all_normalized(fa, ps) == True{} : Bool}
+
+# The record for ALT i+1, as written (its outcome does not stop the run:
+# normalized, or passed as it came), read back as a variant on the
+# reference, makes exactly the change of the line's ALT i+1: the contig after
+# that ALT. (The records' order in the output is the sorted one, law sorted;
+# this law pairs each record with its ALT.)
+law split_change:
+  for fa: List<&2, B.Contig>
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for hv: {line_valid(fa, body) == True{} : Bool}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for hs: {stops(judge(fa, p), R.Opts.strict(o)) == False{} : Bool}
+  {line_change(fa, written(fa, p)) == one_of(List.get(&2, List<&2, B.Base>, line_change(fa, body), i)) : List<&2, List<&2, B.Base>>}
+
+# Genotypes: in the record for ALT i+1, every GT value of every sample (s,
+# j: the sample and the FORMAT key's place) is well written and names, copy
+# by copy, B.Gt.rule's allele for the one the input named there: REF stays
+# REF; ALT i+1 becomes the record's ALT (1); another ALT becomes REF
+# (--multi-overlaps 0) or missing (--multi-overlaps .); missing stays
+# missing.
+law split_gt:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for s: Nat
+  for j: Nat
+  for hk: {List.get(&2, String, format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
+  for g: String
+  for hg: {sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
+  {gt_view(sample_at(p, s, j)) == Some{gt_rule_all(R.Opts.over0(o), 1n+i, gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}
+
+# ... and keeps the input's separators, so its phasing and ploidy.
+law split_phase:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for s: Nat
+  for j: Nat
+  for hk: {List.get(&2, String, format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
+  for g: String
+  for hg: {sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
+  {seps_of(sample_at(p, s, j)) == Some{gt_seps(g)} : Maybe<&2, String>}
+
+# INFO: each record has the input's INFO keys, in order (so as many entries).
+law split_info_keys:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  {info_keys(p) == info_keys(body) : List<&2, String>}
+
+# Every INFO entry (e: its place) whose tag is A, R or G and whose value is
+# not '.' gives, in the record for ALT i+1, exactly the values of that
+# record's alleles (lifted; split_when says the input had exactly
+# expected_count values).
+law split_info_values:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for e: Nat
+  for x: String
+  for hx: {List.get(&2, String, info_entries(body), e) == Some{x} : Maybe<&2, String>}
+  for num: B.Num
+  for hk: {B.Tags.find(B.Defs.info(defs), B.Info.key(x)) == Some{num} : Maybe<&2, B.Num>}
+  for ha: {per_allele_num(num) == True{} : Bool}
+  for hv: {has_value(x) == True{} : Bool}
+  for hm: {String.eq(value_text(x), ".") == False{} : Bool}
+  {entry_values(List.get(&2, String, info_entries(p), e)) == lifted(num, 2n, 1n+i, values(value_text(x))) : Maybe<&2, List<&2, String>>}
+
+# Every other INFO entry is copied by the split, byte for byte: a flag, an
+# empty entry, a value '.', a tag of Number Other. (judge then rewrites END
+# for a record normalization moves, by the END rule, as without -m.)
+law split_info_kept:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for e: Nat
+  for x: String
+  for hx: {List.get(&2, String, info_entries(body), e) == Some{x} : Maybe<&2, String>}
+  for hc: {info_copied(B.Defs.info(defs), x) == True{} : Bool}
+  {List.get(&2, String, info_entries(p), e) == Some{x} : Maybe<&2, String>}
+
+# FORMAT: each sample has as many values as in the input (none when the line
+# has no such column).
+law split_format_shape:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for s: Nat
+  {len_of(sample_column(p, s)) == len_of(sample_column(body, s)) : Maybe<&2, Nat>}
+
+# Every FORMAT value (other than GT) whose tag is A, R or G and that is not
+# '.' gives, in the record for ALT i+1, exactly the values of that record's
+# alleles (lifted), for the copies its sample's GT names: G of one copy gives
+# REF's and ALT i+1's values; G of two copies (or no GT value) the three
+# genotype values; a lone '.' GT, one or two copies as its count says.
+law split_format_values:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for s: Nat
+  for j: Nat
+  for k: String
+  for hk: {List.get(&2, String, format_keys(body), j) == Some{k} : Maybe<&2, String>}
+  for hgt: {String.eq(k, "GT") == False{} : Bool}
+  for num: B.Num
+  for hn: {B.Tags.find(B.Defs.fmt(defs), k) == Some{num} : Maybe<&2, B.Num>}
+  for ha: {per_allele_num(num) == True{} : Bool}
+  for v: String
+  for hv: {sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
+  for hm: {String.eq(v, ".") == False{} : Bool}
+  {values_of(sample_at(p, s, j)) == lifted(num, B.Vals.copies(sample_copies(body, s), n_alts(body), List.length(&2, String, values(v))), 1n+i, values(v)) : Maybe<&2, List<&2, String>>}
+
+# Every other FORMAT value (other than GT) is copied byte for byte: a value
+# '.', a tag of Number Other.
+law split_format_kept:
+  for defs: B.Defs
+  for o: B.Opts
+  for body: String
+  for ps: List<&2, String>
+  for h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
+  for i: Nat
+  for p: String
+  for hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
+  for s: Nat
+  for j: Nat
+  for k: String
+  for hk: {List.get(&2, String, format_keys(body), j) == Some{k} : Maybe<&2, String>}
+  for hgt: {String.eq(k, "GT") == False{} : Bool}
+  for v: String
+  for hv: {sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
+  for hc: {format_copied(B.Defs.fmt(defs), k, v) == True{} : Bool}
+  {sample_at(p, s, j) == Some{v} : Maybe<&2, String>}
```

## Appendix B: the examples

`data/tmp/split/draft/ex_split.bend`, written by `data/tmp/split/gen_ex.py` and checked with
`test/bcheck.sh`: all 107 evaluate (only the 32 imported laws are TODO), and a deliberately
wrong one is reported.

- `ex_*` on `B.Rec.parts`: expected values from bcftools 1.24 (`bcftools norm -m -any` without
  `-f`, before normalization) where the design agrees with it, and as the differences table
  says elsewhere.
- `when_*`: law `split_when` on every case (`refusal(parts) == Some{split_problem}`).
- `ex_run*`, `ex_render*`, `ex_biallelic_run`, `ex_items_without_m`, `ex_split_change*`,
  `ex_written_moves`: whole runs, messages, and the run-level laws on one file. `ex_run` writes
  bcftools' records (with `-f`).

```
import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R

# Draft -m examples, round 3: B.Rec.parts against bcftools 1.24 (data/tmp/split),
# and split_problem against B.Rec.parts on every case (law split_when).

def defs() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n")

def defs2() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##INFO=<ID=TA, Number=A, Type=Integer,Description=\"space after commas\">\n##INFO=<ID=TB,Number=A ,Type=Integer,Description=\"space before a comma\">\n##INFO=<ID=TC ,Number=A,Type=Integer,Description=\"space after the ID\">\n##INFO=<ID=TD,Number= A,Type=Integer,Description=\"space after =\">\n##INFO=<ID=TE,Number=A,Type=Integer,Description=\"x, y\" >\n##INFO=<ID=TG,Number=A\t,Type=Integer,Description=\"a tab\">\n##INFO=<ID=TP,Number=P,Type=String,Description=\"per copy\">\n##INFO=<ID=TF,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=NN,Type=String,Description=\"no Number\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=LAA,Number=.,Type=Integer,Description=\"local alleles\">\n##FORMAT=<ID=LAD,Number=LR,Type=Integer,Description=\"local depths\">\n")

def defs3() -> B.Defs:
  L.defs("##fileformat=VCFv4.2\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n")

def m(o: Bool) -> B.Opts:
  B.Opts{True{}, 1000n, True{}, o, ["-m", "-any"]}

def ex_gt_ref() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT\t1/0\t0/0\t0/0\t1|0\t0|1\t0\t1\t0\t.\t./.\t.|.\t1/.\t./0\t.|0\t0/0\t1/1\t1/0/0\t0/0/0\t0/1\t1/0\t0/0\t0|0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT\t0/1\t0/1\t1/1\t0|1\t1|0\t1\t0\t0\t.\t./.\t.|.\t0/.\t./1\t.|1\t0/0\t0/0\t0/1/1\t0/0/0\t1/0\t0/0\t0/0\t0|0", "c1\t25\t.\tC\tA\t.\t.\t.\tGT\t0/0\t0/0\t0/0\t0|0\t0|0\t0\t0\t0\t.\t./.\t.|.\t0/.\t./0\t.|0\t0/0\t0/0\t0/0/0\t0/0/1\t0/0\t0/1\t1/1\t0|0"]} : B.Parts}:
  {==}

def when_gt_ref() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_gt_dot() -> {B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT\t1/.\t0/.\t./.\t1|.\t.|1\t.\t1\t0\t.\t./.\t.|.\t1/.\t./.\t.|.\t0/0\t1/1\t1/./.\t0/0/.\t./1\t1/.\t./.\t0|0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT\t./1\t0/1\t1/1\t.|1\t1|.\t1\t.\t0\t.\t./.\t.|.\t./.\t./1\t.|1\t0/0\t./.\t./1/1\t0/0/.\t1/.\t./.\t./.\t0|0", "c1\t25\t.\tC\tA\t.\t.\t.\tGT\t./.\t0/.\t./.\t.|.\t.|.\t.\t.\t0\t.\t./.\t.|.\t./.\t./.\t.|.\t0/0\t./.\t././.\t0/0/1\t./.\t./1\t1/1\t0|0"]} : B.Parts}:
  {==}

def when_gt_dot() -> {L.refusal(B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T,A\t.\t.\t.\tGT\t1/2\t0/2\t2/2\t1|2\t2|1\t2\t1\t0\t.\t./.\t.|.\t1/.\t./2\t.|2\t0/0\t1/1\t1/2/2\t0/0/3\t2/1\t1/3\t3/3\t0|0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info0() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=1;FA=0.1;SA=x;IR=10,11;SR=r,a;IG=0,1,2;SG=g0,g1,g2;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL", "c1\t25\t.\tC\tT\t.\t.\tIA=2;FA=0.0025;SA=y;IR=10,12;SR=r,b;IG=0,3,5;SG=g0,g3,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL"]} : B.Parts}:
  {==}

def when_info0() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;FA=0.1,0.0025;SA=x,y;IR=10,11,12;SR=r,a,b;IG=0,1,2,3,4,5;SG=g0,g1,g2,g3,g4,g5;I1=7;I2=8,9;ID_=1,2,3,4;S1=hello;FL")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info1() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c") == B.Pieces{["c1\t26\trs7\tG\tA\t9\tq10\tIA=1;FA=.;SA=x;IR=.,1;SR=r,.", "c1\t26\trs7\tG\tC\t9\tq10\tIA=.;FA=0.333333;SA=.;IR=.,2;SR=r,b", "c1\t26\trs7\tG\tT\t9\tq10\tIA=3;FA=1e+10;SA=z;IR=.,3;SR=r,c"]} : B.Parts}:
  {==}

def when_info1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c")) == Some{L.split_problem(defs(), "c1\t26\trs7\tG\tA,C,T\t9\tq10\tIA=1,.,3;FA=.,0.333333,1e+10;SA=x,.,z;IR=.,1,2,3;SR=r,.,b,c")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_info2() -> {B.Rec.parts(defs(), m(True{}), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28") == B.Pieces{["c1\t28\t.\tA\tC\t.\t.\tFA=0.123457;IR=1,2;IG=1,2,3;END=28", "c1\t28\t.\tA\tG\t.\t.\tFA=1;IR=1,3;IG=1,4,6;END=28"]} : B.Parts}:
  {==}

def when_info2() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28")) == Some{L.split_problem(defs(), "c1\t28\t.\tA\tC,G\t.\t.\tFA=0.123457,1;IR=1,2,3;IG=1,2,3,4,5,6;END=28")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_fmt0() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/0:1,2:0,1,2:0.10:9:4,5\t0:4,5:7,8:.:.:.\t./.:.:.:.:.:.\t0/1:7,.:.,1,2:1:3\t0/0", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t0/1:1,3:0,3,5:0.2:9:4,5\t1:4,6:7,9:1e10:.:.\t./.:.:.:.:.:.\t0/0:7,9:.,3,5:.:3\t0/0"]} : B.Parts}:
  {==}

def when_fmt0() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD:PL:FA:DP:F2\t1/2:1,2,3:0,1,2,3,4,5:0.10,0.2:9:4,5\t2:4,5,6:7,8,9:.,1e10:.:.\t./.:.:.:.:.:.\t0/1:7,.,9:.,1,2,3,4,5:1,.:3\t0/0")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_fmt1() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1") == B.Pieces{["c1\t26\t.\tG\tA\t.\t.\t.\tGT:SA:SR:SG\t1/0:a:r,a:0,1,2\t0:x:r,x:h0,h1\t.:.:.:.\t0/1:p:.,1:.\t1", "c1\t26\t.\tG\tC\t.\t.\t.\tGT:SA:SR:SG\t0/0:b:r,b:0,3,5\t1:y:r,y:h0,h2\t.:.:.:.\t0/0:.:.,.:.\t0", "c1\t26\t.\tG\tT\t.\t.\t.\tGT:SA:SR:SG\t0/1:c:r,c:0,6,9\t0:z:r,z:h0,h3\t.:.:.:.\t0/0:q:.,3:.\t0"]} : B.Parts}:
  {==}

def when_fmt1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1")) == Some{L.split_problem(defs(), "c1\t26\t.\tG\tA,C,T\t.\t.\t.\tGT:SA:SR:SG\t1/3:a,b,c:r,a,b,c:0,1,2,3,4,5,6,7,8,9\t2:x,y,z:r,x,y,z:h0,h1,h2,h3\t.:.:.:.\t0/1:p,.,q:.,1,.,3:.\t1")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_order() -> {B.Rec.parts(defs(), m(True{}), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2") == B.Pieces{["c1\t20\tx\tG\tA\t.\t.\t.\tAD:GT\t1,2:1/0", "c1\t20\tx\tG\tC\t.\t.\t.\tAD:GT\t1,3:0/1"]} : B.Parts}:
  {==}

def when_order() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2")) == Some{L.split_problem(defs(), "c1\t20\tx\tG\tA,C\t.\t.\t.\tAD:GT\t1,2,3:1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_lone_dot() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/0:.:.", "c1\t25\t.\tC\tT\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t0/1:.:."]} : B.Parts}:
  {==}

def when_lone_dot() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=.;IR=.;IG=.\tGT:AD:PL\t1/2:.:.")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_bi() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1") == B.Whole{} : B.Parts}:
  {==}

def ex_mal() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,,T\t.\t.\t.") == B.Whole{} : B.Parts}:
  {==}

def ex_u_flag() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tXY;IA=1", "c1\t25\t.\tC\tT\t.\t.\tXY;IA=2"]} : B.Parts}:
  {==}

def when_u_flag() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tXY;IA=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_empty1() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tIA=1;", "c1\t25\t.\tC\tT\t.\t.\tIA=2;"]} : B.Parts}:
  {==}

def when_empty1() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2;")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_empty2() -> {B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4") == B.Pieces{["c1\t26\t.\tG\tA\t.\t.\t;IA=1;;I1=4", "c1\t26\t.\tG\tT\t.\t.\t;IA=2;;I1=4"]} : B.Parts}:
  {==}

def when_empty2() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4")) == Some{L.split_problem(defs(), "c1\t26\t.\tG\tA,T\t.\t.\t;IA=1,2;;I1=4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_nogt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tDP:PL\t3:0,1,2", "c1\t25\t.\tC\tT\t.\t.\t.\tDP:PL\t3:0,3,5"]} : B.Parts}:
  {==}

def when_pl_nogt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tDP:PL\t3:0,1,2,3,4,5")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dotgt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:0,1,2\t1:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t.:0,3,5\t0:7,9"]} : B.Parts}:
  {==}

def when_pl_dotgt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:0,1,2,3,4,5\t1:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dot_hap() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t.:7,9"]} : B.Parts}:
  {==}

def when_pl_dot_hap() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_hap_dot_over() -> {B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:PL\t.:7,8", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:PL\t1:7,9"]} : B.Parts}:
  {==}

def when_hap_dot_over() -> {L.refusal(B.Rec.parts(defs(), m(False{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t2:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_gtafter() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tPL:GT\t7,8:0", "c1\t25\t.\tC\tT\t.\t.\t.\tPL:GT\t7,9:1"]} : B.Parts}:
  {==}

def when_pl_gtafter() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tPL:GT\t7,8,9:2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_altref() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2") == B.Pieces{["c1\t12\t.\tA\tC\t.\t.\t.\tGT\t1/0", "c1\t12\t.\tA\tA\t.\t.\t.\tGT\t0/1"]} : B.Parts}:
  {==}

def when_altref() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tC,A\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_nogtdef() -> {B.Rec.parts(defs3(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\t.\tGT:AD\t1/0:1,2", "c1\t25\t.\tC\tT\t.\t.\t.\tGT:AD\t0/1:1,3"]} : B.Parts}:
  {==}

def when_nogtdef() -> {L.refusal(B.Rec.parts(defs3(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3")) == Some{L.split_problem(defs3(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:1,2,3")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_trim() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2") == B.Pieces{["c1\t25\t.\tC\tG\t.\t.\tTA=1;TB=3;TC=5;TD=7;TP=a,b;TF;TE=9\tGT:LAA\t1/0:1,2", "c1\t25\t.\tC\tT\t.\t.\tTA=2;TB=4;TC=6;TD=8;TP=a,b;TF;TE=10\tGT:LAA\t0/1:1,2"]} : B.Parts}:
  {==}

def when_trim() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tTA=1,2;TB=3,4;TC=5,6;TD=7,8;TP=a,b;TF;TE=9,10\tGT:LAA\t1/2:1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_info() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2") == B.Unsplit{B.UndefinedTag{"INFO/XX"}} : B.Parts}:
  {==}

def when_u_info() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tXX=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_fmt() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2") == B.Unsplit{B.UndefinedTag{"FORMAT/ZZ"}} : B.Parts}:
  {==}

def when_u_fmt() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:ZZ\t1/2:1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_tab() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2") == B.Unsplit{B.UndefinedTag{"INFO/TG"}} : B.Parts}:
  {==}

def when_u_tab() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tTG=1,2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_nonum() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b") == B.Unsplit{B.UndefinedTag{"INFO/NN"}} : B.Parts}:
  {==}

def when_u_nonum() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\tNN=a,b")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_u_lr() -> {B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7") == B.Unsplit{B.UndefinedTag{"FORMAT/LAD"}} : B.Parts}:
  {==}

def when_u_lr() -> {L.refusal(B.Rec.parts(defs2(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7")) == Some{L.split_problem(defs2(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:LAD\t1/2:5,6,7")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ia() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ia() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ia3() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ia3() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1,2,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_sa() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_sa() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tSA=x")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_key() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_key() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_ad() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_ad() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:AD\t1/2:5\t0/1:6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl4() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl4() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1/2:1,2,3,4\t0/1:1,2,3,4,5,6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_dip3() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_dip3() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/2:7,8,9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_hap6() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_hap6() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t1:1,2,3,4,5,6")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_pl_trip() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_pl_trip() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t0/1/2:1,2,3,4,5,6,7,8,9,10")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_c_more() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_c_more() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/2:5")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_hi() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_hi() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_x() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_x() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t1/x")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_lead() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_lead() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t|1|2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_zero() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_zero() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t01/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_g_plus() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2") == B.Unsplit{B.BadGt{}} : B.Parts}:
  {==}

def when_g_plus() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT\t+1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup_case() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup_case() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\tc,C\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_dup_sym() -> {B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2") == B.Unsplit{B.DupAlts{}} : B.Parts}:
  {==}

def when_dup_sym() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2")) == Some{L.split_problem(defs(), "c1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_pl_dot_bad() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_pl_dot_bad() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\t.\tGT:PL\t.:1,2,3,4")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

def ex_order_code() -> {B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9") == B.Unsplit{B.BadCount{}} : B.Parts}:
  {==}

def when_order_code() -> {L.refusal(B.Rec.parts(defs(), m(True{}), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9")) == Some{L.split_problem(defs(), "c1\t25\t.\tC\tG,T\t.\t.\tIA=1;XX=2\t.\tGT\t1/9")} : Maybe<&2, Maybe<&2, B.Code>>}:
  {==}

# A whole run with -m: split, each record normalized, then sorted (bcftools 1.24 writes the same records).
def ex_run() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", m(True{})) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t8\trs1\tTCA\tT\t50\tPASS\tI1=7\tGT\t1/0\nc1\t8\trs1\tT\tTCA\t50\tPASS\tI1=7\tGT\t0/1\nc1\t15\trs2;rs3\tCAG\tC\t.\tq10\t.\tGT\t1|0\nc1\t16\trs2;rs3\tA\tT\t.\tq10\t.\tGT\t0|1\nc1\t21\t.\tT\tA\t3.5\t.\tFL\tGT\t0/0\nc1\t21\t.\tT\tC\t3.5\t.\tFL\tGT\t0/0\nc1\t21\t.\tT\tG\t3.5\t.\tFL\tGT\t0/1\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", [B.Summary{8n, 3n, 0n, 0n}], 0n} : R.Report}:
  {==}

# Under -c w a line that cannot be split passes as it came, with a warning naming the tag.
def ex_run_unsplit_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", [B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# Under -c e it stops the run.
def ex_run_unsplit_e() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{True{}, 1000n, True{}, True{}, ["-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.UndefinedTag{"INFO/XX"}, Some{B.At{28n, "c1", "25"}}, None{}}], 1n} : R.Report}:
  {==}

# A line that cannot be split and whose CHROM is not in the reference stops with UNKNOWN_CHROM under -c w too, as without -m (item 7).
def ex_run_unknown_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nzz\t25\t.\tC\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.UnknownChrom{}, Some{B.At{28n, "zz", "25"}}, None{}}], 1n} : R.Report}:
  {==}

# Two equal ALTs: ALT_DUP, as without -m (item 8).
def ex_run_dup_e() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\tC,C\t.\t.\t.\tGT\t1/2\n", B.Opts{True{}, 1000n, True{}, True{}, ["-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n", [B.Stop{B.AltDup{}, Some{B.At{28n, "c1", "12"}}, None{}}], 1n} : R.Report}:
  {==}

# Two equal symbolic ALTs: out of scope without -m, but -m cannot split them (decision 20): under -c w, ALT_DUP, not split.
def ex_run_dup_sym_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\t.\tA\t<*>,<*>\t.\t.\t.\tGT\t1/2\n", [B.Warning{B.DupAlts{}, B.At{28n, "c1", "12"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# A split refused for two equal ALTs says it was not split; judge's ALT_DUP (no -m) is unchanged.
def ex_render_dup() -> {B.Note.render(B.Warning{B.DupAlts{}, B.At{28n, "c1", "12"}}) == "ALT_DUP\tc1\t12\tline 28\tnot split\n" : String}:
  {==}

# Under -c w, a line that cannot be split and whose REF does not match reports only the split code (decision 22, documented).
def ex_run_unsplit_mismatch_w() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tA\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", B.Opts{False{}, 1000n, True{}, True{}, ["-c", "w", "-m", "-any"]}) == R.Report{"##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n##framebender_normVersion=0.1.0\n##framebender_normCommand=norm -c w -m -any\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tA\tG,T\t.\t.\tXX=1,2\tGT\t1/2\n", [B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}, B.Summary{1n, 0n, 0n, 1n}], 0n} : R.Report}:
  {==}

# The warning names the tag and the fix.
def ex_render() -> {B.Note.render(B.Warning{B.UndefinedTag{"INFO/XX"}, B.At{28n, "c1", "25"}}) == "UNDEFINED_TAG\tc1\t25\tline 28\tINFO/XX has no usable header line (add one, e.g. with bcftools annotate -h); not split\n" : String}:
  {==}

# Messages of the other codes are as before.
def ex_render_old() -> {B.Note.render(B.Warning{B.RefMismatch{}, B.At{28n, "c1", "25"}}) == "REF_MISMATCH\tc1\t25\tline 28\n" : String}:
  {==}

# Law biallelic_run on one file.
def ex_biallelic_run() -> {L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1\nc1\t12\t.\tACA\tA\t.\t.\t.\tGT\t1/1\n", m(True{})) == L.run(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t25\t.\tC\tG\t.\t.\tIA=1\tGT\t0/1\nc1\t12\t.\tACA\tA\t.\t.\t.\tGT\t1/1\n", L.no_m(m(True{}))) : R.Report}:
  {==}

# Law items_without_m on one file.
def ex_items_without_m() -> {L.out_items(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n", L.no_m(m(True{}))) == L.items(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n", "##fileformat=VCFv4.2\n##contig=<ID=c1,length=60>\n##contig=<ID=c2,length=47>\n##FILTER=<ID=q10,Description=\"low\">\n##INFO=<ID=IA,Number=A,Type=Integer,Description=\"int per alt\">\n##INFO=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##INFO=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##INFO=<ID=IR,Number=R,Type=Integer,Description=\"int per allele\">\n##INFO=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##INFO=<ID=IG,Number=G,Type=Integer,Description=\"int per genotype\">\n##INFO=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##INFO=<ID=I1,Number=1,Type=Integer,Description=\"one int\">\n##INFO=<ID=I2,Number=2,Type=Integer,Description=\"two ints\">\n##INFO=<ID=ID_,Number=.,Type=Integer,Description=\"any ints\">\n##INFO=<ID=S1,Number=1,Type=String,Description=\"one string\">\n##INFO=<ID=FL,Number=0,Type=Flag,Description=\"flag\">\n##INFO=<ID=END,Number=1,Type=Integer,Description=\"end\">\n##FORMAT=<ID=GT,Number=1,Type=String,Description=\"Genotype\">\n##FORMAT=<ID=AD,Number=R,Type=Integer,Description=\"depths\">\n##FORMAT=<ID=PL,Number=G,Type=Integer,Description=\"likelihoods\">\n##FORMAT=<ID=FA,Number=A,Type=Float,Description=\"float per alt\">\n##FORMAT=<ID=SA,Number=A,Type=String,Description=\"string per alt\">\n##FORMAT=<ID=SR,Number=R,Type=String,Description=\"string per allele\">\n##FORMAT=<ID=SG,Number=G,Type=String,Description=\"string per genotype\">\n##FORMAT=<ID=DP,Number=1,Type=Integer,Description=\"depth\">\n##FORMAT=<ID=F2,Number=2,Type=Integer,Description=\"two ints\">\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\nc1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2\nc1\t15\trs2;rs3\tCAG\tCTG,C\t.\tq10\t.\tGT\t2|1\nc1\t21\t.\tT\tA,C,G\t3.5\t.\tFL\tGT\t0/3\nc1\t25\t.\tC\tG\t.\t.\t.\tGT\t0/1\n") : List<&2, R.Item>}:
  {==}

# Law split_change for ALT 1: the record written (moved to 8, TCA T) makes ALT 1's change.
def ex_split_change1() -> {L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA\t50\tPASS\tI1=7\tGT\t1/0")) == L.one_of(List.get(&2, List<&2, B.Base>, L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2"), 0n)) : List<&2, List<&2, B.Base>>}:
  {==}

# Law split_change for ALT 2 (T TCA at 8).
def ex_split_change2() -> {L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tACACA\t50\tPASS\tI1=7\tGT\t0/1")) == L.one_of(List.get(&2, List<&2, B.Base>, L.line_change(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA,ACACA\t50\tPASS\tI1=7\tGT\t1/2"), 1n)) : List<&2, List<&2, B.Base>>}:
  {==}

# What written gives: the normalized record.
def ex_written_moves() -> {L.written(B.Fasta.parse(">c1\nACGTACGTCACACACAGGGGTTTACGTAAAAAGCTAGCTAGCTTGACCATGCAATTGCCA\n>c2\nGGGGCCCCAAAATTTTGCGCATATCGCGATATACGTCAGTCAGTCAG\n"), "c1\t12\trs1\tACA\tA\t50\tPASS\tI1=7\tGT\t1/0") == "c1\t8\trs1\tTCA\tT\t50\tPASS\tI1=7\tGT\t1/0" : String}:
  {==}
```

## Splitter speed

Branch `split-speed` (from `split` at d365d9e), brief `notes/briefs/SPLIT_SPEED.md`. Only
`norm_split.bend` and four `proof_s_*` files changed; `split_t`'s statement and every name used
outside the splitter are as they were. Scratch: `data/tmp/splitspeed/`.

### Result

`data/tmp/splitspeed/bench.sh` (`bench.out` has the raw lines): `norm -c w -m -any`, the base build
(`fb_base`, d365d9e) and the new one (`fb_new`) interleaved, 4 rounds, under
`flock data/tmp/bench.lock`, `nice -n 19`, `taskset -c 0-15`. The machine was shared (load 4-5,
other agents' checks), so wall times are a little high for both; the outputs' md5 are the same
for both builds on every file.

| file | threads | base | new | peak RSS |
|---|---|---|---|---|
| cohort | 1 | 5.78-6.27 s | 3.94-4.11 s | 77-81 MB, both |
| cohort | default | 2.16-2.31 s (CPU 14.8-15.4 s) | 1.33-1.69 s (CPU 8.4-9.6 s) | 343-346 MB, both |
| joined | 1 | 4.39-5.09 s | 4.03-4.40 s | 49-64 MB, both |
| joined | default | 1.42-1.58 s | 1.30-1.34 s | 299-302 MB, both |
| HG002 chr22 | 1 | 0.15-0.19 s | 0.14-0.16 s | 42-49 MB |
| HG002 chr22 | default | 0.08-0.09 s | 0.08-0.09 s | 170-174 MB |

- **Cohort, one thread:** 1.5 times faster for the whole run. With about 0.5 s of the run outside
  the splitter, the splitter itself went from about 5.5 to about 3.5 s, 1.6 times.
- **Cohort, default threads:** 1.4 times; CPU time 1.6 times less. The main thread (the pieces it
  redoes, "Open leads" above) still bounds the wall time.
- **Joined** (4% multiallelic, GT only): 5-10%. **HG002 chr22:** within the noise.
- **Memory:** unchanged.

### What paid

The cost model, read from the generated C: a Bend def compiles either to a `spin_N` C function
(straight code, inlined, arguments in registers) or to a work-loop case (`WL_FID_<def>`, with a
continuation frame for each call that is not in tail position). A def became a work-loop case
whenever something it may call recurses other than in tail position. The `Sw` writer state and
ranges are unboxed either way; what costs is the work loop, lists (allocation, then `term_drop`)
and matching shared values (`span_fade`, `rfc_wrap`).

1. **The writer as straight code.** `NR.room` (called by `NR.put_bytes` and before every pushed
   byte) finds a block size with `NR.depth.go`, whose recursive call sits inside a `Bool.pick`
   (which evaluates both branches), so it is not a tail call. That made `room`, and with it
   `flush`, `cpr`, `ch`, `push`, `sep`, `pick`, `vals`, `gt`, `fmt.go`: everything that writes, a
   work-loop case. The splitter now has its own `room` and `put_bytes`, NR's with the depth search
   as a loop (`depth.go` matches a `stop` flag). Cohort, one thread: 6.6 to 5.6 s alone.
   Proof: `proof_s_w.bend`, `room_eq` and `put_eq` (the splitter's are NR's, by induction on the
   depth fuel), one rewrite each in `flush_put.k` and `push_put`.
2. **A sample's values found in place.** `sample` cut each column into a list of ranges (two
   lists: ends, then ranges), per sample per record: 11 M lists on the cohort, built, walked once
   and freed (`term_drop` was 8% of the time). Now `copies` and `fmt.go` walk the column: each
   step finds the next `:` (`F.find`) and writes the value before it. With (1), the whole record
   writer (`records`, `samples`, `sample`) is straight code: 5.6 to 4.2 s.
   Done as a step-plus-fuel loop over a state that held the FORMAT keys, it was slower than the
   lists (7.0 against 6.1 s): the keys are shared, and a state holding them makes every step
   bump and drop their reference counts. The keys must stay a parameter matched in place, so
   both functions recurse on the key list and take the previous step's `find` as an argument.
   Proof: `proof_s_fmt.bend`, `cps_t` (copies) and `fgo_t` (the values), by induction on the
   keys, with the column's pieces from `K.SP` (`sp_first`, `ts_next`, `ts_last` of
   `proof_s_scan`); `sample_t` keeps its statement. The list-based `copies`, `cp_t` and
   `fmt_go_t` are gone.
3. **No index list.** `B.Vals.idx` (the spec) chooses its list with a `Bool.pick`, which builds
   both lists: 22 M calls, 44 M reference cells, 11 M frees. `pix` picks the 1-3 values directly
   (A: i - 1; R and G for one copy: 0 and i; G for two copies: 0/0, 0/i, i/i). About 8% over (2)
   with a matched list; 2-3% more with no list. Proof: `proof_s_vals.bend`, `pix_eq` (`pix` is
   `picks` of `B.Vals.idx`, by cases).

### What did not pay (measured, dropped)

- Picking each value from where the previous one ended instead of from the value's start: 1%,
  within the noise (measured before (1), when everything was a work-loop case).
- Passing a sample's copies as a number (0 for none) instead of `Maybe` (one fewer box per
  sample): no difference.
- The splitter's own `fits` (B.Vals.fits of expected_count, with matches for the `Bool.pick`s):
  no difference.
- An output buffer sized for the line's records up front (no regrowth, 6% of the profile):
  no difference (medians 4.18 against 4.06 s); it would also have changed `proof_s_drv`.
- Decision 19 (split each column once per line, not once per record): with the values found in
  place there is no per-record cut left to share; the per-record cost is the writing itself.
  Keeping each sample's ranges for the line would add a 3,202-entry structure per line.

### What is left

Profile of the new build (cohort, one thread): the record writer's glue 23%, `vals` 16%, `pick`
13%, `ch` 10%, `put_bytes` 9%, buffer regrowth 6%, freeing 6% (String work outside the
splitter: header, INFO and FORMAT keys per line).

### Checks

- `data/tmp/splitspeed/ident.sh fb_new`:
  - against the old build (`fb_m3`, `same.sh`: the files of `data/tmp/split/thr_m.sh`, 4 option
    sets, `--threads 1` and the default; stdout, stderr and exit code): 312 of 312 identical;
  - bcftools 1.24 (`cmp_m.sh`, `-c w -m -any`): cohort 3,341 records, 0 differing; HG002 chr22
    50,861, 0 differing; joined 57,534, 12 differing (the same 12 symbolic SVs as before);
  - `test/split.sh` (the fuzz, 40 seeds, both `--multi-overlaps` settings): 80 of 80 the same as
    bcftools.
- Proofs (`test/bcheck.sh`): `proof_s_drv.bend` (`split_t`, which imports every splitter proof)
  checks with `--check-only` and `--verdict`; so do `proof_s_multi.bend` and `proof_s_term.bend`.
  `proof_b_adv_split.bend`, `proof_b_mw.bend` and `proof_b_adv.bend` stop at "38 TODOs found",
  the same as on the base tree (milestone (2)'s open holes).
