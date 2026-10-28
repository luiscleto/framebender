# Phase B: proving the packed-bytes machine (plan, interfaces, status)

Brief: `notes/briefs/BYTES_PROOFS.md`. Design of the code: `notes/bytes.md`.

## How the proof is split

The machine law (`MACHINE.bend`, `machine`) is proven by simulation, as on `main`
(`notes/proof_machine.md`). Between two driver steps there is a spec state S
(`R.RunSt`). The driver's collected output and the machine's state stand for S, and the
report is `R.finish(L.run.go(lines still to come, fa, o, S))`. Each line the machine
handles is one `L.line_step`.

The new parts are proven in separate files, one area each. Each file starts as a skeleton
whose deliverables (exact statements) are `?TODO`. An area is done when its deliverables
check with no `?TODO` left, apart from the ones in `proof_b_fasteq.bend`.

| area | file | what it shows | agent (Herdr workspace) |
|---|---|---|---|
| fasteq | `proof_b_fasteq.bend` | `fast.bend` = `bytes.bend` (`find`, `find2`) and `append`'s laws: **holes on purpose**; the lead's prove-bytes agent proves `fast.bend` | (lawful-bytes) |
| cut | `proof_b_cut.bend` | a line that passes `NF.line`: its LF is the first one; the String path cuts the same fields; POS; the alleles passed `NF.alleles`; the line's text | pb-cut (w14) |
| alleles | `proof_b_alleles.bend` | alleles that pass `NF.alleles`: read, written and normalized as they are; `J.fast` gives `Same` | pb-alleles (w15), done |
| enc | `proof_b_enc.bend` | `E.enc` as a mirror (`C.BT`), well formed, view = `codes`; `chars(codes s) = s`; `E.out` of a well-formed buffer | pb-enc (w16), done |
| run | `proof_b_run.bend` | the byte run (`NR.Run`) refines run.bend's `RunSt`, op by op, up to `P.settle` | pb-run (w17) |
| cache | `proof_b_cache.bend` | the window cache: reads within 2^31 letters, truthful answers, a retried read is held, the fast REF test means the String REF check passes | pb-cache (w18) |
| lines | `proof_b_lines.bend` | input buffers, line end, pieces and the end of the file against `B.Text.lines` | pb-lines (w19) |
| frame | `proof_b_frame.bend` | spec level: `settle` does not change a report; the spec commutes with what the driver collected (`pre`) | pb-enc (w16) |
| adv | `proof_b_sim.bend` (`adv_ok`), `proof_b_adv*.bend` | the per-line lemma: `advance` on a good state standing for report T | pb-alleles (w15) |
| drive | `proof_b_drive.bend` | a step's pump ends well (`pump_ok`); then the driver steps, the start, the budget (M.bound) and the law | not started |

Shared definitions: `proof_b_defs.bend` (pictures of the run, sources and line end;
`specRun`, `settle`, `srctext`, ...). The simulation's picture of the whole state and its
invariant (`StP`, `mkSt`, `WF`, `report`, `measure`, `AdvG`) are in `proof_b_sim.bend`.

The science-layer proofs (`proof_var*`, `proof_run*`, `proof_window*`) and `proof_fast.bend`
are kept. `proof_window*` and `proof_fast.bend` only changed `P.Ans` to `J.Ans`: the String
judge now takes a Data answer (`norm_line.bend`'s `J.Ans`, raw letters as a String), which
the machine decodes from the packed answers.

## Rules for every area

- Edit only your own file(s): the skeleton you were given, plus helper files named
  `proof_b_<area>_*.bend` if you want them. Do not change a deliverable's statement. If
  one is false or unusable, stop and report it.
- Never edit the program (`norm*.bend`, `main.bend`), the spec (`LAWS.bend`, `types.bend`,
  `run.bend`, `tan.bend`), the contract (`protocol.bend`, `MACHINE.bend`,
  `bytes_enc.bend`), `../lawful-*`, or another area's files.
- Check **only** through the wrapper, never with `bend` directly:
  `timeout 1800 test/bcheck.sh proof_b_<area>.bend` (add `--verdict` for the kernel).
  - It runs `prlimit --as=4000000000 timeout 1800 nice -n 19 bend ...` (4 GB of address
    space), and at most two checks at once across all of phase B (two lock slots; it
    waits for a free one).
  - Why: on 2026-10-28 a check of `proof_b_lines_tmp.bend` used 22 GB and ran the machine
    out of memory. The cause is in "Where it got hard" below, once known.
  - If it prints `bcheck: bend exited with ...` (not 0 or 1), the check ran out of its
    4 GB or its time, most likely by making the checker compute with a big closed Nat.
    Never do that (see below).
  - The goal is that the only TODOs left are `proof_b_fasteq.bend`'s.
- No git commits.
- Keep `notes/bytes_proofs_<area>.md` short and current: what is proven, what is left, and
  bullets on where it got hard (research data).

## Bend proof technique (read before starting)

- `notes/briefs/PROVING.md` (Bend proof notes), `bend guide` ("Laws and Proofs", the syntax
  reference), `notes/proof_machine.md` ("Where it got hard").
- `../lawful-bytes/notes/` and `../lawful-bytes/PROVING.md`: how lawful-bytes proved its
  laws.
  - A `D.Bytes` is a Type (it holds an Array), so a proof can use one only once.
    Lemmas are therefore about the mirror `C.BT(len, t)` (`../lawful-bytes/proof_core.bend`),
    with `len` and `t` reusable.
  - Every operation has a `*_pair` law (`B.at(b, i) == (b, value)`, `find_pair`, ...), so a
    loop's read-ahead pair reduces.
  - Use lawful-bytes' laws through its proof files (`PROOF.bend` fills `L.name` for every
    law in `LAWS.bend`; the `*_t` lemmas in `proof_*.bend` state them on mirrors).
  - Same for `../lawful-words` (`proof_nat`, `proof_u32`, `proof_bytes`) and
    `../lawful-arrays`.
- **Never let the checker compare a symbolic Nat with a big literal.** `Nat.pow(2n, 32n)`,
  `2147483648n` and `U32.to_nat` of a big word all expand to unary and overflow its stack
  (`../lawful-fields/notes/`).
  - Keep big bounds abstract: prove a lemma for any M, and instantiate it only where the
    types are syntactically identical (lawful-words does this).
  - Word arithmetic on U32 constants is cheap.
  - For "i + 1 does not overflow", lawful-bytes has `add11`, `inc_fits`, `add_fits`,
    `he32`, `fits_e`, `four_lt_e` (in `proof_core.bend` and `proof_find.bend`).
- `fast.bend`'s operations are reached only through `proof_b_fasteq.bend`: rewrite
  `F.find(...)` to `B.find(...)` with `FE.find_eq` (likewise `find2_eq`), then use
  lawful-bytes' laws for `B.find`.

## Code changes for the proofs (phase B)

- `norm_line.bend`: the String judge takes a Data answer `J.Ans` (raw letters as text)
  again. The machine decodes the window it serves (`BY.to_list` + `chars`) into one. So
  `proof_window*` and `proof_fast.bend` keep working; only the type name changed.
- `norm_fast.bend`: `NF.Pass` carries every field end, so the field proofs and the allele
  proofs meet on explicit ranges.
- `norm.bend`, so that the law holds for every input (found while planning the proof):
  - String mode (`MS`): when the output buffer would pass 2^29 bytes, a line is longer
    than 2^28 bytes, or the header longer than 2^28, the run switches to run.bend's own
    state for the rest of the file. Its output is handed out at most 2^30 bytes a step.
  - A line end longer than 2^28 bytes is kept as text (`PS`; `SL` sources).
  - Reads wider than 2^31 letters go in parts (`parts`; `WStr` windows).
  - The fast path asks one read per line at most (`fneed`); after that the line takes
    the slow path, so the machine always makes progress.
  - The pump's fuel is computed (a successor). If it runs out, the step ends with
    `Ask{[]}`, never `More` (the driver gives nothing after the end of the file).
  - Size bounds are tested on words, never on big closed Nats (the checker expands
    those to unary; see "Where it got hard"): `len_le(s, w)`, `take_w(s, w)`,
    `fits31`, `le31` (same body as `E.le31`), U32 sums for byte sizes.
  - Reads (2026-10-28 00:40): `parts` reads a .. b in one read if `le31(b - a)`, else
    reads the two halves the same way; `Req.of` asks its margin/ahead window in one read
    if `le31` of its width, else just a .. e. So no big constant is left in the code.
    Tried first: a fixed part size of 2^31. As a literal (`2147483648n`) it cannot be
    related to `le31`, which the decoding proof needs for every read. Written as
    `U32.to_nat(2147483648)`, it is expanded to unary whenever a proof unfolds `parts`
    (stack overflow). Halving needs neither, and the read count is generic
    (at most max(1, b - a)). `E.reqs_ok` is in the word form too (lead, a9ca757).
  - Each output item keeps its input POS (`Ck.inpos`), so the run converts to
    run.bend's state (`NR.to_spec`).
- Check: identical to `main`'s binary on all 30 + 48 runs. With a test build of tiny
  limits (String mode after 4 KB of output or a 300-byte line, 1 KB per step, reads in
  parts of 2^20 letters, a text line end past 256 bytes), all 54 edge runs (including
  chr22 and scr subsets) are identical too. chr22 0.137-0.152 s against bcftools'
  0.122-0.131 s in the same rounds, with proof checks running.
- C5 (budget, 2026-10-28 00:45): a line's `back` starts at 0 instead of 100, and the
  slow path's first try is `back = 0`. The first Want is then `Req.of` from POS - 1:
  one read or the line's own letters, so the per-line read count fits the bound even
  for a tiny FASTA and REF (with back 100 it could count 100 + |REF| reads). Every
  later miss asks the zero window, and that needs J.fast to have said None first.
  The output cannot change (window law); a slow line does a few more cheap tries.
  Identical on the 30 + 48 runs.
- C6 (adv, 2026-10-28 01:35): the #CHROM line's text with its LF must be at most 2^28
  bytes too (`head.len` tests `len_le(B.Line.text(l), 268435456)`); the line checks only
  bounded the line without its LF, so a 2^28-byte #CHROM line reached the header write
  with 2^28 + 1. If the test fails, the run goes to the String mode, as for the other
  header bounds. Identical on the 30 + 48 runs.
- C7 (budget, 2026-10-28 02:20): when a slow-path result does not fit the output buffer,
  the switch to the String mode keeps the line's `back` (it reset it to 0). A reset could
  raise the budget's potential (the line's zero-window allowance came back). `back` only
  steers which reads are asked, so the output cannot change. Identical on the 30 + 48 runs.
- Timing after all phase-B changes (2026-10-28 02:55, agents idle, 6 interleaved rounds of
  chr22 `-c w`): this build median 0.157 s (0.145-0.208), the same with C5 undone 0.161 s,
  phase A's commit (HEAD) 0.177 s (0.167-0.188); bcftools 0.116-0.132 s in the same
  session. The rounds vary by about +-20 ms, so phase B costs nothing measurable.
- Tiny-limit builds after C5-C7 (2026-10-28 03:00):
  - reads capped at 2^20 letters with margin 2^12 and ahead 2^18 (so `Req.of` asks its
    window in one read, and zero windows are halved): all 54 edge runs identical;
  - reads capped at 2^20 with the real margin and ahead (2^16, 2^24): 52 identical, and
    scr1500 (chr22) times out at 600 s in both modes. There `Req.of` always falls back to
    the line's own letters (ahead is past the cap), so with C5 (first try at back 0)
    nearly every slow line goes on to the zero window, reading chr22 from letter 0 in
    1 MiB parts and decoding them. With the real constants the tries up to the margin
    are served from `Req.of`'s window, as before C5. Run alone with a 50-minute
    limit, scr1500 -c e finishes in 14 min 44 s with output and messages identical
    to main's.
- After the halving `parts` (2026-10-28 00:40): identical on the 30 + 48 runs again, and
  all 54 tiny-limit runs (reads capped at 2^20 letters, so `Req.of` always falls back
  to a .. e and long windows are halved).
- C1 (budget, 2026-10-28 00:45): when the slow path runs out of tries or gets no
  answer, `vd.x` asks for the contig from its first letter with back = POS, so the next
  try decides. Without it, a contig past about 100·2^63 letters could make one line ask
  about log2(clen)/64 times, and the step bound would need a logarithm. Identical on
  the 30 + 48 runs.

## Status (2026-10-28, about 03:00): done

- `PROOF.bend`: ALL PROOFS CHECK with `--check-only` and with `--verdict` (28 s), so the
  13 science laws, `usage` and `machine` are proven, with no ?TODO anywhere in its
  import graph. Run through `test/bcheck.sh` (4 GB caps), not `check.sh` itself,
  which calls bend without a cap; the gate's two other steps pass the same way
  (`examples.bend`: only the imported laws' TODOs, which the gate accepts; `main.bend`:
  relies on unsafe, as expected).
- `examples.bend`: the six machine cases (`m_basic` .. `m_noheader`) moved to
  `examples_machine.bend`, outside the gate. Evaluated in the checker, the bytes machine
  runs past the 4 GB cap within 5 s even for one case. The proven law `machine` covers
  them, and the binary is compared with main's (30 + 48 + 54 runs). `truth_ws` now
  expects `E.enc("CGT")` (answers are bytes), and the `launch` calls take argv.
- Areas and files (each area's notes: `notes/bytes_proofs_<area>.md`):
  - cut, alleles, enc, frame, lines, cache, run: every deliverable proven.
  - adv (`proof_b_adv*.bend`, `adv_ok` in `proof_b_sim.bend`): proven; the String mode by
    pb-cache (`proof_b_adv_msx.bend`).
  - drive (`proof_b_drive*.bend`, `proof_b_drivedefs.bend`): `pump_ok`, `step_chunk`,
    `step_eof`, `step_ref`, `start_ok`.
  - assembly (`proof_b_assemble.bend`): the driver's invariant, induction over the
    driver's steps, `machine`'s body.
  - budget (`proof_b_budget*.bend`, `proof_b_bud_*.bend`; API
    `proof_b_budget_api.bend`): a potential `need` (pieces, Eof, Finish, the lines'
    read allowances, the hand-out steps) and an invariant `bi`; each driver step lowers
    need + reads by at least one; the start fits `M.bound` exactly (with `out_len`, a
    spec-level bound on the report's output).
- Statement changes made on the way (all found by an agent's counterexample, or by a
  proof needing a fact that was true but unstated), listed so the law review can see
  them: hin/hx/settle and the size hypotheses in the run area; `against_hit`'s hcb/hcl;
  WF's eof clause, `st_bytes`, args bytes, `mb_win`, `nolf` in `src_ok(SLP)`, the
  String-mode notes clause; AdvG's guard, stopped, eof, `rq`, `mb_reqs` facts; `eof_ok`'s
  hn; `run_head_empty`'s hx; `parts_ok` and `req_holds` restated for the halving `parts`.
- Counterexamples found along the way are kept in `notes/cex/` as records. Nothing
  imports them, they import from the repository root, and some no longer check against
  the final definitions. The String machine's proofs (`proof_machine*.bend`) were removed
  on this branch; `proof_b_machine.bend` replaces them.
- Contract changes made by the lead at our request: `pieces_ok` and `reqs_ok` state the
  2^31 bound as `le31` (words), not as `Nat.pow(2n, 31n)` or a literal.

## Resolved blocker: big `Nat.pow` in the contract

Resolved by the lead (76abb31, a9ca757): `pieces_ok` and `reqs_ok` state the bound as
`le31` (the size fits a U32 and that word is <= 2^31), not as a literal. Kept for the record:


The checker overflows its stack when it has to unfold a definition whose body holds
`Nat.pow(2n, 31n)`. It expands the power to unary. The literal `2147483648n` does not
overflow: it is one number, and bend and `--verdict` both accept unfolding it. Checked:
`data/tmp/lit/{a,b,c}.bend`.
- `bytes_enc.bend`'s `reqs_ok` and `pieces_ok` use `Nat.pow(2n, 31n)`. No proof can
  unfold them, so the driver's `good` flag (`reqs_ok` of every Ask) and the pieces'
  bound in `texts_ok` cannot be used. The law `machine` cannot be proven as stated.
- Proposed fix: write the bound as `2147483648n` in `reqs_ok` and `pieces_ok`.
- One caveat: comparing two big literals by computation is also very slow (minutes). The
  proofs therefore get literal facts through lawful-words' U32 lemmas, where word
  comparisons are native.
- The program's own bounds are now literals.

## Where it got hard (lead's notes)

- **Big Nats (2026-10-28, tested under the cap, `data/tmp/lit/*.bend`).** In bend 2.0.39's
  checker:
  - any closed big Nat term other than a bare literal is expanded to unary as soon as a
    conversion compares it: `Nat.pow(2n, 31n)`, `U32.to_nat(2147483648)`, and even
    `Nat.add(1073741824n, 1073741824n)`. This includes unfolding a definition whose body
    holds one;
  - a bare literal (`2147483648n`) unfolds fine but relates to nothing but itself:
    comparing it with `Nat.pow` or `to_nat` expands the other side, and `1073741824n <=
    2147483648n` by computation takes minutes;
  - words (U32) are evaluated natively.
  So the program checks sizes on words (`len_le`, `take_w`, `fits31`, U32 comparisons),
  and `proof_b_lit.bend` bridges words to powers without computing either (`lit_pow`:
  `shln(1, k) == w` natively, then lawful-words' `to_nat_shln_fits` with exponents kept as
  variables, `2^k < 2^32` by `pow_lt`). A literal is used only where it meets the
  contract's identical literal (`big()` against `E.reqs_ok`).
  - The bound `M` must stay abstract in any lemma that rewrites near it: one rewrite next
    to `Nat.pow(2n, 32n)` was enough to overflow (`lit.h` takes M as a parameter).
- **`--verdict` and `prlimit --as`.** The Lean kernel needs more than 4 GB of address
  space and aborts (SIGABRT) under `prlimit --as=4000000000`. `bcheck.sh` therefore caps
  `--verdict` by memory (cgroup `MemoryMax=4G`) instead.
- **The 22 GB check (2026-10-28).** `bend proof_b_lines_tmp.bend --check-only` grew to
  22 GB and ran the machine out of memory. pb-lines found the cause: its scratch file proved
  `Nat.is_le(268435456n, Nat.pow(2n, 29n))` by `{==}`. The checker built `2^29` as a unary
  chain of about 537 million nodes on the heap. A timeout does not cap memory.
