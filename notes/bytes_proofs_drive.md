# Phase B, area "drive": notes

## Status (2026-10-28, fifth round)

`pump_ok`, `step_eof`, `step_ref` and `start_ok` are proven, in both modes. Each deliverable
is one call (DP.pump_ok_h, DS.step_eof_h, DS.step_ref_h, DST.start_ok_g). None of my helper
files has a TODO, and every drive file checks through bcheck.sh; the TODOs they report are
other areas' (run, lines, cache, adv, lit). `step_chunk` belongs to pb-lines (below).

Helper files:
- `proof_b_drive_out.bend`, the end of a step (out_ok), both modes. Also: the WF tools (`X8`
  with 9 tests, `x8_a`, `x9_1`..`x9_8`, `x9_mk`), md_ok(MSP)'s six tests (`Z6`, `z6_*`,
  `z6_mk`), `live`, `mode`, and out_ask/out_more (OutG to StepG).
- `proof_b_drive_fin.bend`, the end of the run in byte mode (`fin_mb`), and `NoLines`
  (`nl_halt`, `nl_eof_mb`).
- `proof_b_drive_finms.bend`, the end of the run in String mode.
  - `fin_ms_some`: the code is set; the queue is handed out at once if it fits
    (`fin_fits`), else over `Ask{[]}` steps.
  - `fin_ms_none`: R.finish's report is queued first. The no-fit branch outside the body is
    impossible, since there the queue is empty.
  - Bytes of finish's output: `fin_out_bytes`, through `fl_bytes`.
  - The queue: `cat_rev_cons`.
- `proof_b_drive_pump.bend`, `pump_ok_h`: by induction on the fuel over AdvG.
- `proof_b_drive_step.bend`:
  - `go_ok`, `rep_lines`, `step_eof_h`, `step_ref_h` (with `mbw_of`: mb_reqs gives the new
    window's mb_win);
  - `step_chunk_go`: my side of step_chunk.
- `proof_b_drive_start.bend`, `start_ok_g`.

### step_chunk: the interface for pb-lines

pb-lines writes, in `proof_b_drive_chunk.bend`, this lemma (the feed step; byte-level LF
search, pend add/join, piece splitting):

    def feed_ok(+fa: List<&2, B.Contig>, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
      hm: {DR.more_ok(fa, p) == True{} : Bool},
      hcb: {E.is_bytes(c) == True{} : Bool},
      hcn: {P.le31(String.length(c)) == True{} : Bool}) ->
      &p1: S.StP -> ({Norm.feed(S.mkSt(fa, p), E.enc(c)) == S.mkSt(fa, p1) : Norm.St}
        & ({S.WF(fa, p1) == True{} : Bool}
        & ({S.report(fa, cs, O, N, p1) == S.report(fa, c <> cs, O, N, p) : R.Report}
        & ({S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>}
        & {S.guard(O, N, p1) == S.guard(O, N, p) : Bool}))))

(DR = proof_b_drivedefs.bend, S = proof_b_simdefs.bend, P = proof_b_defs.bend.) The type
of `fd` in `DS.step_chunk_go` is exactly this sigma. step_chunk's body is then:

    DS.step_chunk_go(fa, T, c, cs, O, N, p, hb, hr, hg, CH.feed_ok(fa, c, cs, O, N, p, hm, hcb, hcn))

with `import ./proof_b_drive_chunk.bend as CH` in proof_b_drive.bend. (go and pump_ok are
handled by step_chunk_go.)

What feed_ok can use:
- `DS.rep_lines` (proof_b_drive_step.bend): the report from the lines still to come. Two
  states with the same options and run whose `B.Text.lines(S.intext(.., cs))` agree stand
  for the same report; cs may differ, so pass `c <> cs` on one side.
- WF: `DO.x9_mk` builds S.WF from its nine tests; `DO.x8_a`, `DO.x9_1`..`DO.x9_8` read
  them (each with the nine tests as written in S.WF, then the hypothesis). `DO.wf_set_md`
  swaps the run.
- more_ok's four tests: `DS.mo_w`, `DS.mo_se`, `DS.mo_ne`, `DS.mo_no`. `DS.step_eof_h`
  shows the pattern: match p's src (Nil), eof (False) and asked (None), and refute the
  other shapes.
- The end-of-file proof as a template: `DS.eof_empty`, `DS.eof_full2` (a new source and an
  empty line end, WF rebuilt, report by rep_lines + lines_eof).
- The md: md.reserve via PR.run_reserve (specRun unchanged, so report, guard and mb_win
  are unchanged; md_ok via RunInv of the new run). The String mode keeps MS as it is.
- `DS.ends_lf_lf` (`ends_lf(x ++ "\n")`), `DS.empty_of_len`, `DS.nonempty_of_len`.

## The statement problems

1. **O and N before the #CHROM line** (pump_ok, step_chunk, step_eof, step_ref).
   - The statements allow any O and N collected by the driver.
   - Before #CHROM, run.bend's report does not keep them: `R.finish` without a header is
     `Report{"", [NO_HEADER], 1}`, and `R.head_line` writes the header over out.
   - cex case 1: the start run at eof with O = "x" finishes. The driver reports
     `{"x", [NO_HEADER], 1}`, while T = `{"", [NO_HEADER], 1}`.
   - cex case 2: the piece "#CHROM\n" gives t = the header. StepG's More case needs
     `report(.., "x" ++ t, ..) == T`, but T's out is the header alone.
   - Fix: the frame area's guard as a hypothesis,
     `hg: {R.RunSt.inbody(S.smd(S.StP.md(p))) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{} : Bool}`,
     and StepG's More and Ask cases giving it for p2 with `O ++ t` and `N ++ ns`. This needs
     RunInv to say a run before #CHROM writes and notes nothing, so that t = "" and ns = [].
2. **start_ok: the command line's bytes.**
   - S.WF asks `E.all_bytes(S.opts_args(o))`, and the options' arguments are argv after
     "norm".
   - start_ok assumes only the parse, so a VCF path with a character above 255 parses, yet no
     p is more_ok (cex case 3: `Some{False}`).
   - Fix: add `hab: {E.all_bytes(argv) == True{} : Bool}`; the law machine has it through
     E.texts_ok.
3. **AdvG's Ended case** (proof_b_sim.bend, another area's statement).
   - pump finishes on Ended, and StepG's Finish needs `Report{O ++ t, N ++ ns, c} == T`, with
     T = `report(.., p2)` = the spec's run over the lines still to come.
   - That is the stopped report only if the run stopped: run_halted applies, or the String
     mode has its code.
   - The code's Ended is exactly that (mb.rs: Rs halt; ms.adv: code Some or halt), but AdvG
     does not say so.
   - Fix: add to AdvG's Ended case a fact such as
     `{S.stopped(S.StP.md(p2)) == True{} : Bool}`, where stopped is `RunP.x(rp)` for MBP and
     `Maybe.is_some(code) || R.RunSt.halt(s)` for MSP.
   - (Idle is fine: at eof, WF makes the line end empty, so no lines remain.)

4. **AdvG gives no guard for the state it leads to** (proof_b_sim.bend's AdvG).
   - pump_ok's induction calls adv_ok again after Went, and adv_ok now needs
     `guard(O, N, p2)`.
   - StepG asks for the guard of the state after the step.
   - AdvG should give `{guard(O, N, p2) == True{}}` in every case (the run never leaves the
     body; before #CHROM, O and N stay empty).
5. **Keeping the guard across a step's out** needs a run-area fact that no lemma states:
   for a good run not in the body, `P.RunSt.out(P.specRun(rp)) == ""` and
   `P.RunSt.notes(P.specRun(rp)) == []`.
   - The step hands out exactly those (run_take), so then t = "" and ns = [].
   - RunInv is meant to include it (its comment says so), but it is opaque here.
   - A lemma in proof_b_run.bend would do, e.g.
     `run_head_quiet(p, hi, hin: RunP.i(p) == False): out == "" & notes == []`.
   - The String mode has it in md_ok's new clauses.

6. **step_ref needs the reads to be a window's parts.**
   - set_win builds the window with `win_of(rs, truths(fa, rs))`. The cache area's
     `win_truths` describes it only for `rs = Norm.parts(c, a, b)`; for arbitrary reads it is
     no picture's window.
   - The machine only asks `Norm.Req.of(c, a, e)`, which is one read within 2^31 or
     `parts(c, a, e)`, so the fact is true. But AdvG's Want and StepG's Ask (hence step_ref's
     hypotheses) only say reqs_ok and asked_of.
   - Fix: carry "rs is [] or parts(c, a, b) for some c, a, b" in AdvG's Want, StepG's Ask and
     step_ref's hypotheses, for example `&w -> {rs == S.reads_of(w)}`, where reads_of(None) =
     [] and reads_of(Some (c, a, b)) = parts(c, a, b).
7. **The String mode's guard.**
   - Before #CHROM the String mode hands out its messages, notes(s). md_ok(MSP) says the
     queued text is empty outside the body, but nothing says notes(s) is empty there.
   - Fix: add `R.RunSt.inbody(s) || List.is_empty(&2, B.Note, P.RunSt.notes(s))` to md_ok(MSP).

## Earlier rounds (helper files, checked through test/bcheck.sh)

- `proof_b_drive_out.bend`:
  - `X8`, `x8_a`, `x8_t`, `x8_swap`: S.WF is a left-nested chain of eight tests (`&&`
    associates to the left; probed).
  - `wf_md`: a good state's run is good. `wf_set_md`: a good state with a good run swapped in
    is good.
  - `chars_nr` (E.chars = NR.chars), `pre_clear`, `clear_inbody`, and `left_eq`
    (`Norm.left(mkSrcs(src)) == (mkSrcs(src), lsum(src))`).
  - `OutG` and `out_ok`: the end of a step (Norm.out) from a good state. The buffer reads as
    text t, and the new state is good, standing for the same report with t and the messages on
    the driver's side. It keeps the input, what was asked, and inbody, and next is as given.
    - The byte mode is proven (`out_mb.k`, through run_take and proof_b_enc's out_ok).
    - The String mode is a TODO. ms.take hands out at most `lim()` bytes through NR.of_str,
      whose hypothesis is `<= Nat.pow(2n, 30n)`, while `lim()` is now the literal 1073741824n.
      Joining the two is the bound question the lead is settling.
- `proof_b_drive_start.bend`:
  - `start_ok_g`: start_ok with `hab` added, through run_start and pd_empty.
  - `args_parse`: a command line of bytes gives options whose arguments are bytes.
  - `g_st`, `g_paths`, `g_more`, `g_rep`: the four parts.
  - start_ok's body is `start_ok_g(...)` once `hab` is in the statement.

## Not started (waiting on the fixes)

- pump_ok (induction on f over AdvG), the finish lemma (byte mode: run_finish, then out_ok,
  then finish_pre and run_halted), and step_chunk/step_eof/step_ref (feed, feed_eof, set_win,
  then pump).

## Where it got hard (research data)

- **Two definitions refused to unfold.**
  - A def that only abbreviates a state, `P0(o, rp, pp)`, blocked `S.mkSt(fa, P0(...))`
    from reducing; the same term written out reduces. Write constructor terms inline.
  - Destructuring a pair whose type came from a zero-argument def (`StartR()`) failed with
    "cannot infer"; writing the type inline in the signature fixed it.
- **Pair parts are used once unless marked.** Components destructured from a lemma's
  sigma must be bound with `+` (`(+esp, eow) = tk8`) to be used twice.
- **Lets.** `%e : G; t` inside a `+x = ...` let cannot be inferred, so rewrite with
  `Equal.trans`/`Equal.cong` chains, or move the step into its own small law.
- **A `+` on the second half of a final pair.** In a destructuring chain,
  `(a, +b) = x` (and `(+a, +b) = x`) fails with "cannot infer" when x's second half is the
  last pair. Leave b linear and pass the parts to a lemma with `+` parameters.
- **Identical definitions do not unify on a stuck argument** (StepG and a copy), and Bend
  refuses import cycles. Definitions a helper needs must live in a file the deliverable file
  does not import back.
- **No lets before a match.** Lets placed before a `match` make the scrutinee unmatchable;
  move them into the branches.
- **Generated lemmas.** The nine-test WF needed nine projections and a builder; a short
  Python generator wrote them, which kept the rewrites consistent.
- **Shared imports.** Other agents' files in progress (a `?goal` probe in
  proof_b_cache.bend, then an error in its `te.go`) stopped my checks, since the drive files
  import the cache and sim files. Retry later.
- **The statements themselves.** Running the machine on a concrete start state found the
  first problem in minutes. Reading the code's Ended paths against AdvG found the third.

## Budget API (proof_b_budget_api.bend; pb-cut proves these)

The assembly needs exactly these. All are `?TODO`, and their statements are fixed by
proof_b_assemble.bend.

- `need(fa, T, p, cs, eof, nx, O) : Nat`: the potential of a driver state that has not
  stopped (next More or Ask). It is stated over the machine's picture `p` and the driver's
  fields: cs = pieces not given, eof = the end of the file given, nx = the machine's next,
  O = output collected. It is an upper bound on the driver steps plus the reads still to
  come. pb-cut defines it.
- `bi(fa, T, p, cs, eof, nx, O) : Bool`: pb-cut's own invariant of such a state, kept by
  every step (`True{}` if not needed).
- `bud_start`: for start_ok's picture p of the program's first state (with the law's
  hypotheses, `hst`, `hm` = more_ok, `hr` = report is `L.run`), `bi` holds and
  `need(..., cs, False, More, "") <= M.bound(argv, fasta, vcf, cs)`.
- Per driver input kind (`chunk`, `eof`, `ref`), two lemmas. The before-state facts are
  those the step lemmas take (more_ok, or WF and Ask's facts), plus `bi`.
  - `bud_k`: for every picture `p2` of the step's next state, with
    `sst(step) == mkSt(fa, p2)`, `snx(step) == nx2`, `sout(step) == Some{t}`, and the next
    state's WF, report and guard: `bi` holds for p2, and
    `need(p2, ...) + (R + 1) <= need(p, ...)`. R is the reads the driver adds:
    `|rs|` for `ref`, 0 otherwise.
  - `bud_k_fin`: if the step's next is `Finish{code}`, then `R + 2 <= need(p, ...)` (one
    step for this one, one for the driver's last).
  - `sst`, `snx`, `sns` and `sout` project a Norm.Step (state, next, messages,
    `E.out(buffer)`). The statements use the step term itself (`Norm.step(S.mkSt(fa, p),
    Pr.Chunk{E.enc(c)})`, `Pr.Eof{}`, `Pr.Ref{M.truths(fa, rs)}`), so pb-cut can unfold
    the machine.
- Nothing about the stopped state is needed. The assembly keeps
  `reads + need <= bound` and `need <= fuel`, so reads <= bound at the end.

## Assembly (proof_b_assemble.bend; machine's body is one call)

`proof_b_machine.bend`'s `machine` is `AS.machine_h(...)`, and it checks. The remaining
TODOs are the API's 9, the 4 below, and other areas'.

- `Good(fa, T, lim, f, d)`: by the driver state's done, then next (`GoodD`, `GoodN`):
  - stopped: good flag True, report = T, reads <= lim;
  - Finish: the same with reads + 1 <= lim and 1 <= f;
  - More: a picture p with more_ok, the report, the guard, flag True, `eof == False`, the
    pieces' bytes (`txt`), `bi`, `reads + need <= lim`, `need <= f`;
  - Ask{rs}: a picture p with WF, the report, Ask's facts (reqs_ok, rq, mb_reqs, asked),
    the guard, flag True, `eof given implies p's eof`, `txt`, `bi`, the budget.
- `StepR(f, d')`: Empty at fuel 0, else Good of d' with fuel f - 1. One step lemma
  (`step_good`) serves both the induction and the contradiction at fuel 0.
- `absorb_ok`: from a step's guarantee and the budget's continuations (`Kont`, `KFin`, from
  API.bud_*), the driver's absorb gives StepR (`am_more`, `am_ask`, `am_fin`, with the
  arithmetic `ar_lim`, `ar_fuel`, `ar_zero`).
- Kinds: `k_chunk`, `k_eof`, `k_ask`, `k_fin`. The More state with no piece left after
  the end of the file is refuted by `eof == False`.
- `drive_ok`: by induction on the fuel. `machine_h`: start_ok's picture plus
  `API.bud_start` give Good of the first driver state with fuel = lim = M.bound.

Open TODOs of the assembly (not budget), as of 2026-10-28:
- **`sg_eof`, `sg_ref`: proven** (`DS.step_eof_h2`, `DS.step_ref_h2`), now that AdvG
  carries eof.
  - `DO.StepG2` (proof_b_drive_out.bend) is the step guarantee with the eof flag and
    nothing asked in More, and `DO.sg2w` weakens it to DD.StepG.
  - Through the helpers it is `out_ask`/`out_more` (with `ef`, `eof(p) == ef`, and
    `asked(p) == None` for More), the finish lemmas (with `ef`), `pump_ok_h2`, `go_ok2`,
    `step_eof_h2` (ef = True) and `step_ref_h2` (ef = eof(p)).
  - The old names (`pump_ok_h`, `go_ok`, `step_eof_h`, `step_ref_h`) are now `sg2w` of
    the new ones, so the drive deliverables and pb-lines' file are unchanged.
- **`sg_chunk`: open, waiting for pb-lines.** It needs step_chunk with StepG2 and
  ef = False. In `proof_b_drive_chunk.bend` that is mechanical:
  - make a copy of the chain ending in `step_chunk_h2` whose result is
    `DO.StepG2(fa, T, cs, O, N, False{}, ...)`: replace `DR.StepG(fa, T, cs, O, N, ` with
    `DO.StepG2(fa, T, cs, O, N, False{}, ` and `DS.go_ok(` with `DS.go_ok2(`. Every state
    there has eof False, so go_ok2's flag `S.StP.eof(p1)` reduces to False;
  - keep `step_chunk_h` as
    `DO.sg2w(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), step_chunk_h2(...))`.
  - Then `sg_chunk` is `DC.step_chunk_h2(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg)`
    (import proof_b_drive_chunk.bend in proof_b_assemble.bend).
- **`fa_bytes_parse`**: pb-lines (proof_b_fa_bytes.bend), with the statement as used:
  `def fa_bytes_parse(+fasta: String, hb: {E.is_bytes(fasta) == True{} : Bool}) -> {PC.fa_bytes(B.Fasta.parse(fasta)) == True{} : Bool}`.

### Where it got hard (assembly)

- **Stuck case trees.** M.dstep's and Good's matches look at `next` before `done`, so a
  stopped state's dstep or Good does not reduce while `next` is a variable. drive_done
  matches `next`; Good is three nested matches (state, done, next).
- **Erased states.** The driver's state holds the machine's state, a Type used once. The
  step lemmas take it erased (`-st`), since `Equal.sym`'s term arguments are erased.
- **No destructuring of computed pairs, again.** StepR (Empty at fuel 0) avoids a sigma
  result in the drive induction. The budget's per-step results reach the absorb lemmas as
  continuations (`@p2: S.StP -> ...` taking the next picture), filled by lambdas over the
  API lemmas.

## bud_start (proof_b_bud_start.bend; the API's body is one call)

`bud_start` in proof_b_budget_api.bend is `BSt.bud_start_h(argv, o, ref, vcfpath, fasta, vcf,
cs, p, ha, h, hst)`. It uses only ha, h and hst. proof_b_bud_start.bend checks through
bcheck.sh, with no TODO of its own. A copy of the API without pb-lines' proof_b_bud_fin.bend
import checks with only TODOs left. The real API file does not check yet: proof_b_bud_fin.bend
calls `BN.WA(fa, p, cs)`, which pb-cut has since removed from proof_b_budget_need.bend.

Route (no walk of the machine):
- **The picture.** hst, then ha (reversed), turn `mkSt(fa, p)` into Norm.start's concrete
  state: back 0, no sources, an empty line end, no window, nothing asked, byte mode, fneed False.
  `NR.chars(D.view(BY.empty(0n)))` reduces to "" by computation, so the lines still to come are
  `Text.lines(concat cs)`, which h turns into `Text.lines(vcf)`.
- **bi** is `bi.ls(0n, ...)`: True on any list (`bi0`).
- **WA <= LAs** (`rem_le`, `wa_le`). At the start the line being handled has RW + RW + ZW + (at
  most ZW) left.
- **LA of a line <= (|piece| + 1) ZW** (`la_le`), where a piece is the text between two LFs.
  When lgate holds, `8 + |REF| <= 1 + |body|` (`body_f3`), and `|body| <= |piece|` (`body_le`).
  - body_f3 splits on `J.c7(body)`, using proof_fast's `c7_split`. With seven tabs found (Got),
    the fields are f0..f6 followed by `split(r)`, so SN >= 8 + |f3| for any body. Otherwise
    (Short), the fields are the body's and a line that is not malformed has 8 of them
    (`short_f3`, refuting the shorter lists).
  - With `SN(split(s, c)) = 1 + |s|` (pb-cut's `split_sn`), the arithmetic is
    `2 (1 + max(1, R)) + 2 Z <= (R + 4) Z <= n Z` (`la_ar`).
- **Sum** over `lines.start`/`lines.go`/`last` (`lgo`, `lstart`, `lvcf`):
  `LAs(lines vcf) <= SN(split(vcf, '\n')) ZW = (1 + |vcf|) ZW`.
- **FM <= |fasta|** (`fa_fm`), from proof_machine_fasta's `bounded`/`keep_bounded`/`go_bounded`.
- **HO <= (1 + |vcf|) + args_len(argv)** (`ho_le`):
  - pb-cut's `out_len` gives |out| <= 2 OB, and `OB <= 124 X` with X = (1 + |vcf|) + args_len.
  - |args_text(o.args)| = args_len(o.args) <= args_len(argv) (`at_len`, `args_le`; o.args is
    the argv after "norm").
  - The step through the division is generic in the divisor lm >= 248 (`div_le`: N.div_lt,
    then lt_succ_iff). HO now divides by 256n.
- **Final arithmetic** (`fin`):
  `c + 1 + 2 + H + W <= c + 3 + AL + v (F + 3)`, with `v (F + 3) = v + v (F + 2)`.

Where it got hard:
- HO changed under me from `Norm.lim()` to `256n`. The mismatch looked like a checker bug: the
  expected form showed `divmod.go(..., 255n, ...)` against `1073741823n`. It was just the new
  divisor. Re-read pb-cut's defs before blaming the checker.
- `+x = 1n+e` lets fail ("cannot infer"). Write them as `Nat.add(1n, e)`.
- A hypothesis of function type (`@e: {g == True} -> ...`) cannot be `+` (not Data). Leave it
  linear; each match branch uses it once.

## Budget lemmas F1-F3 (pb-cut's, notes/bytes_proofs_budget.md)

- **F1 `chunk_fed`, F2 `eof_fed`: proven** in proof_b_bud_fed.bend. The file checks through
  bcheck.sh, has no TODO of its own and does not import proof_b_budget_step.bend.
  - The statements are copied exactly (chunk_fed is in def form, eof_fed in law form; their
    types are the same).
  - Route: the drive area's chains (pb-lines' chunk chain from proof_b_drive_chunk.bend, and the
    eof chain from proof_b_drive_step.bend), copied with FedG in place of `go`.
  - The copies were made by a small script; edit them directly. Each takes `hbi` along.
  - Each leaf is `fed_leaf`: the fed picture Q1 has Q0's back, window, fneed, mode and nothing
    asked. The line equality the leaf already has for the report (`hl`) gives
    `BN.lines(Q1) == BN.lines(Q0)` (`lines_eq`, via BL.text_pic). From it, WA is equal
    (`le_eq`) and bi carries over.
  - In chunk_mb2 the run changes (reserve), but WP and biS do not read the run (fast_left of
    MB is `not fneed`), so the types convert.
- **F3 `ref_fed`: false as stated.** proof_b_bud_ref_cex.bend checks a counterexample:
  - The instance: fa = [], one line `1 2 . C A . . .` to come, the String mode, back 0, the
    window Unknown{"1"} (it holds every read of contig 1), and asked = Some{[Req{"2", 0, 1}]}.
  - Every hypothesis holds by computation (WF, ha, hq, hp, hmr, hg, hbi; hr with T := the
    report).
  - set_win puts the Ask's window (contig 2) in place of the old one, so the line's read is no
    longer held and rem's RW comes back: WA goes from 4 to 6 (`c_wa0`, `c_wa1`). `c_false`
    refutes FedG at this instance.
  - With back > 0, bi breaks the same way: the old window held the zero window and the Ask is
    elsewhere.
  - The cause: nothing ties the old window to the pending Ask. heldA counts a read held by the
    old window even while an Ask is pending, and set_win throws that window away.
  - Suggested fix (need/bi are pb-cut's): let heldA read only the Ask while one is pending
    (`asked = Some -> coversA`, `None -> holdsW`). The window after set_win is the Ask's, so
    pb-cut's coversA -> holdsW fact gives F3. adv_bud's Want case would then need the Ask to
    cover the line's windows, which is why the machine asks.

### F3 `ref_fed`: proven after pb-cut's fix

pb-cut changed need's `heldA`: while an Ask is pending it reads only the Ask (`coversA`). With
that, `ref_fed` is proven in proof_b_bud_fed.bend, with the statement unchanged. The file checks
with no TODO of its own.
- The key fact is `cov_hold`: what `coversA(Some{Req{c, a, b} :: t})` covers (same contig,
  start >= a, end <= last_b(t, b)), the window set_win builds,
  `mkWin(fa, wpOf(fa, c, a, last_b(t, b)))`, holds.
  - The proof splits on `find(fa, c)` (Unknown window: same contig) and on le31 (known or
    String window).
  - It uses `hwk`, copied from pb-cache's proof_b_bud_win.bend, for the pair in win_of.k, and
    `min_mono` for the end.
- From cov_hold, `rem_ref`/`wa_ref` give WA after <= WA before, and `bi_ref` keeps bi.
- The cases follow step_ref_h2. With no reads (Nil), the window and the lines are kept
  (`fed_leaf`). With reads, `ref_win2`/`ref_some`: the window becomes `wpOf(c, a, bb)` (via
  win_truths), with WF built as in ref_win.
- The old counterexample file (proof_b_bud_ref_cex.bend) is deleted: under the new heldA,
  WA after set_win is 4 there, not 6, so its `c_wa1`/`c_false` fail, as they should.

### F3 after pb-cut's stronger bi (zero window fits)

`bi_ref` now proves the new heldZ. Before set_win (Ask pending), the old window fits
(`zfit`: contig c1, e <= its clen) and the Ask covers (c1, 0, e). After set_win, the window
built from wpOf(c, a, bb) holds and fits (`zheld`). Lemma `zcov`:
- `zf`/`zfk`: a fitting window's contig is in the reference, `find(fa, c1) == Some{r}`, with
  e <= |r|. This uses proof_run_base's `str_eq_sound` for the contig names.
- The Ask is for the same contig (String.eq again), so the new window reads the same r: same
  clen, from a <= 0, to bb >= e.
- `zk`/`zh2` evaluate zheld on it. `zfwk`/`zhwk` handle win_of.k's pair, as in pb-cache's hwk.
proof_b_bud_fed.bend checks; so do proof_b_budget_step.bend and proof_b_budget_api.bend (TODOs
only).
