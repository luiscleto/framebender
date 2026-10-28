# Phase B, area "budget" (the law `machine`): notes

Brief: `notes/briefs/BYTES_PROOFS_BUDGET.md`.

## The potential (written first, as the brief asks)

Notation: F = |fasta|, K = F + 3, cs = pieces not given yet, p = the machine state's
picture (S.StP), O = what the driver collected, T = the report.

    need(D) = |cs|                        one step per piece
            + [not eof]                   the Eof step
            + 1                           the Finish step
            + K * (|intext(p, cs)| + 1)   allowance of the input still to come
            - spent(p)                    Wants already used on the waiting line
            + ceil((|T.out| - |O|) / 2^30) + 1   hand-out steps still to come
            + reads(next)                 the reads of a pending Ask (paid on answer)

- Driver invariant: `need(D) + reads_so_far <= bound`, and every driver step lowers
  `need + reads` by at least one (a step adds |rs| to reads exactly when it answers an Ask
  whose |rs| is in need).
- Start: |cs| + 1 + 1 + K * (|vcf| + 1) + ceil(|T.out| / 2^30) + 1 <= bound needs
  `ceil(|T.out| / 2^30) <= args_len(argv) + 1` (the bound's "+3" covers Eof, Finish and one
  more). See "Gap B".

### Paying for each kind of step

- Chunk: |cs| drops by one; the input text is the same (moved from cs into the sources).
- Eof: [not eof] drops.
- Finish: the last 1 (the driver stops).
- Ask answered (a Ref step), and the pump that follows:
  - every line the pump completes lowers |intext| by |line| >= 1, so K * |line| >= K
    is released; it pays that line's own Wants (spent resets to 0) and nothing else;
  - the step itself and its reads are paid by the Ask's `reads(next)` (already in need)
    plus one unit of the waiting line's stage (spent grows by 1 + |rs'| for the next Want);
  - a Yield (byte or String mode) or a String-mode hand-out step writes at least 2^30
    bytes (byte mode: `ow >= 2^30` written this step; String mode: `take` hands out
    `lim() = 2^30` when `ql >= lim()`), so `|T.out| - |O|` drops by 2^30.
- Per line, the Wants (fast path at most once, slow first try at most once, the zero
  window at most once, plus one more with code change C1) cost at most
  `4 + 2 * (1 + (|REF| + 2^25) / 2^31) + 2 * (1 + F / 2^31)` steps and reads. A line that
  Wants has 8 fields (>= 8 bytes), so this is `<= K * |line|` for every F.

### spent(p): the waiting line's stage

A function of (fneed, back, the window picture wp, asked) and of the waiting line's
read windows (c, a, e computed from the line's fields):
- fresh (fneed False, back <= 100, wp does not hold the line's back-100 window): 0;
- after the fast path's Want (fneed True): 1 + |parts of Req.of(c, p1, p1 + rl)|;
- after the slow first try's Want (wp holds the back-100 window, req_holds): + 1 + |...|;
- after the zero window's Want (wp holds (0, e), zero_holds): + 1 + |parts(c, 0, e)|.
The proof that no further Want happens once wp holds the zero window needs the window
laws (window_enough: the zero window is enough, so J.fast gives a result) and
`J.fast = None => REF fits the contig` (so e <= clen <= F, proof_machine_fasta's clen_le).

## Gaps found (the lead decides)

- **Gap A (code change C1 proposed): the slow path's fuel.** `slow.go(64n, ...)` grows
  back by doubling. If 64 tries are not enough (a contig longer than about 100 * 2^63
  letters: impossible on disk, but the law has no bound on |fasta|), `vd.x` asks
  `parts(c, 0, pos + |REF|)` again with back unchanged, and the next step can run out
  again: about log2(clen) / 64 Wants for one line. The total still fits the bound, but
  the potential would need a logarithm of clen / back.
  - C1: in `vd.x`, for `SAgain` (fuel out) and `SDone{J.Other{None}}`, keep back = POS in
    the VWant (`VWant{win, parts(..), B.Rec.pos(fs)}`). The next try then starts at the
    contig's first letter, which the answer holds (zero_holds), and decides (window_enough).
    Output unchanged (those paths only change which reads are asked, and only for
    absurdly long contigs).
- **Gap B: a bound on run's output length.** Paying for Yield and hand-out steps needs
  `|L.run(fasta, vcf, o).out| <= 2^30 * (args_len(argv) + 1 + something the bound allows)`.
  This is a spec-level fact (no machine), but it needs the length of a rewritten record
  (Rec.rebuild: POS, REF and ALT normalized are never longer than the input's: var area's
  `shortest`?) and of the header written at #CHROM (the echoed command line:
  args_len). Alternatively: bound the yields by lines (each yielding step handled a line in
  the byte mode; the String mode's hand-outs need the per-line output bound anyway).
- **Gap C: the budget is not in the simulation's statements.** StepG/AdvG give the next
  state only as an existential p2 with partial-correctness facts. The budget lemmas here are
  therefore stated for every picture of the step's state (`@p2 -> {s == mkSt(fa, p2)} ->
  {WF(fa, p2)} -> need(p2) ...`) and proved by walking pump/advance again with the budget's
  facts: per Adv outcome, what the Want asked, how fneed/back/wp changed, and how much
  input a Went consumed. That walk is the size of the adv area's.

## Status (2026-10-28)

### Done first, at the lead's request: proof_b_lit.bend's four bridges

`len_le_le`, `le_len_le`, `take_w_ok`, `take_w_all` are proven. The proof is induction on
the string, with the zero test as a parameter tied to `U32.is_zero(w)` (`lle.go`,
`lel.go`, `tw_app.go`, `tw_len.go`, `tw_all.go`), and `w_dec`: `to_nat(w - 1) = to_nat(w) -
1` for `w != 0`. `proof_b_lit.bend` has no TODO left; `--check-only` and `--verdict` both
print ALL PROOFS CHECK.

### proof_b_budget.bend (checks; its 23 TODOs are imported from other areas)

- `margin_ahead`, `fit0`, `fit100`, `big_pos`: closed facts on the code's literals, by
  `{==}`. Bare literals are native, so closed arithmetic on them is cheap; they are stated
  only with `Norm.margin()` / `Norm.ahead()` / `Norm.big()`, never next to a word.
- `win_size`: Req.of's window is at most `(e - a) + margin + ahead` letters (generic in
  margin and ahead).
- `ks`: `j * B <= x + y` with `y < B` gives `j <= x`.
- `parts_le`, `reqof_g` / `reqof_reads`: a Req.of window of at most `x + d` letters (with
  `d + margin + ahead < 2^31`) takes at most `x + 1` reads. The fast path (d = 0) and the
  slow path's first try (d = 100) therefore take at most `|REF| + 1` reads each.
- `zero_reads`: the zero window `(0, e)` takes at most `e + 1` reads.
- With these, one line's Wants cost at most `8 + 2 |REF| + 2 |fasta|` steps and reads
  (with C1), which is at most `(|fasta| + 3) * |line|` since `|line| >= |REF| + 7`.

### Not started, waiting for the lead's decisions

- The potential as a Bend definition: spent(p) depends on whether C1 is taken, and on how
  Gap B is settled.
- The per-step budget statements (Gap C): extend AdvG/StepG with budget facts, or state
  them separately for every picture of the step's state.
- The `machine` assembly in proof_b_machine.bend (drive induction, start bound). Its
  shape depends on the drive area's statements, which that agent reports are still being
  fixed (notes/bytes_proofs_drive.md, problems 2 to 5).

## Where it got hard (research data)

- A literal next to a non-literal form overflows: `{Norm.margin() == U32.to_nat(65536)}`
  by `{==}` overflowed the stack. Closed literal arithmetic (`65536n + 16777216n <
  2147483648n`) is cheap.
- A lemma that instantiates generic arithmetic with the code's literals inside its own body
  (`reqof_reads` written directly against Req.of) overflowed. The same lemma proved for
  abstract m, h (`reqof_g`) and instantiated at the end (one line) checks.
- With a hypothesis like `{Nat.pow(2n, 32n) == M}` in context, any error crashes the error
  printer (see notes/bytes_proofs_cut.md). Debug without it.

## Blocked (2026-10-28): big() as `U32.to_nat(2147483648)`

Probes under bcheck.sh, all "the machine stack overflowed" or "MemoryExhaustion":
- `{Norm.big() == U32.to_nat(2147483648)}` by `{==}`;
- a hypothesis `{Nat.is_le(x, Norm.big())}` used where `{Nat.is_le(x, U32.to_nat(2147483648))}` is expected;
- `{Norm.parts(c, a, b) == Norm.parts.go(Nat.sub(b, a), Norm.le31(Nat.sub(b, a)), c, a, b, Norm.big())}` by `{==}`, with c, a, b variables (only `parts` unfolded);
- `margin() + ahead() < big()` by way of `u_sum_lt`, even with margin and ahead also written as `U32.to_nat` words behind defs.

Reading: a non-syntactic conversion normalizes both sides fully. A closed `U32.to_nat(w)` then
evaluates to a unary Nat (2^31 nodes), so the term is fine only where it is compared
syntactically. A bare literal stays native under normalization. That is why the same
lemmas checked with `big() = 2147483648n` (and why proof_b_cache's `pg1` now fails). Every
lemma that unfolds `parts`, `Req.of` or `slow.reqs` meets `Norm.big()` this way.

## After the lead's parts change (2026-10-28)

- proof_b_budget.bend now holds only generic counts (ALL PROOFS CHECK, no TODO):
  `parts_len`: |parts(c, a, b)| <= max(1, b - a) (induction on the fuel; le31 rejects only
  windows of 2 or more letters, `ge2`, and both halves of n >= 2 are nonempty, `half`);
  `reqof_len`: |Req.of(c, a, e)| <= max(1, e - a).
- **Gap D (code change C5 proposed).** With the generic count, the slow path's first Want
  (window POS-1-100 .. end of REF) counts as up to 100 + |REF| reads. A line's Wants then
  cost up to about 106 + 2|REF| + 2|fasta|. The per-line allowance (|fasta| + 3) * |line|
  (|line| >= |REF| + 7) does not cover this when |fasta| and |REF| are small: a 3-byte FASTA
  `>c\n` and a 1-letter REF give 66 < 102. In reality it is one read, but proving that
  needs margin + ahead + 100 < 2^31, a relation between bare literals and 2^31 that is
  ruled out.
  - C5: the waiting line's back starts at 0 instead of 100 (ms.done and done.b reset back
    to 0n), and slow.reqs' first-try test is `Nat.is_eq(back, 0n)` instead of
    `Nat.is_le(back, 100n)`.
  - The first Want is then Req.of(c, POS - 1, e): at most |REF| reads.
  - Every later miss (back >= 1, reached only by growing after J.fast said None, so REF fits
    its contig) asks the zero window: at most clen + 1 <= |fasta| + 1 reads.
  - Per line: at most 6 + 2|REF| + 2|fasta| <= (|fasta| + 3)(|REF| + 7) for every |fasta|
    and |REF|.
  - Behaviour: the same reads in practice (Req.of's window starts margin letters before
    POS-1 instead of POS-1-100, and still holds every try up to back = margin), and the same
    output (window law). A few more J.fast tries per slow line (back 0, 1, 3, ..., 63)
    before reaching 127.

## C1 and C5 accepted; the output-length lemma (2026-10-28)

The lead took C1 (vd.x keeps back = POS on SAgain and SDone{J.Other{None}}) and C5 (back starts and
resets at 0; slow.reqs' first test is `Nat.is_eq(back, 0n)`). Outputs identical on the 30 + 48 runs.

### Proven: `out_len` (proof_b_budget_run.bend)

    |Report.out(L.run(fasta, vcf, o))| <= 2 * (63 * (|vcf| + 1) + 61 + |args_text(o.args)|)

Generous and spec-level (no machine). The pieces, each in its own file, all `--check-only` clean (the
only TODOs are the 13 spec laws of LAWS.bend, which they import):

- `proof_b_budget_tan.bend`: the normalizer never lengthens a record. `normal_bnd`: Tan.normal's
  variant w of v has `pos(w) + len(ref w) <= pos(v) + len(ref v)`, no more letters in all, as many
  alleles, and none empty (BND). By induction over `right` (trim, shift) and `left` (drop the
  first base), with a step bound for each (`trim_bnd`, `shift_bnd`, `drop_bnd`). It needs the
  alleles nonempty (`lasts_eq([[]])` is True), which a normalized record has (L.valid).
- `proof_b_budget_dig.bend`: numbers. `dlen`: n < 10^k has at most 1 + k digits (via
  proof_b_cut_pos's `show_snoc`). `pos_lt`: a POS field of k characters reads as a number below
  10^k. `qdig`: a number at most POS + r has at most 1 + r + |POS field| digits. Exponents stay
  variables: no closed big Nat anywhere. Also `LIN(k, c, x)` (k x + c as an add chain) with
  `lin_add`, `lin_mono`, `lin_x`, so every bound sums with small literal constants.
- `proof_b_budget_rec.bend`: `judge_len`: a normalized record has at most
  `LIN(10, 10, |body| + 1)` bytes. Field lists measured by `SN(xs) = sum (1 + |x|)`: split gives
  `SN = |s| + 1` (`split_sn`), a field is at most SN, `Rec.put` adds at most the new field,
  joining with one-character separators gives at most SN. POS and END digits by `qdig`; REF and
  ALT by the letter and allele counts of BND; INFO: `Info.end_ok` passing means at most one END
  entry (`end_one`), so `Info.set_end` adds at most 5 + digits. The judge walk reuses
  proof_run_line's `nz_valid` and `first_b`.
- `proof_b_budget_run.bend`: the run invariant. Held bytes `BS(buffer) + |head| + |out|` stay
  within an allowance growing by `LC(line) = 21 (|line| + 1)` per line, with `AD(o) = 61 +
  |args text|` reserved for the two added header lines until the #CHROM line. A stop writes the
  buffer once more, so a halted run's output is within twice the allowance (`INV`, `POST`).
  `lines_lt`: the lines' texts plus one per line are at most `3 (|vcf| + 1)` (a last line without
  LF gains a terminator).

### Where it got hard (research data)

- `+` parameters must have Data types: a `Type`-valued alias (`LE(a, b)` for `{Nat.is_le(a, b) ==
  True}`) is not seen as Data, so an alias can't be a `+` parameter. Fixed by writing the equality
  out (a small script expands the alias before each check).
- Pattern variables of a `+` parameter are affine unless written `+x`: a matched fuel `1n+f` used
  in both the step and the recursive call failed with an empty message at the `case` line.
- `Nat.is_lt(10n+k, 10n)` with k a variable does not reduce (`Nat.cmp(k, 0)` is stuck); the
  absurd cases use `N.lt_add_self`.
- Everything else as before: no match after a let, bare constructor lets need an annotation, no
  forward references, matched parameters in order.
- Each check takes under 3 s. Kernel check: a temporary harness (PROOF.bend's 13 `L.*` forwards plus an
  import of proof_b_budget_run.bend, without MACHINE) passes `--verdict` in 5 s.

### How out_len closes the start bound (the potential, final form)

Write v = |vcf| + 1, F = |fasta|, and lim = Norm.lim() (a bare literal, so `250 <= lim` is a
closed literal fact, cheap). Steps, against `bound = |cs| + 3 + args_len(argv) + v (F + 3)`:
- chunks |cs|, Eof 1, Finish 1;
- Wants and their reads: per line at most `6 + 2|REF| + 2F <= (F + 2) |line|` (C1, C5; a line that
  Wants has |line| >= |REF| + 7), so at most `(F + 2) v` in all (the lines' texts sum to at most v);
- hand-outs and yields: each writes at least lim bytes (String mode: `take` hands out lim; byte
  mode: `ow >= lim` before a yield), so at most `1 + |T.out| / lim <= 1 + (126 v + 122 + 2 |args
  text|) / lim <= 1 + v + |args text|`, by out_len and `250 <= lim`;
- `|args_text(args)| = args_len(args)` (clean keeps lengths); it remains to link `o.args` to argv
  (at most args_len(argv)).

Sum: `|cs| + 3 + args_len + (F + 3) v`, the bound exactly. So the potential is

    need = |cs| + [not eof] + 1                    pieces, Eof, Finish
         + (F + 2) (|intext| + 1) - spent(p)       Wants of the lines still to come
         + 1 + (|T.out| - |O|) / lim               hand-outs and yields still to come
         + reads(next)                             reads of a pending Ask

with `need(start) <= bound` by out_len.

## Left (2026-10-28)

- The per-step budget lemmas (Gap C), stated for every picture of the step's state: walking
  pump/advance again for what each Want asked (fast path once; first slow try `Req.of(c, POS - 1,
  e)` at most |REF| reads; the zero window at most clen + 1 <= F + 1 reads, then decided by
  zero_holds/window_enough), what a Went consumed, and that each Yield or hand-out wrote lim.
  The drive area's statements (StepG/AdvG, S.StP) still have open holes (proof_b_drive.bend 1,
  proof_b_sim.bend 2); these lemmas walk the same pictures.
- `spent(p)` as a Bend definition over the picture (fneed, back, the window), and `need`.
- The `machine` assembly in proof_b_machine.bend: drive induction with `need + reads <= bound`,
  the start bound from out_len, and `o.args` vs argv for args_len.

## The potential, as defined (proof_b_budget_need.bend; the API's need and bi call it)

    need = |cs| + [not eof] + 2 + HO(T, O) + RD(nx) + WA(fa, p, cs)
    HO   = (|T.out| - |O|) / lim()              each yield / hand-out writes >= lim bytes
    RD   = 1 + |rs| for Ask{rs}, else 0         a pending Ask pays its step and reads
    WA   = rem(L1) + sum of LA(l) over the other lines of Text.lines(intext(p, cs))
    LA(l)  = [l not malformed] (RW + 2 ZW),  RW = 1 + max(1, |REF|),  ZW = 2 + FM(fa)
    rem(l) = [l not malformed] ([not H1] RW + [back = 0] ZW + [back < POS] ZW)
    H1     = the window held once the pending Ask is answered (wpA) holds (c, POS - 1, POS - 1 + |REF|)
    bi     = back = 0, or wpA holds the zero window (c, 0, POS - 1 + |REF|) of the line being handled

FM(fa) is the longest contig's raw length; fields are J.pfs's (the code's own). Each driver step is paid
by its input (a piece, the end of the file, or RD of the Ask it answers). A Want made while pumping is
paid by rem: the Req.of window flips H1 (RW >= 1 + its reads), the slow path's zero miss moves back off
0, vd.x's moves back to POS (ZW >= 1 + max(1, POS + |REF|) when REF fits its contig). A yield or a
String-mode hand-out is paid by HO. A finished line leaves WA (its LA is replaced by the next line's
rem <= LA). The flags only go one way within a line, and back and the window reset only between lines.

Start: sum of LA <= (FM + 2) sum |line| <= (|fasta| + 2)(|vcf| + 1); HO <= (|vcf| + 1) + |args text| by
out_len and 248 <= lim; so need(start) <= |cs| + 3 + args_len + (|vcf| + 1)(|fasta| + 3).

Facts the per-step lemmas will need (semantic, in the walks):
- a zero window is asked only after a try's J.fast said Other{None}, so REF fits its contig
  (POS - 1 + |REF| <= clen <= FM);
- with the zero window held and back >= POS, the line decides without asking (window_enough,
  zero_holds); with H1 the slow path's first try and the fast path do not ask (req_holds, against);
- a byte-mode Yield's output has at least lim bytes (ow at most the output buffer);
- |O ++ t| <= |T.out| (the report's output extends what was written; guard covers the #CHROM line);
- a line that Wants is not malformed, and its Req.of window has |REF| letters;
- the line being handled is the first line of Text.lines(intext(p, cs)).

## Change to need (2026-10-28): the fast path's Want gets its own term

A risk listed above was false: "with H1 the fast path does not ask". The fast path (`against`,
`win.cover`) asks when `POS - 1 + |REF| > min(window end, clen)`, while H1 (serve's `holds`) clips the
read's end to the contig. Counterexample: contig c = ACGTACGTAC (10 letters); line 1 on c at POS 1 asks
Req.of(c, 0, 1), whose window reads all of c; line 2 `c 10 . CA ...` (REF past the end): holds(c, 9, 11)
is True, but against gives WNeed, and fast.need asks Req.of(c, 9, 11). H1 was already True, so the old
rem had nothing for this Want. (The line then ends as REF_MISMATCH; the code is fine.)

Also, ms.want sets fneed to False, so a byte-mode line that switches to the String mode mid-line (Rs's
third flag: output buffer >= 2^29) could reset an fneed term.

New definition (only rem and LA change):

    rem(l) = [l not malformed] ([not fneed and byte mode] RW + [not H1] RW + [back = 0] ZW + [back < POS] ZW)
    LA(l)  = [l not malformed] (2 RW + 2 ZW)

fast.need runs only with fneed False in the byte mode and sets it (drops RW). The slow path's first miss
flips H1 (drops RW). The String mode never runs the fast path, and a switch to it only lowers rem.
2 RW + 2 ZW <= 2 |REF| + 8 + 2 FM <= (FM + 2)(|REF| + 8), so the start bound still holds.

Checked and true: J.fast says Other{None} only after ref_check found REF fits (start + |REF| <= clen), so
zero windows ask at most 1 + FM reads; a byte-mode Yield hands out exactly ow >= lim bytes (take
truncates ob to ow); the fast path asks only for a nonempty CHROM (fast.run.q's s < e0).

## Change to need (2026-10-28): computed from the machine state mkSt(fa, p)

need and bi now read the machine state `S.mkSt(fa, p)` (BN.needS, BN.biS), not the picture's fields. The
values are the same: mkSt copies o, eof, back, asked and fneed; the text functions are the picture ones
on mkSrc/mkPd (srctext(SBP{len, t, d, at}) is srcT(SB{C.BT(len, t), at}) by definition); holds is
serve's test on the window itself (holdsW), and a pending Ask counts by its window (coversA, the reads'
contig, first start and last end). Why: AdvG gives the next state as some picture p2 with
`st == mkSt(fa, p2)`, and the per-step lemmas meet several pictures of one state (the step lemmas',
the adv area's, the API's). With need a function of the state, `sst(step) == mkSt(fa, p2)` rewrites
need(p2) to needS(sst(step)) whatever p2 is. Nothing else changes (the API statements are the same).

## Change to need (2026-10-28): HO divides by 256, not lim()

A yield or hand-out meets one of three thresholds: the byte mode's `U32.is_le(1073741824, ow)` (a word),
the String mode's `Nat.is_le(lim(), ql)` (a bare literal), and the hand-outs' `take_w(t, 1073741824)`
(a word). Words and bare literals cannot be related in a proof (any conversion between them normalizes the
word's U32.to_nat to unary), and a closed Nat.pow or U32.to_nat inside need's body would blow up whenever
need is unfolded. So HO divides by a small bare literal every hand-out provably exceeds:

    HO(T, O) = (|T.out| - |O|) / 256

Each yield or hand-out writes at least 256 bytes: `256 <= 2^30` holds natively on words (`U32.is_le(256,
1073741824)`) and on bare literals (`256n <= lim()`), so each world gets its own small fact. Start: |T.out|
<= 126 v + 122 + 2 |args text| (out_len, v = |vcf| + 1) gives HO <= v + |args text|, as before.

## need is final (2026-10-28)

need and bi are as defined in proof_b_budget_need.bend now (state level, `HO = (|T.out| - |O|) / 256`,
rem with the fast-path term). No further change planned; if one is needed it is announced here first.

## For pb-run (and pb-cache, pb-enc): self-contained lemmas with fixed statements

Each lemma goes in its own new file of yours (say proof_b_bud_<name>.bend). It may import anything except
proof_b_budget_step.bend (which will import yours and call it). The predicates are in
proof_b_budget_need.bend (as BN) and proof_b_budget_sdefs.bend (as BD). Other aliases as in
proof_b_budget_step.bend: S = proof_b_simdefs, PC = proof_b_cachedefs, P = proof_b_defs, DD =
proof_b_drivedefs, E = bytes_enc, M = MACHINE, J = norm_line, Norm = norm, R = run, B = types,
Pr = protocol. The statements are fixed; tell me (here) if one is false or awkward, with the reason. Copy
each statement exactly (they already sit in proof_b_budget_step.bend with `?TODO` bodies, except Z1 to Z3).

### Suggested for pb-run (spec and run pictures)

R1 `hop`: what a state stands for begins with what the driver wrote.

    def hop(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
      +hr: {S.report(fa, cs, O, N, p) == T : R.Report},
      +hg: {S.guard(O, N, p) == True{} : Bool}) ->
      {Nat.is_le(String.length(O), String.length(R.Report.out(T))) == True{} : Bool}

  (L.run.go and R.finish only add to out once the run is in the body; before it, guard makes O empty.)

R2 `yield_out`: a yield hands out at least 256 bytes (byte mode: take hands out ow bytes, ow >= 2^30,
by RunInv; String mode: ql >= lim() and ql = |cat(qs)| by md_ok, and take_w(.., 1073741824) hands out
min(|cat|, 2^30); use `U32.is_le(256, 1073741824)` and `256n <= lim()`, both closed and native, never a
word next to a bare literal).

    def yield_out(+fa: List<&2, B.Contig>, +p: S.StP, +hw: {S.WF(fa, p) == True{} : Bool}, +hy: {BD.yc(p) == True{} : Bool}, +t: String,
      +ht: {BN.sout(Norm.out(S.mkSt(fa, p), Pr.Ask{Nil{}})) == Some{t} : Maybe<&2, String>}) ->
      {Nat.is_le(256n, String.length(t)) == True{} : Bool}

R3 `out_was`, `out_bi`, `out_snx`: the step's end (out) keeps the sources' text, the line end, eof, back,
the window, asked, fneed and the mode, and the next.

    def out_was(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
      {BN.WAS(fa, BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.WAS(fa, S.mkSt(fa, p), cs) : Nat}
    def out_bi(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +nx: Pr.Next) ->
      {BN.biS(BN.sst(Norm.out(S.mkSt(fa, p), nx)), cs) == BN.biS(S.mkSt(fa, p), cs) : Bool}
    def out_snx(+fa: List<&2, B.Contig>, +p: S.StP, +nx: Pr.Next) -> {BN.snx(Norm.out(S.mkSt(fa, p), nx)) == nx : Pr.Next}

  (proof_b_drive_out.bend's left_eq gives left(mkSrcs(src)); md.take keeps the mode.)

R4 `fin_bud`: the end of the run keeps the budget (Finish: RD = 0; the String mode's output past 2^30:
Ask{[]} with 2^30 >= 256 bytes handed out, so HO drops by one; WA and bi as before).

    def fin_bud(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +p: S.StP,
      +hw: {S.WF(fa, p) == True{} : Bool},
      +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}) ->
      BD.BudS(fa, T, cs, O, BN.WAS(fa, S.mkSt(fa, p), cs), Norm.finish(S.mkSt(fa, p)))

  (proof_b_budget_ho.bend's ho_drop does the HO arithmetic.)

### Suggested for pb-enc (the driver inputs: as step_chunk / step_eof / step_ref, plus WA and bi)

F1 `chunk_fed`, F2 `eof_fed`, F3 `ref_fed` (statements in proof_b_budget_step.bend; BD.FedG): the state
after feed / feed_eof / set_win is some picture q that is good, stands for the report, has the guard and
nothing asked, has WA at most the state's before (the text still to come is the same, as the drive area's
rep_lines hypotheses show; back, fneed and the mode are kept; set_win turns a pending Ask's window into
the held one), and keeps bi. For F3, `BN.coversA(Some{rs}, c, a, b)` (the Ask's window) gives `BN.holdsW`
of the window set_win makes; proof_b_budget_lem.bend has srcT_pic / pdT_pic / text_pic (state text =
picture text).

### Suggested for pb-cache (windows)

Z1 `fast_none_fits`: J.fast says "the window is too small" only after REF fits its contig (ref_check's
`fits`).

    def fast_none_fits(+clen: Nat, +off: Nat, +raw: String, +fs: List<&2, String>, +body: String,
      +h: {J.fast(Some{J.Known{clen, off, raw}}, fs, body) == J.Other{None{}} : J.Fast}) ->
      {Nat.is_le(Nat.add(Nat.sub(B.Rec.pos(fs), 1n), String.length(B.Rec.field(fs, 3n))), clen) == True{} : Bool}

Z2 `zero_decides`: with the line's zero window held and back >= POS, the verdict does not ask (the first
try starts at 0, is served, and J.fast decides: window_enough).

    def zero_decides(+fa: List<&2, B.Contig>, +wp: PC.WP, +back: Nat, +body: String,
      +hb: {PC.fa_bytes(fa) == True{} : Bool},
      +hwp: {PC.wp_ok(fa, wp) == True{} : Bool},
      +hz: {BN.holdsW(PC.mkWin(fa, wp), B.Rec.field(J.pfs(body), 0n), 0n,
        Nat.add(Nat.sub(B.Rec.pos(J.pfs(body)), 1n), String.length(B.Rec.field(J.pfs(body), 3n)))) == True{} : Bool},
      +hp: {Nat.is_le(B.Rec.pos(J.pfs(body)), back) == True{} : Bool}) ->
      {BD.is_vwant(Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body)) == False{} : Bool}

Z3 `held_serves`: a window that holds a read serves it.

    def held_serves(w: Norm.Win, +c: String, +a: Nat, +b: Nat,
      +h: {BN.holdsW(w, c, a, b) == True{} : Bool}) ->
      {BD.sv_hit(Norm.serve(w, c, a, b)) == True{} : Bool}

  (Z3's w is used twice in the statement; if that is refused, state it for `PC.mkWin(fa, wp)` with +fa,
  +wp instead and tell me.)

### Mine (in progress)

adv_bud / adv_bi (advance's paths: WA and bi, using Z1 to Z3), the pump (done: pb_go, go_bud), and the
API's bud_chunk / bud_eof / bud_ref (arithmetic on top, next).

Note (2026-10-28): the API's step projections sst, snx, sns, sout now forward to BN.sst etc. (same
bodies, now in proof_b_budget_need.bend), so the budget's lemmas, stated with BN's, meet the API's by one
unfolding (two copies of a match do not unify on a stuck step). No statement changed.

## Status (2026-10-28, later)

- The API's bud_chunk, bud_eof, bud_ref are proven (proof_b_budget_step.bend: bud_*_h) from go_bud (the pump
  induction, proven) and the dispatched sub-lemmas: chunk_fed, eof_fed, ref_fed (pb-enc), hop, yield_out
  (pb-lines), out_was, out_bi, out_snx, fin_bud (pb-run). The API file has no hole of its own.
- Left with me: adv_bud and adv_bi (advance's paths), which use pb-cache's Z1 to Z3.

## Change to need (2026-10-28): while an Ask is pending, held means the Ask's window

pb-enc found F3 (ref_fed) false as stated (proof_b_bud_ref_cex.bend; notes/bytes_proofs_drive.md "Budget
lemmas F1-F3"): heldA counted a read the old window held while an Ask was pending, and set_win throws that
window away, so WA could grow (4 -> 6). Fix (pb-enc's, taken):

    heldA(w, asked, c, a, b) = coversA(asked, c, a, b)   when asked is Some (an Ask pending)
                             = holdsW(w, c, a, b)          when asked is None

F3's statement is unchanged (it reads BN's definitions) and now follows from coversA => holdsW of the
window set_win makes. The cost moves to adv_bud's Want case, which must show the Ask covers the line's
windows, and it does: every Want of the line being handled covers (c, POS - 1, POS - 1 + |REF|) (Req.of's
window starts margin() letters before and ends at or after it; parts(c, 0, ..) starts at 0), and the zero
windows also cover (c, 0, POS - 1 + |REF|). need is otherwise unchanged; bi reads heldA too.

## For pb-cache: c.ms.sb and c.ms.sl (String-mode lines of the budget walk)

Both are standalone defs in proof_b_budget_adv.bend (lines ~98 and ~110), with `?TODO` bodies. Write them
in proof_b_budget_ms.bend (it may import proof_b_budget_need.bend as BN, proof_b_budget_sdefs.bend as BD,
proof_b_bud_win.bend, the adv area's files, but not proof_b_budget_adv.bend or proof_b_budget_step.bend),
then replace only those two bodies by calls. StM is now BD.StM (proof_b_budget_sdefs.bend). Statements,
copied exactly:

    def c.ms.sb(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
      +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
      +hb: {PC.fa_bytes(fa) == True{} : Bool},
      +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
      +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
      +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
      +hx: {R.RunSt.halt(s) == False{} : Bool},
      +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
      BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, None{}, fneed),
        Norm.ms.sb(o, s, qs, ql, at, NF.lf(C.BT(len, t), at), P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), fneed))

    def c.ms.sl(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
      +o: B.Opts, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +q: String, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool,
      +hb: {PC.fa_bytes(fa) == True{} : Bool},
      +hw: {S.WF(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
      +hr: {S.report(fa, cs, O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == T : R.Report},
      +hg: {S.guard(O, N, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)) == True{} : Bool},
      +hx: {R.RunSt.halt(s) == False{} : Bool},
      +hbi: {BN.biS(S.mkSt(fa, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed)), cs) == True{} : Bool}) ->
      BD.AdvC(fa, cs, BD.StM(o, S.MSP{s, qs, ql, None{}}, Con{P.SLP{q}, rest}, pd, eof, back, wp, None{}, fneed),
        Norm.ms.line(o, s, qs, ql, q, back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp)))

Aliases as in proof_b_budget_adv.bend (NF = norm_fast, C = lawful-bytes/proof_core, AT =
lawful-arrays/proof_tree). What each outcome must give (BD.AdvC):
- Went past the line (ms.done): WA drops. The text loses exactly its first line (lines(before) = l <>
  lines(after); the adv area's itx / SPLIT for a byte source, `SL{q} <> rest` -> rest for a text line),
  then `rem(next) <= LA(next)` and `rem(l) >= 0`. bi: back is 0 after the line (ms.done resets it).
- Went with the text kept (ms.part.len: the partial line moves into pend): WA and bi equal (back, the
  window, fneed kept; fast_left is False in the String mode either way).
- Want (ms.want): `1 + |reqs| + WA(after) <= WA(before)`. In the String mode fast_left is False on both
  sides, and ms.want sets fneed False (harmless there). The verdict's Want is one of:
  the first try's miss (back 0, Req.of(c, POS - 1, e)): H1 was False (the miss means the window did not
  hold the read: Z3's contrapositive), the Ask covers it, so RW >= 1 + |reqs| is released
  (|Req.of| <= max1(|REF|), proof_b_budget.bend's reqof_len);
  the grown miss (back >= 1 after a try said Other{None}, parts(c, 0, e)): ZW for back = 0 -> >= 1 (or for
  back < POS if the miss's back is >= POS ... the [back = 0] term drops in any case since the stored back
  was 0, or else bi held the zero window and Z3 rules the miss out), with |parts(c, 0, e)| <= max1(e) <=
  1 + FM by Z1 (e <= clen) and proof_b_budget.bend's parts_len;
  vd.x's (back := POS): the [back < POS] term drops (stored back < POS, else bi's zero window and Z2 rule
  it out), |parts(c, 0, POS + |REF|)| <= max1(e + 1) <= 1 + FM (Z1).
  bi after a Want: back >= 1 only for the zero windows, whose Ask covers (c, 0, e).

## The byte-mode line (c.mb.sb) split into three (2026-10-28)

c.mb.sb (proof_b_budget_adv.bend) is proven: Run.inbody, then the decoded paths (c.dec) or the fast path
(c.fast). Three standalone lemmas, statements fixed in their files (`?TODO` bodies):

- **vd_bud** (proof_b_bud_vd.bend): the slow path's verdict and the budget, for both modes (c.ms.sb/sl
  need it too; pb-cache's c.ms.* should use it rather than redo it). `BD.VB` (proof_b_budget_sdefs.bend):
  a VWant{w2, reqs, back2} pays `1 + |reqs|` from rem without the fast path's term (`fl = False` on both
  sides: a slow Want never changes it), with nothing asked before and `Some{reqs}` after; and after it
  back2 = 0 or the Ask covers the line's zero window. Why it holds (vd.x's three Wants):
  - the first try's miss (back 0): the window did not hold (c, POS - 1, e) (serve's test is holdsW), so
    [not H1] drops RW; the Ask Req.of(c, POS - 1, e) covers it, |Req.of| <= max1(|REF|)
    (proof_b_budget.bend's reqof_len);
  - the grown miss (the try's back >= 1, parts(c, 0, e)): the stored back was 0 (else bi's zero window
    holds every later read: Z3 and holdsW's a0 <= a), so [back = 0] drops ZW; a try said Other{None}
    before it, so e <= clen <= FM (Z1, find_fm), |parts| <= max1(e) <= 1 + FM (parts_len);
    [back < POS] does not grow (back2 < POS implies 0 < POS);
  - out of tries or Other{None} at the end (back := POS, parts(c, 0, POS + |REF|)): the stored back is
    < POS (else bi's zero window and Z2 rule it out), so [back < POS] drops ZW; the last try said
    Other{None}, so POS + |REF| = e + 1 <= clen + 1 <= FM + 1;
  - in every case H1 and the back terms do not grow (each Ask covers (c, POS - 1, e)), and the gate holds
    (a Want means judge_fs(None) said None, so the line is not malformed).
- **c.dec** (proof_b_budget_dec.bend): the byte mode's decoded paths, mirroring proof_b_adv_dec.bend's
  dec (header lines: hold / write; a partial line: part; a line > 2^28: to_str; the slow path: VRes and
  VSame end in done.b, VWant in want.b with fneed kept). Leaves: proof_b_budget_mb.bend's `went_done` (a
  line handled; any state after; needs the adv area's SPLIT and the line's nolf, which dec's helpers
  carry); the text-kept leaves (to_str, part: WA equal, bi equal; like proof_b_budget_adv.bend's to_ms_c);
  vd_bud for VWant (the byte mode's fl = not fneed is the same on both sides). Note: the code's line is
  Norm.line(btext), WA's is B.Text.line(btext); their bodies must agree (the adv area has the link).
- **c.fast** (proof_b_budget_fast.bend): the fast path, mirroring proof_b_adv_fast.bend's F.top: a hit
  ends in done.b (went_done); WNeed with fneed False is fast.need's Want (fneed False -> True drops RW;
  the Ask Req.of(c, POS - 1, POS - 1 + rl) covers (c, POS - 1, e), rl = |REF| by the cut area's
  pass_fields); everything else goes to c.dec with the same fneed.

Suggested split: vd_bud to pb-cache (with c.ms.*), c.dec to a free agent (pb-enc: the decoded bytes),
c.fast to me.

## Change to bi (2026-10-28): the zero window also fits (REF within its contig)

Found while writing c.fast's Want leaf (F.need). The fast path asks when `against` says WNeed, which tests
the window unclipped (`POS - 1 + |REF| <= min(window end, clen)`), while holdsW clips. So with back >= 1
and bi's zero window held (clipped), a REF running past the contig's end would still let fast.need ask,
replacing the window; a later slow miss would then be unpaid. That state is unreachable (back >= 1 only
after J.fast said Other{None}, so REF fits: Z1), but bi did not record it. bi now records it, in the
window (no signature change; need unchanged):

    bi.ls(back, w, m, l <> t) = back = 0 || heldZ(w, m, lchrom(l), lend(l))
    heldZ(w, Some{rs}, c, e) = zfit(w, c, e) && coversA(Some{rs}, c, 0, e)   (Ask pending: the served window fits)
    heldZ(w, None, c, e)     = zheld(w, c, e)                                (the window holds (c, 0, e) and fits)
    zfit(w, c, e):  w is WKnown / WStr for contig c with e <= its clen (else False)
    zheld(w, c, e): w is WKnown / WStr for c, a0 = 0, min(e, clen) <= min(b0, clen), and e <= clen

Effects: BD.VB's bi part becomes `back2 = 0 || heldZ(w2, Some{reqs}, c, e)` (vd_bud: the try that said
Other{None} was served by w2, whose clen is the answer's, e <= clen by Z1); F3 (ref_fed) must show
zheld of set_win's window from zfit(old window) and coversA (same contig, so the same clen); the fast
Want happens only with back = 0 (with back >= 1, zheld and fits make against cover: Z4 below), so bi
after it is trivial. Other steps keep back, the window and asked, or reset back to 0.

New lemma for pb-cache (Z4, file proof_b_bud_win.bend or a new one): with the zero window held and
fitting, the fast path's window test is not WNeed (statement in proof_b_budget_fast.bend once written).

### Z4 for pb-cache (statement fixed; new file of yours, e.g. proof_b_bud_z4.bend)

With the line's zero window held and fitting (bi's zheld), the fast path's window test does not say
WNeed (win.cover's `offu <= p` and `end <= offu + rlen` hold: offu = min(0, clen) = 0, and end = POS - 1 +
|REF| <= clen with the window reaching it). Aliases as in proof_b_budget_fast.bend (CD = proof_b_cachedefs,
FH = proof_b_adv_hit); add hypotheses the window's contig name bytes need (mb_win) if you must, and say so.

    def against_zero(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
      +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
      +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
      +hb: {CD.fa_bytes(fa) == True{} : Bool},
      +hwp: {CD.wp_ok(fa, CD.WPKnown{c, a, b}) == True{} : Bool},
      +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
      +hs: {U32.is_le(at, len) == True{} : Bool},
      +hp: FH.PASS(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
      +hse: {U32.is_lt(at, e0) == True{} : Bool},
      +hz: {BN.zheld(CD.mkWin(fa, CD.WPKnown{c, a, b}), P.btext(len, t, at, (e0 - at : U32)),
        Nat.add(Nat.sub(U32.to_nat(pos), 1n), U32.to_nat((e3 - e2 - 1 : U32)))) == True{} : Bool}) ->
      {BD.wo_need(Norm.against(CD.mkWin(fa, CD.WPKnown{c, a, b}), C.BT(len, t), at, e0, pos, (e2 + 1 : U32), (e3 - e2 - 1 : U32))) == False{} : Bool}

## From pb-cache (2026-10-28): vd_bud, c.ms.sb, c.ms.sl done

- **vd_bud** (proof_b_bud_vd.bend) is proven, against the strengthened bi (heldZ / zfit). The slow path's
  tries are walked with an invariant (INVX): a try still to come after "too small" has
  back <= b, back < POS - 1, POS - 1 + |REF| <= FM (Z1 + find_fm), 1 <= b, and zfit of the window that
  served it (the try was served by it; Z1 gives e <= its clen); a decided try is not Other{None}; a miss
  already pays (pay_w1: first try, [not H1] drops RW; pay_w2: grown miss, [back = 0] drops ZW; pay_w3: out
  of tries, [back < POS] drops ZW). The gate holds because judge_fs(None) said None. Statement unchanged
  (hbi still asks holdsW of the zero window; c.ms gets it from bi's zheld).
- **c.ms.sb / c.ms.sl** (proof_b_budget_ms.bend: c_ms_sb, c_ms_sl) are proven and wired: the two bodies in
  proof_b_budget_adv.bend are now one call each (import `./proof_b_budget_ms.bend as BMS`; nothing else
  changed there). Leaves: a consumed line (done_c: WA drops by the line's rem, rem(next) <= LA(next),
  back 0 so bi holds), the partial line to pend (cpart.k: same text, WA and bi equal), a Want (want_c:
  vd_bud's VB plus the text kept, the line back in front).
- Shared tools for pb-alleles' c.dec: `BV.vd_bud` only (the rest is String-mode).
- Next: Z4 (against_zero).
- **Z4 (against_zero) is proven** (2026-10-28). Statement in proof_b_bud_z4.bend (pb-cut's stub, kept), with
  **one hypothesis added after hwp: `+hcl: {Norm.len_le(c, 268435456) == True{} : Bool}`** (the window's
  contig name is at most 2^28 bytes; mb_win gives it in the byte mode, with is_bytes(c), which the proof
  derives itself). It is needed to build the name's byte buffer (NR.of_str) that the CHROM test compares
  against. The body is one call to proof_b_bud_z4k.bend's against_zero.k (my file; please do not overwrite
  it). How: zheld names the window's contig as the CHROM text and gives a = 0 and e <= min(b, clen); the
  CHROM bytes then match (chars is injective; the lengths agree), cover holds (offu = 0 <= POS - 1, and
  POS - 1 + |REF| <= the window's bytes; PASS gives POS >= 1, so POS - 1 does not wrap; word sums through
  to_nat_lt_p, no closed big Nat compared), and fits only picks WMiss or a REF test (cache's ah.f0 / ah.q).
