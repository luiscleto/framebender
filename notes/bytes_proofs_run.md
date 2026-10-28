# Phase B area "run": notes

## Status (2026-10-28, final): run area done

All deliverables in `proof_b_run.bend` are proven, with no holes: `run_start`, `run_bytes`,
`run_head_empty`, `run_to_spec`, `run_tick`, `run_head_hold`, `run_head_write`,
`run_body_line`, `run_fast_done`, `run_same_done`, `run_finish`, `run_take`,
`run_reserve`, `run_same`, `of_str`. Checked through `test/bcheck.sh` with
`--check-only` and with `--verdict` (both print `ALL PROOFS CHECK`). Statements are as the
lead last gave them; I changed none.

### RunInv (in `proof_b_rundefs.bend`, `RD.inv.k`)

Eleven parts, on the fields of `P.RunP{n, i, h, c, cb, e, la, f, b, bn, tl, k, ob, ow, ns, x}`:

1. ob is a well-formed block of its tree's depth (`D.ok(ob, tdepth(obt))`);
2. `|ob| <= 2^30` (as `U32.is_le(obl, 1073741824)`);
3. cb is well formed, and 4. its bytes spell `c` (or "" when `c` is None);
5. `x || ow + lens(items(f, b)) == |ob|`: the bytes after `ow` are exactly the buffered
   items' texts, in order (front, then back reversed);
6. `x || bn == |f| + |b|`;
7.–8. every key in the front and in the back is at most `tl` (the last key added);
9. the held header `h` is bytes;
10. `pre`: before #CHROM (`i` False), ob is empty, both lists are empty, and if not stopped
    there are no notes;
11. `ow <= |ob|`.

Parts 5 and 6 are weakened on stopped runs (`x`): after an UNSORTED stop the machine drops
the front list but leaves the texts in ob, and nothing reads them after a stop.

### How the body deliverables go

`run_body_line` cases on the result. Broken, NoContig and Problem under `-s` stop the run
(`bl.stop`: `x := True`, notes grow, RunInv via `FN.pr`). Problem without `-s` and Skipped
pass the line's own bytes through `keyed` (`NR.Raw`). Normalized cases on
`String.eq(t, body)`: equal → Raw (the source bytes already are `t ++ term`), else `NR.Own`
with the new text, sized from `hfit` (`res_fits` → `|t ++ term| <= 2^30 - |ob|`).
`keyed` (`KD.kd_t`) goes to `same_run` (`SR.sr_t`) or `new_run` (`NR.nr_t`, which
uses `of_str` for the new CHROM through `hcb`/`hcl`). Both add the item (`AD.add_t`: at the
end, or in the middle through pb-lines' `proof_b_run_ins.bend`), then flush ready items
(`FL.flush_t`, one induction on the fuel over front and back lists, writing or stopping
UNSORTED). `run_fast_done`/`run_same_done` are the Raw path with the length the fast
scanners measured (`BL.fd_t`, `BL.sd_t`); `run_finish` is the flush with all items
ready, then the end notes (`FN.fin_t`).

Files (all `proof_b_run_*.bend`, plus `proof_b_rundefs.bend`):
- `proof_b_rundefs.bend` (definitions only): `RunInv` and its parts (`tdepth`, `lens`,
  `keys_le`, `items`, `pre`, `no_notes`, `inv.k`). No closed big number in it.
- `proof_b_run_inv.bend`: RunInv taken apart (`inv_parts`, `pr1`..`pr11`) and built
  (`inv_mk`, `parts_h`, `parts_ob`, `parts_ns`), `SRT` (specRun as a function of ob's
  text), bytes of texts, `pre_take`.
- `proof_b_run_lem.bend`, `proof_b_run_num.bend`: Bools, block depth, `4 << d`, `NR.depth`
  bounds (`depth_bound`, `depth_le`, `pinv`, `pinv_le`), no-wrap (`mul2_fits`), `b8`.
- `proof_b_run_sz.bend`: `Norm.len_le` bounds to `Nat.pow` (through `proof_b_lit.bend`).
- `proof_b_run_buf.bend`: buffers on mirrors, each named by a Data tree where possible:
  `room` (`RT`), `put_str` (`pstl`/`pstt`), `reserve` (`RVT`); `put_bytes` (through
  `FE.append_*` and `C.bmirror`: an existential tree), list/string facts.
- `proof_b_run_take.bend`: `run_take`. `proof_b_run_same.bend`: `run_same`.
- `proof_b_run_head.bend`: `run_head_write`.
- `proof_b_run_flush.bend`: the flush loop (`FS`, `FLR`, `loop`, `flush_t`).
- `proof_b_run_fin.bend`: `run_finish` (`fin_t`), `pr` (RunInv of a stopped run).
- `proof_b_run_add.bend`: adding an item (`put_txt_t`, `add_t`), using `proof_b_run_ins.bend`.
- `proof_b_run_sr.bend`, `proof_b_run_nr.bend`, `proof_b_run_kd.bend`: `same_run`,
  `new_run`, `keyed`.
- `proof_b_run_bl.bend`: `run_fast_done` (`fd_t`), `run_same_done` (`sd_t`),
  `run_body_line` (`bl_t`, `bl.stop`, `bl.kr`, `nm.c`).
- `proof_b_run_ins.bend`: written by pb-lines (the insert side), imported by `add`.
- `proof_b_run_cex.bend`: the round-1/2 counterexamples against the old statements, kept
  as a record; it is a runnable program, not a proof file.

## Budget lemmas R3 and R4 (2026-10-28): `proof_b_bud_out.bend`

For pb-cut's budget (notes/bytes_proofs_budget.md, "For pb-run"): `out_was`, `out_bi`, `out_snx` (R3)
and `fin_bud` (R4), statements copied verbatim from `proof_b_budget_step.bend`, which this file does
not import. All check; the file has no TODO of its own (the 16 reported come with
`proof_b_drive_out.bend`'s imports, which report the same 16 alone).

- R3: `out` rewrites `left(mkSrcs(src))` (`DO.left_eq`), then `out.k` of any take result keeps every
  field but the mode (`ok_st`, `ok_nx`, by matching the pair), and take keeps what WA reads of the
  mode (`fl_take`: byte mode stays byte mode, String mode stays String mode). bi does not read the
  mode at all.
- R4: byte mode: `fin.mb` on `NR.finish`'s pair, then Finish (RD 0, WA as before, HO only drops:
  `fin_ar`). String mode, report not taken yet (`fb_none`) or code set (`fb_some`): `fin.ms.go`
  either fits (Finish) or hands out `take_w(cat, 2^30)` and asks `Ask{[]}` (`bud_ask`): the handed-out
  text is the `now` part (via `PR.of_str` and `ENC.out_ok`), which has at least 256 characters when the
  queue does not fit (`lo`: `take_w` of a text longer than w hands out exactly `to_nat(w)`, proved for
  any word w, then `U32.is_le(256, 1073741824)` natively; only `U32.to_nat(256)` is ever converted).
  HO then drops by one (`ask_ar`, with `HO.ho_drop`). The queue's bytes come from `md_ok` and
  `DF.fin_out_bytes`.
- A `+` parameter needs a Data type, and `Norm.Md` / `NR.Run` are not Data, so a run value can be
  used once in a proof term. Each lemma therefore matches the take/finish pair once and proves
  everything about the resulting step in that branch (`bud_mbk`, `bud_msf`, `bud_ask.k`); the
  R3 lemmas take the mode as its Data picture (`S.MdP`).

## Asked of pb-lines: `proof_b_run_ins.bend` (the insert side; delivered and used)

Mirror-level facts about `NR.ins.start` (no RunInv; it may import `proof_b_rundefs.bend` for
`RD.lens` and `RD.keys_le` only). Below, `I = NR.ins.start(xs, NR.Ck.key(x))` (or
`NR.ins.start(xs, k)` where there is no x). Exact statements:

```
# Accessors (definitions in proof_b_run_ins.bend)
def ipre(i: NR.Ins) -> List<&2, NR.Ck>     # Ins{p, n, r} -> p
def iplen(i: NR.Ins) -> U32                # -> n
def irest(i: NR.Ins) -> List<&2, NR.Ck>    # -> r

def ins_eta(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {NR.ins.start(xs, k) == NR.Ins{ipre(NR.ins.start(xs, k)), iplen(NR.ins.start(xs, k)), irest(NR.ins.start(xs, k))} : NR.Ins}

def ins_split(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {NR.append_ck(ipre(NR.ins.start(xs, k)), irest(NR.ins.start(xs, k))) == xs : List<&2, NR.Ck>}

# The prefix's text length, as the word mid adds up (no wrap while xs's lengths fit).
def ins_plen(+xs: List<&2, NR.Ck>, +k: Nat,
  h: {Nat.is_le(RD.lens(xs), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  {U32.to_nat(iplen(NR.ins.start(xs, k))) == RD.lens(ipre(NR.ins.start(xs, k))) : Nat}

# R.insert of x's item into the items of xs is x put at the split, its text tx put at
# the prefix's text length (t holds exactly the texts of xs).
def ins_mid(+xs: List<&2, NR.Ck>, +x: NR.Ck, +chrom: String, +t: String, +tx: String,
  ht: {String.length(t) == RD.lens(xs) : Nat},
  hx: {String.length(tx) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t))
    == NR.spec.items(NR.append_ck(ipre(NR.ins.start(xs, NR.Ck.key(x))), x <> irest(NR.ins.start(xs, NR.Ck.key(x)))), chrom,
         String.append(String.take(t, RD.lens(ipre(NR.ins.start(xs, NR.Ck.key(x))))),
           String.append(tx, String.drop(t, RD.lens(ipre(NR.ins.start(xs, NR.Ck.key(x)))))))) : List<&2, R.Item>}

# At the end: every key of xs is at most x's.
def ins_end(+xs: List<&2, NR.Ck>, +x: NR.Ck, +chrom: String, +t: String, +tx: String,
  hk: {RD.keys_le(xs, NR.Ck.key(x)) == True{} : Bool},
  ht: {String.length(t) == RD.lens(xs) : Nat},
  hx: {String.length(tx) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t))
    == NR.spec.items(NR.append_ck(xs, [x]), chrom, String.append(t, tx)) : List<&2, R.Item>}
```

Notes: no sortedness is needed (`ins.start`'s prefix is the longest one with keys <= k,
which is `R.insert`'s walk). `ht` makes each item's text land where `spec.items` reads it.
Every parameter is `+` so the lemmas can be called with any terms.

## Round 1 and 2 (statements)

Brief: `notes/briefs/BYTES_PROOFS_RUN.md`. Skeleton: `proof_b_run.bend` (unchanged).

## Status (2026-10-27): stopped, statements false

Nothing is proven yet. Six of the 13 deliverables are false as stated. Each one fails on states
that any `RunInv` has to admit, so the fix belongs in the statements, not in `RunInv`. Every
counterexample was run on concrete values: `bend proof_b_run_cex.bend` prints
`[False, True, False, False, False, True, False, False, False]`, where each False is a
counterexample and the two Trues are controls (the states just before the failing step agree).

Why `RunInv` cannot help: `run_start`, `run_tick` and the body/head deliverables chain from
`NR.start()`. Their preconditions (`hok`, `hs`, `ht`, `hbig`, `hk`, ...) all hold for small
`E.enc` buffers. So `RunInv` must hold on every state in the traces below. And `p2` is forced
by `... == P.mkRun(p2)`, since constructors are injective.

1. **Body lines after an UNSORTED stop** (`run_fast_done`, `run_same_done`, `run_body_line`).
   run.bend's stopped state keeps a `buf` and `last` that the machine cannot reproduce:
   - (A) `run_same_done`/`run_body_line`. Lines chr1:100, chr2:100, chr1:200 with w = 1000.
     `R.new_run.go`'s "run ended" case stops on the *original* state: buf = [chr2:100],
     last = None, though the texts were written to out. The machine has flushed: buf = [],
     last = chr2:100.
   - (B) `run_fast_done` too. One CHROM, w = 10, keys 100, 200, 50, 300. Before 300 the
     machine has front [50, 200]. 300 goes to back, and 50 is ready and below last (100).
     run.bend: buf = [] (`emit.ready` stops on the state with `Nil` buf). Machine:
     `flush.stop` keeps back = [300], so `specRun`'s buf = [300].
2. **Body lines on a stopped run** (E, all three body deliverables). With w = 0: c:100,
   c:50 (UNSORTED; both agree), then c:200. `R.same_run` does not look at halt, so it writes
   the item. `NR.flush.step` writes nothing once halted. So out, buf and last differ.
3. **`run_head_write`**. `R.head_line(True)` replaces out. `NR.head_line` appends the header
   to `ob` and sets `ow` to all of it.
   - (C) Two #CHROM lines: run.bend's out is the second header, the machine's both.
   - (F) A body line before the #CHROM line (the body deliverables allow inbody False):
     the machine's out is the record's text, then the header.
4. **`run_finish`** (G). A body line before any #CHROM line, written at once (w = 0), then
   the end: run.bend reports out = "" (NO_HEADER); the machine's out is the record.
5. **`run_same`** (D). On `NR.start()` (cur None, cb empty) with s = e0, `NF.same` compares
   0 bytes, so q = True. The claim then reads `Some{""} == None`. The caller
   (`norm.bend`'s `fast.run.q`) checks `s < e0` after `Run.same`, but the statement does not.

Not affected: `run_start`, `run_to_spec`, `run_tick`, `run_head_hold`, `run_take`,
`run_reserve`, `of_str` (no counterexample found by reading the code; not proven).

## Round 2 (after the lead's fixes: hin, hx, P.settle, hlt)

The first round's counterexamples are gone. Before writing proofs I re-read all 13 statements
against the code. Two more are false:

6. **`run_same` after `run_same_done`/`run_body_line` (H, run).** A new CHROM run stores
   `NR.of_str(NR.At.chrom(at))` as cb. Neither statement says that CHROM is bytes or
   bounded: only the line's text is tied to the source buffer (`ht`). With
   `at = At{2, "\u0100", "1"}`, a line "x\t1\n" after a #CHROM line (hin and hx hold), cb
   holds a byte that is not the CHROM. `run_same` on a buffer holding cb's text passes
   (q = True), though that text is not `c`'s. The state is forced (`mkRun(p2)`), so no
   RunInv makes both deliverables true. `ex_h` in `proof_b_run_cex.bend` prints True.
   A CHROM longer than 2^30 breaks `of_str` the same way (not run).
   **Fix:** in `run_same_done` and `run_body_line`, assume
   `E.is_bytes(NR.At.chrom(at)) == True` and a length bound (e.g.
   `String.length(NR.At.chrom(at)) <= 2^28`; the caller's CHROM is a field of a line of at
   most 2^28 bytes).
7. **`run_head_write`: no bound on the #CHROM line or the added lines.** Only `hh` bounds
   `h`. With `|Line.text(l)| = 2^31`, `put_str` computes room for `2^31 + 8` bytes.
   `depth((2^31 + 8) * 2)` wraps to a depth-2 block, the pushes wrap inside it, and
   `specRun(p2).out` is not the header. That is a logical counterexample (a 2 GiB line),
   not run. **Fix:** assume a bound on the whole text written, e.g.
   `String.length(P.RunP.h(p) ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l)) <= 2^30`,
   or 2^28 on each of `R.added(o, term)` and `B.Line.text(l)` beside `hh`.

The other 11 statements look true to me after this re-read (no proofs yet).

## Suggested fixes, round 1 (applied by the lead)

- Body deliverables: add hypotheses that p is in the body and not stopped (`i == True`,
  `x == False`; `proof_b_defs.bend` needs a `RunP.x` accessor). Compare through a
  normalization that also forgets buf and last once the result has stopped, e.g.
  `settle(st)`: `blank_st(st)` when not halted, else `RunSt{n, i, h, c, e, None, Nil, k, o,
  ns, True}`. The simulation then needs `finish(run.go(ls, fa, o, settle(st))) ==
  finish(run.go(ls, fa, o, st))`. That holds, because `L.line_step` returns a halted state
  as is and `R.finish` of a halted state reads only out and notes. The proof is like
  `proof_fast_run.bend`'s `inv`, plus a halted case.
- `run_head_write`: add `i == False`. With the body hypothesis above, `RunInv` can then say
  "not in the body → ob empty, ow = 0, buffer empty", which also makes (G) go away.
- `run_same`: add `{U32.is_lt(s, e0) == True{}}`, or put `q && s < e0` in the conclusion's
  `Bool.pick`.

## Where it got hard (research data)

- **Shadowed names give misleading errors.** In `bl.stop.k` a parameter named `st`
  (a proof) shadowed the source tree `st` used in the same signature; the checker reported
  `expected AT.Tree<U32>, observed Sigma<...>` at the later use. Generated code needs
  fresh names for every binder.
- **Code generation paid off.** The body side (add, same_run, new_run, keyed, the three
  body deliverables) was written by small Python generators (long repeated parameter
  lists and state terms); the last helper file checked on its second run.

- **Overflows that are not big numbers.** The checker overflowed (instead of an error) on:
  a wrong rewrite direction (it seems to normalize terms to print the mismatch); an affine
  variable used twice (`(l2, q) = m` with l2 used twice; fixed by `(+l2, q) = m`); a reference
  to a deleted lemma; the inline `%e : G; t` form in some places. Bisecting by truncating
  the lets (`?TODO` after the k-th) finds the line in a few runs.
- **Copying an unpacked equality** (`+lq = lp` where lp came from destructuring a pair of
  proofs) failed with "cannot infer"; use each unpacked fact once and derive copies from
  lets with explicit types.
- `&&` is left-associative: `a && b && c` is `(a && b) && c`.
- A Sigma result cannot be stated as a `law`; use a `def` with a signature.
- A rewrite `%e : G` applies to the whole goal: with a Sigma goal, build each equation
  apart (`AB.subst` on its own type) instead.

- **Closed big Nats.** A conversion (`U32.to_nat(8)` against `8n`) inside a type that also
  holds the closed `Nat.mul(4n, Nat.pow(2n, 29n))` overflowed: the checker normalizes the
  whole type when two terms differ. A name for the bound (`def W31()`) overflowed the same way.
  Fix: do conversions in a lemma where the bound is a variable (`le_c8`), and write the bound
  out in full wherever it must match a library lemma's type.
- **A missing name overflows too.** An edit had deleted `sh4`; the checker reported a stack
  overflow, not an unknown name.
- U32 literals convert natively (`U32.shln(1, 2n)` against `4`), so U32 literal facts plus
  `I.size_n` reach `Nat.pow` bounds cheaply. Nat literals do not (no native arithmetic).

- Finding these took reading only, then a 150-line executable file. Running the machine
  and the spec side by side on 3-4 records (`NR.to_spec` against `R.body_line`) confirmed
  each case in seconds. Do this before writing an invariant.
- The old String machine (`proof_fast_run.bend`) did not have problem 1, because on rare
  paths (a new CHROM, UNSORTED) it called run.bend's functions. The bytes machine has its own
  flush and stop, so its stopped states differ from run.bend's in fields nothing reads
  after a stop.
- Planning notes for the proofs once the statements are fixed:
  - `room`/`reserve` need `depth(need) ≤ 29` and (`need ≤ 4·2^depth` or depth = 29).
    That needs `to_nat(shln(4, d)) = 4·2^d` for d ≤ 29, from lawful-words' `wshl.m`
    with the top bit clear.
  - Bounds on U32 constants (hbig, hk) are best chained on U32, with no-overflow side
    conditions on constants only (natively cheap).
  - `ins.start` is exactly `R.insert`'s split for any list (no sortedness needed). `at_end`
    needs only "every buffered key ≤ tl" and "bn = |front| + |back|".
