# Phase B area "adv": notes

Brief: `notes/briefs/BYTES_PROOFS_ADV.md`. Deliverable: `adv_ok` in `proof_b_sim.bend`; its
proof is `proof_b_adv.bend: adv` (adv_ok's exact statement, against the current AdvG with the
guard and stopped clauses).

## Status (2026-10-28, round 5): every byte-mode path proven; one stated lemma

All of advance's byte-mode paths are proven, given the other areas' deliverables
(run_fast_done, run_same_done, run_body_line, run_head_write, against_hit, vd_ok, reqof_rq,
... may still be ?TODO in their files) and one lemma I state for the lead to assign:

- `judge_bytes` (`proof_b_adv_slow.bend`): for `CD.fa_bytes(fa)` and `E.is_bytes(body)`,
  `E.is_bytes(P.res_text(L.judge(fa, body)))` (run_body_line's `hb`, the slow path's VRes).

| path | file |
|---|---|
| byte mode: Ended, Yield, Idle, big buffer / text source to the String mode | `proof_b_adv.bend`, `_tostr` |
| before #CHROM: line too long, header line held | `_dec` |
| the #CHROM line: written, or the String mode when it does not fit | `_wr` |
| no complete line: to pend | `_part` |
| in the body, fast path (all window cases, hit, Want) | `_fast`, `_hit` |
| in the body, slow path (VRes written or to the String mode, VSame, VWant) | `_slow` |
| String mode: Ended, Yield, Idle | `proof_b_adv.bend` |
| String mode: a byte source / a text line | pb-cache, `proof_b_adv_msx.bend` (adv.ms.sl wired; adv.ms.sb hole) |

Scratch check (other areas in flux stubbed): `proof_b_adv.bend` reports only TODOs. The real
tree currently stops inside `proof_b_adv_msx.bend` (`sb_line`, pb-cache's work in progress).

Decided by the lead in round 5: the #CHROM line's text bound is now a test in norm.bend's
head.len (hl comes from it; `hl_gap` is gone); `run_same0` is proven here (`Run.same` at
length 0: `n(e0 - s) = 0` from `s <= e0` and not `s < e0`, so `NF.same` compares no bytes
and hands both buffers back, `C.at_pair_t`); vd_ok's VWant gives
`fst_c(reqs) == Some{CHROM field}`, which with the field being bytes and at most 2^28
(`f0_bytes`, `f0_len`: the first piece of `String.split` is bytes and no longer than the
line) gives `mb_reqs`.

Structure: `proof_b_adv_hit.bend` no longer imports `_dec` (its tick and spec lemmas come
from `_wr`), so `_slow` can use the hit file's run lemmas (`k_fit`, `k_text`, `k_le_z`,
`runn_eq`) and `_dec` imports `_slow`.

Fixed since round 3: `run_hdr` / `run_hdr_notes` are gone (run_hdr_notes was false
without "not stopped"); `to_ms_went` now takes `hx` and uses the run area's
`run_head_empty` (`proof_b_adv_tostr.bend`: `hdr_out`, `hdr_notes`).

Files (mine): `proof_b_adv.bend` (dispatch), `_wf` (WF tools), `_ms`, `_tostr`, `_str`,
`_line` (`went_line`), `_dec` (decoded path), `_nat`, `_ib`, `_proj` (projections of the
cut's facts), `_judge` (`fast_res`), `_hit` (the fast path's hit), `_fast` (the fast
path's cases), `_wr` (the #CHROM line), `_part` (to pend), `_cex` (rounds 1-2).

Where it got hard (round 4):
- Instantiating a lemma at 2^28 made the checker expand `U32.to_nat(268435457)` (stack
  overflow). Fix: state the lemma with the bound as a variable `y` below a word `z`
  (`k_le_z`, `chrom_len`) and instantiate only at the call; the call then only compares
  U32 literals natively.
- Defs named `F.x` in a file imported `as F` are `F.F.x` ("expected a defined name").
- `+x = "literal"` and `+q = S.StP{...}` need a type annotation (`{... : String}`).
- A file can't import the file whose hole it fills (dec ← wr/part): the small tick/spec
  lemmas are copied.

## Round 2 (fixed by the lead): two more gaps

Round 1 (cases A-D below) was fixed by the lead (WF's eof clause, st_bytes and the options'
arguments, asked = None on the two Went paths). With the fixed statement, two more gaps
show, three counterexamples (E, F, G), all run in `proof_b_adv_cex.bend`; WF (round 2)
holds in each:

4. **The String mode's own out is not empty** (case E). `report` ignores `s.out` (`smd`
   sets out to qs's text), but `ms.out` moves `s.out` into qs after the next line. E:
   in the body, `s.out = "x"`, one malformed line `"a"`. Spec report: out `""`; the next
   state's report: out `"x"`.
   - Fix: `md_ok(MSP)` adds `String.is_empty(P.RunSt.out(s))`. Every way into the
     String mode (`ms.out`) sets out to `""`, so advance keeps it.
5. **Text in front before the #CHROM line** (cases F, G). run.bend's #CHROM line
   *replaces* out (`R.head_line(True)`), so text already in front is dropped by the spec
   but kept by the machine:
   - F: String mode before the #CHROM line, `O = "y"` (adv_ok allows any O). Spec
     report: out = the header; next state's: `"y"` + the header. The byte mode does the
     same (run_head_write's equation is `R.head_line(True, specRun(p))`).
   - G: the same with `O = ""` and `qs = ["y"]` (WF allows text in qs before the
     #CHROM line).
   - Fix: give adv_ok the hypothesis `step_pre` already has,
     `{R.RunSt.inbody(S.smd(S.StP.md(p))) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)) == True{}}`
     (the pump keeps it: nothing is written before the #CHROM line), and add to
     `md_ok(MSP)` `R.RunSt.inbody(s) || String.is_empty(Norm.cat(List.reverse(&2, String, qs)))`.
     N is harmless here (head_line keeps notes, and finish's NO_HEADER drops them on both
     sides), but O and qs are not.

**Wiring.** `adv_ok`'s body cannot call a proof in `proof_b_adv*.bend`: those files need
`StP`, `WF`, `report` and `AdvG` from `proof_b_sim.bend`, and `bend` refuses import cycles
("an import cycle through ..."). Options for the lead:
- turn `def adv_ok ... ?TODO` into `law adv_ok`, which a file of mine fills as
  `def S.adv_ok(...)`, as LAWS/PROOF do; or
- move the pictures and definitions of `proof_b_sim.bend` into a defs file that both
  import.
Until then my lemma `proof_b_adv.bend: adv` will carry `adv_ok`'s exact statement.

Started (kept): `proof_b_adv_wf.bend`, tools for taking WF apart and putting it together
(`C8`, `c8_m`, `c8_mk`, `wf_c8`, and/or lemmas); it checks.

Missing lemma noticed while planning (not a falsity; I will state it as a `?TODO` in my
files per the brief unless the run area adds it): `run_fast_done`, `run_same_done` and
`run_body_line` take `hbig` about the run *after* the line's tick, but `run_tick` does not
say the tick keeps `obl` (nor `ow`); `i`, `x`, `c` can be read back from its `specRun`
equation, `obl` cannot. Suggested: `run_tick` also gives `P.RunP.obl(p2) == P.RunP.obl(p)`.

Re-run after the lead's later norm.bend changes (literal bounds, `slow.reqs`): E, F, G
still hold; `proof_b_adv_wf.bend` still checks. For the plan: the slow path's Want now
asks `parts(c, 0, e)` once the window has grown (back > 100), else `Req.of` (reqs_ok from
`parts_ok` either way); `against_hit` now also needs `U32.is_lt(pos, 1000000000)`
(`pass_pos_small`) and `U32.is_lt(0, rl)`.

**Rule (lead, after an out-of-memory check):** never run `bend` directly. Every check,
`--verdict` and counterexample run goes through
`timeout 1800 test/bcheck.sh <file.bend> [--check-only|--verdict]` (`prlimit --as`
4 GB address space, at most two at once). `bcheck: bend exited with N` (N > 1) means out of
memory or time. Never make the checker compute with big closed Nats (2^28, 2^31, 2^32, Nat.pow of
them, two big literals compared): keep bounds abstract or go through U32 lemmas.
`proof_b_adv_cex.bend` runs `Norm.advance`, which now compares `ql` with the literal
`lim()`; rerun it only through bcheck.

## Round 1 (fixed by the lead)

Nothing is proven; `proof_b_sim.bend` is untouched. `adv_ok` is false as stated, with the
`AdvG` of the lead's two updates (asked/eof clauses, then the fuel measure). Three independent
gaps in `WF`/`AdvG`, four counterexamples. All are run on concrete values:
`bend proof_b_adv_cex.bend` prints

    Res{True, Wt{True, "abc", True, True}, True, Wt{False, "", False, True},
        Wt{False, "", True, False}, True, Wt{False, "", False, True}}

That file copies `StP`/`mkSt`/`WF` for String-mode states with no window, because importing
`proof_b_sim.bend` would import other areas' open TODOs and the program would not run.
`Wt{eof, pend's text, qs are bytes, asked is None}` describes the `Went` state that `advance` returns.

1. **eof with a last source that has no LF** (case A). String mode, `eof = True`, one source
   `"abc"` (no LF), empty pend. `WF(p)` is True. `advance` reaches `ms.part.len`: `Went`
   with pend `"abc"` and `eof = True`. Any p2 with `mkSt(fa, p2)` equal to it has
   `pdtext(pd2) = "abc"`, so the clause `not eof || pdtext empty` makes `WF(p2)` False.
   The byte mode does the same through `part.len`. The report is unchanged; only `WF` fails.
   The machine never reaches this (`feed_eof` gives the last line an LF), but `WF` does not
   say so.
   - Fix: add to `WF` `Bool.not(eof) || ends_lf(P.srcstext(src))`. `advance` keeps it: a
     source without an LF under it must have empty text, so pend stays empty. `feed_eof`
     establishes it when the pump has emptied the sources (they are Nil at Idle).
2. **String mode texts that are not bytes** (cases B and D). `md_ok(MSP{s, qs, ql, code})`
   constrains only `qs`. The `#CHROM` line writes `h ++ R.added(o, term) ++ line` into `qs`
   (`ms.done`/`ms.out`), so:
   - B: a held header `h` holding `Chr{256}`;
   - D: an option argument (`o.args`, written by `R.added` through `args_text`/`clean`)
     holding `Chr{256}`.
   In both, `WF(p)` is True and the new state's qs is not bytes, so `md_ok`, and with it
   `WF(p2)`, is False. Body lines would likewise write buffered item texts.
   - Fix: `md_ok(MSP)` should also say the run state's texts are bytes (`h`, the buffered
     items' texts, out), and `WF` should say the options' arguments are bytes (e.g.
     `E.all_bytes(args)`). `run_head_write` already needs `E.is_bytes(R.added(o, term))` (hb3)
     in the byte mode, so the byte mode needs the options fact too. `RunInv` (the run area) must then
     give bytes-ness through `run_to_spec`, so that `to_ms` keeps `md_ok`.
3. **Went keeps asked** (case C). The new clause `StP.asked(p2) == None` for `Went` fails on
   two byte-mode paths that keep `asked` as it was: `mb.src` with a text-line source (`SL`,
   switching to the String mode), and `mb.rs` when the output buffer is big (`to_ms`). C
   is the start run (`NR.start()`, so `RunInv` holds by `run_start`), source `SL{"x"}`, asked
   `Some{[Req{"c", 0, 1}]}`. `WF` holds, and `advance` gives `Went` with asked Some.
   - Fix: either `AdvG`'s Went says "asked is None or unchanged" (the pump then needs only
     that a Went never comes right after a Want that is still pending), or `norm.bend` sets
     asked to None on those two paths, as `to_str` does.

Checked and fine (by reading): the new measure decreases on every Went path (a consumed
line: `len - (lf+1) + 2 < len - s + 2`; a dropped source: at least 2; leaving the byte mode:
the +1). Want's `asked_of(reqs)` matches `Some{reqs}`, because the reads are never empty
(`parts_ok`'s length >= 1). Idle, Ended and Yield keep asked (and Idle keeps eof).

## Plan once the statement is fixed

Same shape as `proof_machine_sim.bend`'s TL, path by path:
- the run's halt/full/big test (`Run.rs` computes on `P.mkRun`);
- then per line: `src_line` to split the text, `lines_cons`, `L.run.go`'s step, `step_pre`,
  the run lemma's settle equation (`run_fast_done` and so on), `settle_inv` and `settle_pre`;
- the fast path's verdict through `alleles_*`, `pass_*`, `against_hit`, `fast_judge`,
  `window`.

## Where it got hard (research data)

- Round 2 came from planning the proof of each path: writing down how `report(p2)` must
  unfold to `report(p)` exposed both gaps (smd overriding out, head_line replacing out).
  Planning the report equation path by path before proving catches these early.
- Other areas' files change under the proof all the time (statements migrating to U32
  bounds, files mid-edit that do not load). A scratch copy of the tree, with the files in
  flux replaced by statements-only stubs (every proof body ?TODO), kept my checks going;
  every check still went through bcheck.sh.
- Pair patterns take `+` only on the first component (`case (+p2, q)`); `+` on an inner
  one, or a bare copy `+x = y` of an inner one, fails with "cannot infer" (in Base's
  Pair). Copy through `Equal.trans(T, a, b, b, y, {==})`. The checker's report was cut off
  by bcheck's last-40-lines, so the failing step was found by bisecting with ?TODO.
- Rewrite direction is still the most common error (about 40 again).
- `LAWS.bend`'s open laws also block running a file, so the spec side of a one-line
  example is computed by hand (`R.body_line` of `L.res`, `R.head_line` after `R.tick`).

- Again, reading the paths against `WF` before writing any proof found the problems. Each
  Went/Want branch was checked for which `WF` clause it could break. A 120-line executable
  file confirmed all four in one run, in about a minute.
- A counterexample cannot import a file whose import graph holds open TODOs (`bend` refuses
  to run it). Copy the definitions it needs (here `WF` and `mkSt`, specialized to the String
  mode, which avoids the opaque `RunInv`).

## For pb-alleles, from pb-cache (the String-mode holes adv.ms.sb / adv.ms.sl)

- **Both String-mode holes are proven (2026-10-28).** `adv.ms.sb`'s body is
  `MX.ms_sb(...)` and `adv.ms.sl`'s is `MX.ms_sl(...)` (`proof_b_adv.bend` imports
  `./proof_b_adv_msx.bend as MX`; that import line and the two bodies are the only changes to
  your files). Both give the AdvG `eof` clause. `proof_b_adv_msx.bend` and `proof_b_adv.bend`
  check with TODOs only; break tests (in `step_bytes`, `wantL`, `sb_line`) fail where they
  should.
- **The one open statement under them is `judge_bytes`,** the lemma you stated for the lead.
  It has the same statement in `proof_b_adv_msx.bend` (`MSX.judge_bytes(fa, body, hb, hbd)`),
  since my `step_bytes` needs it for Normalized records and I cannot import `_slow` (it imports
  msx). To keep a single hole, your `judge_bytes` body in `proof_b_adv_slow.bend` can be
  `MSX.judge_bytes(fa, body, hb, hbd)`; whoever proves it then fills msx's.
- How it goes (in `proof_b_adv_msx.bend`):
  - `msline` is the core: a text line `q` (bytes, no LF) in front of the sources `src`, with
    `src2` the sources after it. Header line: `head_line`, as the spec does. Body line:
    `vd_ok`'s verdict. VRes/VSame give the spec's `body_line` (`bl_eq`, via `pfs_field`/`pfs_pos`);
    VWant gives Want with `SL{q}` back in front (`wantL`). The consumed cases go through
    `wentL` with `ms.out` (`MS.mk_msO`, `rep_msO`, `meas_msO`, `mbw_msO`; `mdok_msO` is the
    String-mode `md_ok` after a line).
  - `ms_sl`: `src = SLP{q} <> rest`, `src2 = rest`. `ms_sb`: `NF.lf` (via `LN.lf_ok`); no LF
    left → bytes to pend (`MP.*`, a String-mode copy of your `DP.*`, using `meas_drop2`);
    else the decoded line (`LN.src_line`, `sb_text` = your `text_eq`) goes to `msline` with
    `src2 = SBP{len, t, d, lf + 1} <> rest`.
  - `step_bytes`: the run's texts stay bytes after a line (`stop_b`, `ins_b`, `tk_b`, `dr_b`,
    `fl_b`, `em_b`, `sr_b`, `nr_b`, `ky_b`, `pl_b`, `bl_b`, `hd_b.*` over run.bend; your
    `WR.added_bytes`/`WR.tb` for the header lines).
- Imports of `proof_b_adv_msx.bend` among your files: `_ms`, `_wf`, `_str`, `_line`, `_nat`,
  `_part`, `_wr` (and `proof_b_lines`, `proof_b_run_inv`). None of them may import msx.
- **The verdict lemma your `dec.slow` needs is there too:** `vd_ok(fa, wp, back, body, hb, hv)`.
  - It gives `&v: VdP -> ({Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(body), body) == mkVd(fa, wp, v)} & vdOK(fa, body, v))`.
  - `VdP` has three cases:
    - `VRP{r}`, with `r == L.judge(fa, body)`;
    - `VSP{}`, with `B.Res{B.Normalized{}, B.Rec.pos(J.pfs(body)), body, False{}} == L.judge(fa, body)`;
    - `VWP{reqs, back2}`, with `E.reqs_ok(reqs)`, `reqs == S.rq(reqs)` and `1 <= length(reqs)`
      (that is `RQOK(reqs)`), **and** (added on your request, 2026-10-28)
      `{fst_c(reqs) == Some{B.Rec.field(J.pfs(body), 0n)} : Maybe<&2, String>}`.
      `fst_c` (in `proof_b_adv_msx.bend`) is the first read's contig: `None` for no reads,
      `Some{c}` for `Pr.Req{c, a, b} <> t`. So `vdOK(fa, body, VWP{reqs, b})` is now the pair
      `RQOK(reqs) & {fst_c(reqs) == Some{field 0}}`; destructure it with `(hq, hc) = hok`.
      To get `mb_reqs.k(reqs)`, match `reqs`: the `Con{Pr.Req{c, a, b}, t}` case turns `hc`
      into `Some{c} == Some{field 0}` (take `c == field 0` with `Equal.cong` and
      `Maybe.default`, as `jres_inj` does for `B.Res`).
  - The window is unchanged, as `serve` hands it back.
  - **It checks (2026-10-28).** A break test fails as expected. The window is unchanged, so the
    state after a VWP keeps `wp`.
