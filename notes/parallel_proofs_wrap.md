# Phase E, area E1 (wrap): proof notes

Deliverables: `wstep_chunk`, `wstep_eof`, `wstep_ref`, `wstart` in `proof_e_wrap.bend`
(definitions `proof_e_wrap_defs.bend`). Helpers: `proof_e_wrap_*.bend`.

## Status (2026-10-28, night): done

`wstep_chunk`, `wstep_eof`, `wstep_ref` and `wstart` are proven; their statements are unchanged.
No TODO of mine is left.

- `timeout 1800 test/bcheck.sh proof_e_wrap.bend --check-only`: only the 15 TODOs every file
  importing MACHINE.bend reports (its laws, proven only in PROOF.bend). Areas B, C, D and F are
  proven in the real tree, so this is the whole chain.
- `--verdict` refuses any file importing MACHINE, so the kernel check uses a harness,
  `proof_e_wrap_vh.bend` (PROOF.bend's forwards plus `import ./proof_e_wrap.bend`, as area F's
  `proof_e_qif_vh.bend`): `timeout 1800 test/bcheck.sh proof_e_wrap_vh.bend --verdict` gives ALL
  PROOFS CHECK. Before the last fix it listed every one of my defs that depends on `out_xs`, so the
  harness does check these files.

Files (helpers import only files below them; no cycles):
- `proof_e_wrap.bend`: the deliverables, by the batch's phase (absurd phases by the next the
  driver was given); `wstart` from phase B's `start_ok` and `start_k` (W.start wraps Q.start).
- `proof_e_wrap_base.bend`: `g2_none` (a Q step with phase B's StepG2 is a wrapper step with no
  batch), W.quiet/opts/q.n on pictures (`quiet_mk`, `qb_stop`, `opts_mk`, `qn_mk`), `more_keep`,
  `rev_encs`; code-level Norm.out facts (`out_x`: options, stop flag, next kept), `out_stop`,
  `out_o`, `stop_pic`, `o_pic`, `g2_ef`, `live_k`, `nbm`, `and2`.
- `proof_e_wrap_col.bend`: no batch (`none_chunk`), collecting (`col_add_k`, `col_eof`), a
  complete batch (`plan_ok`: its Ask, or with no reads its tasks at once), the Ask's answers
  (`ask_ref`), `pcs_dup` (PcsOK is needed twice: by PT.batch and by the next state).
- `proof_e_wrap_qx.bend`: XS(s, o) = a Q step keeps the options and, when it answers More, has
  not stopped. `out_xs`, `finish_x`, `idle_x` (code level), `pump_x` (induction along AdvG with
  area A's options clause), `go_x`, `ref_x` (F's `set_win_ok`), `chunk_x` (F's `core` after
  phase B's `run_reserve`).
- `proof_e_wrap_seq.bend`: `seq_ok` (Q's StepG2 + XS give the wrapper's step while combining),
  `seq_ref`, `comb_end`, `comb_eof`, `comb_dirty`.
- `proof_e_wrap_comb.bend`: `comb_next_ok`, the combine's dispatch (end, dirty, clean).
- `proof_e_wrap_ms.bend`: advance keeps the String mode (code walk of ms.*), `ms_pic`.
- `proof_e_wrap_spec.bend`: spec facts: `go_n` (each line adds one to n while the run has not
  stopped; a walk of run.bend's head_line/body_line), `go_app`, `go_settle`, `fin_settle`,
  `pre_pre`, `pre_shift`, `segok_pre`, `segok_settle`, `shift_settle`.
- `proof_e_wrap_edge.bend`: the chain of Moved facts over the edge's advances (`Ch`, `ch_refl`,
  `ch_step`), `one_line`, `edge_lines` (also for E2).
- `proof_e_wrap_mg.bend`: `mg_rep_k`, the report after a merge (area B's `seg`, area C's
  `merge_spec`/`merge_segok`, settle bookkeeping); `ob_out`, `i_merge`, `x_merge`, `segok_rs0`.
- `proof_e_wrap_mok.bend`: `mok_state` (the state after the splice is good), `tc_*` (TcOK's
  run test taken apart), `halt_of_segok`.
- `proof_e_wrap_fb.bend`: a clean piece left to Q after the edge (`go_seq`, `want_seq`,
  `idle_seq`, `ended_seq`, `yield_seq`).
- `proof_e_wrap_mc.bend`: `merge_case` (merge.ok decides MOk or MNo).
- `proof_e_wrap_clean.bend`: `comb_clean`: feed_line, then the edge's fuel levels `E3` .. `E0`
  (each: `E_a` by the advance, `E_k` by edge.where's tests), `where_eq`, `splice_ok`.
- Generated text: the E levels (`E0`..`E3`, identical up to the fuel) and the XS-macro files
  (`qx`, `seq`) were written by small scripts kept in `data/tmp/wrap_gen/` (ignored). The `.bend`
  files are the source of truth; an edit to one E level must go to all four.

## Statement gaps sent to the coordinator

1. Q keeps its options (`StP.o`) through a step: phase B's AdvG and StepG2 do not say it, and
   PhaseOK's BCombP holds `BatchOK(fa, StP.o(p), ...)`. Decision: area A adds
   `{S.StP.o(p2) == S.StP.o(p)}` to AdvG; E1 proves it for out, pump, finish and step on top.
2. PhaseOK's BColP, BAskP and BCombP (seq False) lack "Q's run has not stopped", which `Norm.out`
   needs (`DO.out_ok`'s `live`). Without it a halted header run with output pending fits InvW
   and Q.out breaks the guard.
3. PcOK's True case lacks "k is the piece's first LF", which the edge needs to name the lines
   still to come after the boundary line.
4. PcsOK held a function (`@X`), which cannot be used twice; batch and the next state both need
   it. Now instantiated per piece (PcsOK(ps, dcs)).
All four fixed by the coordinator. Area F's statements needed nothing more; its `core` and
`rep_of` were reused for the fed state.

## What was hard

- Linearity: a pair of equalities is a Type, but can be destructured and rebuilt (`pcs_dup`);
  a function cannot. Lets of a rewritten hypothesis (`+h = %e : G; h`) do not infer: use
  Equal.trans/cong. Computed pairs cannot be destructured: pass them to a lemma.
- The kernel (`--verdict`) counts a linear variable named in a proof term (an `Equal.cong`
  argument) as a second use, where bend2 does not: `out_xs` first projected `out_x`'s pair with
  `cong`, mentioning the linear `Norm.St` three times; walking `out` directly fixed it.
- The edge: a match cannot recurse into a helper that calls back (no mutual recursion), so the
  three-advance loop became four generated levels; `edge.where` is stated once on pictures
  (`where_eq`, eight shapes of the source list and run) so each level generalizes its two tests.
- Name clashes in long generated signatures (an advance `a` and the first-LF prefix `a`) give
  confusing errors far from the cause.
- Code-level facts about Norm.out need each computed pair (left(src), md.take, take.fin, the
  String mode's cut) taken apart by its own lemma, matching the linear md before the pair.

## For E2

Checked (`--check-only`), in `proof_e_wrap_edge.bend`:
- `edge_lines(fa, c, k, X, p, p3, ls1, a, hm, hc, hn, hmv, hone)`:
  `{B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X)))}`
  from `hm: DR.more_ok(fa, p)`, `hc: c == a ++ "\n" ++ PT.after(c, k)` and `hn: P.nolf(a)` (PcOK's
  last component), `hmv: lines(S.intext(p, c <> X)) == ls1 ++ lines(S.intext(p3, X))`,
  `hone: List.length(ls1) == 1n`.
- `one_line(fa, o, ls1, rp1, rp2, hs, hn, hx)`: `{List.length(ls1) == 1n}` from the Moved run fact
  `hs: settle(specRun(rp2)) == settle(run.go(ls1, fa, o, specRun(rp1)))`, the edge's count
  `hn: RunP.n(rp2) == 1n + RunP.n(rp1)` and `hx: RunP.x(rp2) == False` (merge.ok has it).
- `Ch(fa, cs, p1, pc)`, `ch_refl`, `ch_step`: the advances' Moved facts chained (byte mode),
  with the String mode kept (`proof_e_wrap_ms.bend`: `adv_keep_ms`, `ms_pic`).
- Spec helpers in `proof_e_wrap_spec.bend`: `go_n` (n of run.go), `go_app`, `go_settle`,
  `fin_settle`, `pre_pre`, `pre_shift`, `segok_pre`, `segok_settle`, `shift_settle`.
