# Phase C, area "bud": brief

Prove `fix_bud` in `proof_c_bud.bend` (statement fixed): the budget (phase B's `BD.AdvC`) holds
for the rewrite path, `Norm.fix(...)`, which `fast.pre`'s `NF.Slow` branch now runs
(`norm.bend`, section "A record rewritten on its bytes", and `norm_fix.bend`).

## How (suggested)

- Phase B's `proof_b_budget_fast.bend` was generated from the adv proofs (its header says so):
  the same walk with `BD.AdvC` in place of `S.AdvG`. Do the same from my adv chain for the fix
  path: `proof_c_adv.bend` (`fix_ok`, `K.fp`, `K.cut`, `K.lt` .. `K.wo`, `K.kw`), whose decline
  cases are `DE.dec` there and will be `BDe.c.dec` here.
- The take case (`norm.bend` `fix.hit` .. `fix.tick`, the WHit branch) needs no judge or text
  facts for the budget: phase B's budget `fhit.w` only uses `BM.went_done` and `BM.bi0` with the
  line's `SPLIT`/`nolf` (`LN.src_line`). Follow the code's case splits:
  - window: `CA.ah.mk` turns `mkWin(fa, WPKnown{c, a, b})` into its `WKnown` (with a mirror of
    `NR.of_str(c)` from `C.bmirror`);
  - `NX.norm`: tan's `proof_c_tan.bend` `norm_pair` (answer `NZB`), then case on `Q.NZ`;
  - the `same` test, then `NX.write`: my `proof_c_text.bend` `write_t` (its first conjunct gives the
    `Wb` shape for any `ok`; needs `REF <> TL(als)`: `proof_c_pre.bend` `fix_als`'s first
    conjunct), then case on `ok`;
  - `fix.cmp`: `BY.len` on a mirror reduces; `BY.same` on mirrors: lawful-bytes
    `proof_same.bend` `same_pair_t`; case on the flags;
  - `fix.len`: `proof_b_adv_slow.bend` `oblen_eq`; the fit test: false is `to_str` (find the
    budget lemma phase B uses for the slow path's `body.fits` false case), true is the tick
    (`PR.run_tick`), `NR.fix_done`, `fix.out`, `done.b`: the result is a `Went` with some run;
    mirror that run as `P.mkRun(rp2)` (match the `NR.Run`, `C.bmirror` its two buffers, or a
    pair-eta step on `NR.fix_done`'s result), then `BM.went_done`/`BM.bi0`.
- Facts of a passed line: `proof_c_advf.bend` (`AF.*`), `proof_c_pre.bend`.
- Do not edit my files (`proof_c_adv*.bend`, `proof_c_hit*.bend`, `proof_c_text*.bend`,
  `proof_c_run.bend`, `proof_c_judge.bend`, `proof_c_cache.bend`) or phase B's. Helper files:
  `proof_c_bud_*.bend` (`ls` first).

Rules as in `notes/briefs/REWRITE_PRE.md` (checks through `test/bcheck.sh`, at most two at once;
no big closed Nats; no benchmarks, builds or commits). Notes: `notes/rewrite_bud.md`. Report when
`proof_c_bud.bend` checks with no `?TODO` (also with `--verdict`), or if a statement is false or
unusable.
