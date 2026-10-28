# Phase C, area "pre": status and notes

Brief: `notes/briefs/REWRITE_PRE.md`. Deliverables: `proof_c_pre.bend`.

## Status

| deliverable | status |
|---|---|
| `line_pair` | proven |
| `fix_lf`, `fix_fields`, `fix_pos`, `fix_cr`, `fix_tabs` | proven (phase B's cut lemmas) |
| `fix_als` | proven |
| `read_bf` | proven |
| `fix_info` (INFO as `F7`, the full split's field 7) | proven |

Check: `timeout 1800 test/bcheck.sh proof_c_pre.bend` (about 14 s) and `--verdict` (about 21 s), both
"ALL PROOFS CHECK", no TODO in the import graph. A copy with one proof broken fails under `--verdict`,
so the pass is not cached. About 3,600 lines over 12 files. All statements were true as given; nothing
to report to the lead.

## Files

- `proof_c_pre_pair.bend`: `NX.line` on the mirror `C.BT(len, t)` hands it back; its answer is
  `FX(len, t, s)` on Data. One mirror per loop (`LG` lets, `FG` feq, `DG` dis.go, `XG`/`XS` the ALT
  loop, `LIT`/`KEY`/`SG` nostale); the cut, POS and END test are phase B's (`M.MC`, `M.NUM`, `M.NE`).
- `proof_c_pre_inv.bend`: `FX(..) == Fix{pos, Cut8{e..}, als, up}` gives `M.MC == Cut8{e..}` (so
  phase B's `V.i0` gives every search's flags) and the tests passed (`TT`); `dst`/`dtt` hand them out.
- `proof_c_pre_cut.bend`: glue for the deliverables that reuse phase B's `CU.pass_*.k`.
- `proof_c_pre_let.bend`: the ten letters (`isl_cases`), their bases, `read_bf`, `String.eq` on
  byte text (`sc`, `seq`, `sapp`), REF written back (`up_ref`).
- `proof_c_pre_lp.bend`: `lets`, `feq` and `dis.go` loops as list facts (`lets_v`, `fg_v`, `feq_v`,
  `dg_m`).
- `proof_c_pre_alt.bend`: the ALT loop (`aloop`): the alleles it adds (`XN`) are the comma pieces of
  the ALT field, inside it, letters, distinct, and its up flag.
- `proof_c_pre_als.bend`: `fix_als` assembled (`als_core`).
- `proof_c_pre_str.bend`: String lemmas copied from `proof_fast.bend` (it imports LAWS.bend, whose
  open laws count as TODOs).
- `proof_c_pre_key.bend`: the stale keys. `kfalse`: a key the bytes test refused is none of the
  four (by its length, then `lit_v`). `ENT`: one entry of INFO (up to the first ';'), its key up to
  the first '=' (`D.first` facts, phase B's `LS.spl`/`ts_lt`/`ts_eq`); `c_end`, `c_semi`, `c_eq_t`,
  `c_eq_f` for the branches of `NX.sk.step`; `sloop` by induction on the scan's fuel; `info_key`.
- `proof_c_pre_inf.bend`: phase B's `fields`/`fd_cr`/`fd_q`/`fd_core` (proof_b_cut_fx.bend) copied
  by a script with a new conclusion (`IG`): field 7 of `B.Rec.fields(body)` is INFO's bytes, and
  `J.scan` finds no END in it. `cutR`: INFO cut at its tab (`S.cut_fld`) or, at the line's end, has
  none (`notab`).
- `proof_c_pre_ifo.bend`: `fix_info` assembled (`info_k` moves `IG` to the line's `e6, e7, lf` with
  the cut equation, as phase B's `pass_fields.k`; `end_has` via `proof_window_info.bend`'s
  `scan_eq`).

## Where it got hard (research data)

- The lead edited `norm_fix.bend` while I worked (a duplicate `alts.go` for a while): nothing that
  imports it checked until it was fixed. No statement changed under me except the announced ones.
- A `+` lambda parameter of a Type-valued bundle (`+htt =>` for a tuple of equalities) is an error,
  and with phase B's big E-form context the error printer ran out of memory instead of printing it.
  Bisected by stubbing deliverables.
- Type aliases (`def LE(..) -> Type`) cannot type a `+` parameter or `+` let: "+x can be used many
  times, so its type must be Data". Write the equality out.
- Rewrite direction again (about 15 slips), each fixed from the expected/observed message.
- Mutual recursion between the loop induction and its case split: the recursive call is passed
  as a lambda (`+x1 => +x2 => +x3 => aloop(j, ..)`), as in phase B.
- The lead's change of `fix_info` to `F7` (the full split) meant redoing phase B's field chain:
  `J.pfs` keeps INFO only as `""`, so its result could not be reused; the chain was copied and its
  conclusion replaced (a script did the renaming and the motives, ~200 lines generated).
- `match` on a scrutinee after `+` lets is refused ("matched after a local statement"): the lets
  went into the branches. `case 1n+q` with q used twice needs `case 1n+(+q)`.
- The ALT loop keeps its alleles newest first and checks each new one against all earlier ones;
  distinctness of the final (reversed) list came for free by stating the induction over the
  alleles it adds (`XN`, in order) against the ones before them (`NOTIN`), as phase B's `sp_dist`.
