# Phase B proof area "lines": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in the proofs of the fourteen deliverables in
`proof_b_lines.bend`. Each is `?TODO`, with its statement fixed.

They are about the machine's input (`norm.bend`: `Src`, `Pd`, `NF.lf`, `pend.add`,
`join.k`, `eof_src`, `line`). The text not handled yet is the sources' text
(`P.srcstext`) followed by the line end's (`P.pdtext`). It splits into the lines
`B.Text.lines` gives, one source line at a time, and a piece or the end of the file
changes it as expected.

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_defs.bend`: shared pictures (`SrcP`, `PdP`, `mkSrc`, `mkPd`, `srctext`,
   `pdtext`, `src_ok`, `pd_ok`, `nolf`, `btext`). Read-only.
3. `proof_b_lines.bend`: your skeleton and deliverables.
4. The code, `norm.bend`:
   - the "Text" section (`chars`, `text`, `text_of`, `ends_cr`, `line`);
   - `pend.add` and its helpers, `Pd.len`, `join.k` and its helpers (`join.go`,
     `join.l`, `join.b`, `join.s`), `Pd.src`, `eof_src`;
   - `NR.put_bytes`, `NR.put_str`, `NR.room` (`norm_run.bend`);
   - `NF.lf` (`norm_fast.bend`).
5. `types.bend`: `B.Text.lines`, `B.Text.line`, `B.Text.last` (they use `String.split`
   at '\n').
   The old machine's input proofs are in `proof_machine_lines.bend` (pieces to lines with
   `String.split`, lemmas `S1`, `L1`, `L2`, `L3`). That file no longer checks, because it
   used the old String machine's `feed`. Copy any pure String lemmas you want from it
   into your own file.
6. lawful-bytes, all proven:
   - `../lawful-bytes/LAWS.bend`: `find_view`, `find_pair`, `first_*`, `append_*`,
     `push_*`, `grow_*`, `to_list_*`, `len_*`, `empty_*`, `capacity_*`;
   - `../lawful-bytes/proof_core.bend` (`C.BT`), its `notes/` and `PROVING.md`.
   - `F.find` and `F.append` (fast.bend) only through `proof_b_fasteq.bend` (holes on
     purpose).
   - `piece_src` needs `E.enc` as a mirror: the enc area proves it in
     `proof_b_enc.bend` (`enc_bt`, `enc_ok`; in progress). Call those (import the file)
     even if they are still `?TODO`.
7. `notes/briefs/PROVING.md`, `bend guide`.

## Hints

- Size bounds use `Nat.pow(2n, 28n)` and `Nat.pow(2n, 31n)` exactly as written. Keep
  them abstract (prove for any bound, instantiate syntactically); never compare a
  symbolic Nat with a big literal (see the notes).
- `pend.add` and `join.k` switch to text past 2^28 bytes. The deliverables only say what
  text results, so both branches must give it.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_lines.bend` and new `proof_b_lines_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_lines.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: no TODO left apart from those of `proof_b_fasteq.bend` and `proof_b_enc.bend`
  (other areas).
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_lines.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about seven hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
