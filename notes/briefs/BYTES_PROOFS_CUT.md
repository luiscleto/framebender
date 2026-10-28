# Phase B proof area "cut": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in the proofs of the six deliverables in
`proof_b_cut.bend`. Each is `?TODO`, with its statement fixed.

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_cut.bend`: your skeleton and deliverables.
3. The code, `norm_fast.bend`:
   - `NF.line(b, s) = NF.pre(s, NF.cut(b, s))`.
   - `NF.cut` is the chain `k0 .. k8`. Each step uses `NF.tab` (`F.find2` for TAB or LF
     from s, then `BY.at` of the byte found) or `NF.lf` (`F.find` for LF).
   - `NF.pre` reads POS (`NF.num`), tests the alleles (`NF.alleles`: you only need it to
     return True; its meaning is the alleles area's), INFO (`NF.noend`), and the final CR.
   - Also `norm.bend`'s `chars` and `line` (`Norm.chars`, `Norm.line`).
4. The String side:
   - `norm_line.bend`: `J.pfs`, `J.c7`, `J.cut`, `J.noend`, `J.info.if`.
   - `proof_fast.bend` already proves facts about them; import it and reuse them:
     `c7_split` (J.c7 against String.split), `noend_scan`, `ikeyT_cut`, `info_end`,
     `pfs_field`, `pfs_pos`.
   - `types.bend`: `B.Pos.read`, `B.Text.line`, `B.Line.text`.
5. lawful-bytes, all proven:
   - `../lawful-bytes/LAWS.bend`: `find_view`, `find_pair`, `find2_view`, `find2_pair`,
     `at_view`, `at_pair`, `first_hit`, `first_miss`, `first_range`, `first2_*`.
   - `../lawful-bytes/proof_core.bend` (`C.BT`, `at_pair_t`, bounds lemmas) and
     `proof_find.bend`.
   - Its `notes/` and `PROVING.md`.
   - `../lawful-fields/defs.bend` (`FD.dec`) may help with POS.
6. `notes/briefs/PROVING.md`, `notes/proof_machine.md` ("Where it got hard"), `bend guide`.

## Route (suggested)

- Reach `fast.bend` only through `proof_b_fasteq.bend`: rewrite `F.find`/`F.find2` to
  `BY.find`/`BY.find2` with `FE.find_eq`/`FE.find2_eq`. Those are holes on purpose: leave
  them.
- Step through the chain on the mirror. The `*_pair` laws turn each call into a literal
  pair, so the destructuring reduces.
- Collect the finds as `D.first`/`D.first2` equations on the view (`find_view`,
  `find2_view`).
- Show the String path's fields are the same slices:
  - the body is the text before the first LF, minus a final CR;
  - `NF.pre` rejects "INFO ends at the LF and the byte before the LF is CR", so INFO and
    every earlier field lie before any final CR.
- `NF.noend` (bytes) gives `J.noend(INFO text) == True`, so `J.info.if` keeps `""`.
- `NF.num` gives `B.Pos.read` and `Nat.show`.
- For i + 1 in U32: D.ok bounds len by 2^31. Use lawful-bytes' bounds lemmas; never
  compare with a big literal.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only your skeleton file and new `proof_b_cut_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_cut.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: the only TODOs left are the 5 in `proof_b_fasteq.bend`.
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_cut.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about six hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
