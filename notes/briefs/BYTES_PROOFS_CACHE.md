# Phase B proof area "cache": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in the proofs of the six deliverables in
`proof_b_cache.bend`: `parts_ok`, `win_truths`, `serve_ok`, `req_holds`, `jtruth_ok`,
`against_hit`. Each is `?TODO`, with its statement fixed.

They are about the machine's reference cache (`norm.bend`: `Win`, `parts`, `Req.of`,
`win_of` and `win_parts`, `serve`, `against`). The machine keeps the last answers it
got. A window built from truthful answers is fixed by the contig and the bounds read: its
picture `WP`, and `mkWin` builds the window. Then:
- the answers it serves are truthful (`jtruth`);
- the reads it asks are within 2^31 letters;
- a retried read is held;
- the fast path's REF test passing means the String path's REF check passes.

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_cache.bend`: your skeleton (`WP`, `mkWin`, `wpOf`, `jtruth`, `holds`,
   `wp_ok`, `fa_bytes`, `up`, `bases_of`) and deliverables. Also `proof_b_defs.bend`
   (shared, read-only).
3. The code, `norm.bend`:
   - the "Reference reads" section;
   - `against` and the `win.*` functions in the fast path section;
   - `NR.of_str` (`norm_run.bend`, `put_str`);
   - `NF.same`, `NF.refeq` (`norm_fast.bend`).
4. The contract:
   - `MACHINE.bend`: `truth`, `truths`;
   - `bytes_enc.bend`: `enc`, `reqs_ok`; `E.enc`'s view is `codes(s)` (the enc area
     proves this in `proof_b_enc.bend`, `enc_bt`/`enc_ok`, still in progress: state what
     you need from it as a hypothesis-free lemma call to `PE.enc_ok`, and leave it if it
     is not done yet).
5. `proof_window_defs.bend` (`WS.truthful`), `norm_line.bend` (`J.ref_check`, `J.Ans`),
   `types.bend` (`B.Fasta.find`, `B.Bases.of_fasta`, `B.Base.of_fasta`,
   `B.Base.of_letter`).
6. lawful-bytes, all proven:
   - `../lawful-bytes/LAWS.bend`: `len_*`, `to_list_*`, `same_*`, `at_*`, `push_*`,
     `grow_*`, `empty_*`;
   - `../lawful-bytes/proof_core.bend` (`C.BT`), its `notes/` and `PROVING.md`;
   - `../lawful-words` (`proof_nat`, `proof_u32`): U32/Nat conversions.
7. `notes/briefs/PROVING.md`, `bend guide`.

## Hints

- 2^31 appears as `Norm.big()` = `Nat.pow(2n, 31n)` and in `E.reqs_ok` as
  `Nat.pow(2n, 31n)`. Prove `parts` facts for an abstract bound k, and instantiate them
  only with that syntactic term. Never compare a symbolic Nat with a big literal: see the
  notes.
- `parts.go`'s fuel is `b - a`; the case `0n False` is never reached when k >= 1.
- `against_hit`:
  - The fast path compares in U32 (`offu`, `rlen`, `clenu`).
  - `win_of.k` sets `clenu` to 0 unless off and clen are below 2^31. The window's `raw`
    holds `letters(r, a, b)`, so it has at most 2^31 bytes (a single read). Hence a hit's
    U32 tests mean the Nat facts.
  - `NF.refeq` is `(x ^ y) & 0xDF == 0` byte by byte. With REF upper-case ACGTN (`up`),
    it means `B.Base.of_fasta` of each letter equals `lb` of REF's byte.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only `proof_b_cache.bend` and new `proof_b_cache_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_cache.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: no TODO left apart from those of `proof_b_fasteq.bend`, `proof_b_enc.bend`
  (another area, in progress) and the 15 open laws of `LAWS.bend`/`MACHINE.bend` (they
  are not yours).
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_cache.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about seven hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
