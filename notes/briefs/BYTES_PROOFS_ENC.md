# Phase B proof area "enc": brief

You are a proof agent on framebender (a VCF normalizer in Bend 2.0.39, with machine-checked
laws), on git branch `bytes`. Fill in the proofs of the five deliverables in
`proof_b_enc.bend`: `enc_bt`, `enc_ok`, `chars_codes`, `chars_eq`, `out_ok`. Each is
`?TODO`, with its statement fixed.

## Read first, in order

1. `notes/bytes_proofs.md`: the plan, the rules, the 2^32 trap, the lawful-bytes technique.
2. `proof_b_enc.bend`: your skeleton (`ttree`, `enc_t`) and deliverables.
3. `bytes_enc.bend`, the contract's encoding:
   - `E.enc(s) = D.Bytes{from_nat(length s), tree(depth(length s), words(codes s))}`;
   - `E.text`, `E.chars`, `E.codes`;
   - `E.out` checks that the block is a perfect tree (`shape`) of depth at most 29 holding
     len bytes.
4. `../lawful-bytes/defs.bend`:
   - `D.view = take(unpack(A.view(buf)), len)`;
   - `D.ok` is `A.full(buf, d)`, `d <= 29`, and `len <= 4 * 2^d`.
5. `../lawful-bytes/proof_core.bend`:
   - `C.BT(len, t) = D.Bytes{len, fromT(t)}`;
   - `C.ok_full`, `C.ok_d`, `C.ok_len`, `C.ok_mk`, `C.WL`, the `unpack_*` lemmas;
   - also read its `notes/` and `PROVING.md`.
6. lawful-arrays:
   - `../lawful-arrays/defs.bend` (`A.view`, `A.full`);
   - `../lawful-arrays/proof_tree.bend` (`Tree`, `fromT`, the mirror lemmas,
     `view_length`, `size_tree`);
   - its notes.
7. lawful-words: `../lawful-words/defs.bend` (`W.pack4`, `W.byte`) and
   `../lawful-words/proof_bytes.bend` (byte/pack facts).
8. `notes/briefs/PROVING.md`, `bend guide`.

## Hints

- `enc_bt` and `chars_eq` should be short: an induction showing
  `fromT(ttree(d, ws)) == E.tree(d, ws)`, and one on the list.
- `enc_ok` is the main work:
  - `unpack(words(codes s))` starts with `codes s`, zero-padded;
  - the perfect tree of depth `depth(n)` holds `words`;
  - `n <= 4 * 2^depth(n)`, and `depth(n) <= 29` when `n <= 2^31`;
  - `U32.to_nat(U32.from_nat(n)) == n` for `n <= 2^31`.
  Keep 2^31 abstract (`Nat.pow(2n, 31n)` exactly as in the statement), and prove generic
  lemmas for an abstract bound.
- `out_ok`:
  - `C.ok_full` gives `A.full(fromT(t), d)`, so `E.shape` is `(Some d, A.view(...))`;
  - `ok` gives `d <= 29` and `len <= 4 * 2^d`.

## Rules

Follow `notes/bytes_proofs.md` ("Rules for every area"):
- Edit only your skeleton file and new `proof_b_enc_*.bend` helper files.
- Check with `timeout 1800 test/bcheck.sh proof_b_enc.bend` (never bend directly: 4 GB cap, at most two checks at once), one check at a time.
- Target: no TODO left in your file.
- No git commits.
- If a statement is false or unusable as stated, stop and report exactly why, with a
  counterexample if you have one.
- Keep notes in `notes/bytes_proofs_enc.md`: status, and bullets on where it got hard.

Work until all deliverables are proven, or about five hours. Then finish with a report:
what is proven, what is left and why, and any statement you think is wrong.
