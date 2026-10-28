# Phase B area "cache": notes

Brief: `notes/briefs/BYTES_PROOFS_CACHE.md`.

## Status (2026-10-28): all deliverables proven

Every check goes through `test/bcheck.sh`:
- `proof_b_cache.bend`: 15 TODOs, none of them mine (all other areas').
- `proof_b_cachedefs.bend`, `proof_b_cache_lem.bend`, `proof_b_cache_te.bend`,
  `proof_b_cache_hit.bend`: all check, and pass `--verdict` too.

Copies of `proof_b_cache.bend` with `parts_ok`'s last conjunct, or `against_hit`'s REF
conclusion, broken on purpose fail.

| deliverable | status |
|---|---|
| `parts_ok` | proven: reqs_ok (le31 on every read); 1 <= reads; reads <= max(1, b - a) |
| `win_truths` | proven: one read, or the halves, whose joined answers are the window's letters |
| `serve_ok` | proven, every case |
| `req_holds` | proven, about `CD.wpReq` (Req.of's one read, or a .. e itself) |
| `zero_holds`, `jtruth_ok` | proven |
| `against_hit` | proven, with hypotheses `hcb` (c is bytes) and `hcl` (`len_le(c, 2^28)`), which the lead added; counterexample without them: `proof_b_cache_cex2.bend` |

What each file holds now:
- `proof_b_cache_lem.bend`, the reads of `parts.go`. No bound constant: the lemmas are
  generic in the fuel and the le31 test.
  - Halves: `HV`, `half_eq`, `half_pos`, `half_lt`, `half_rest`, from `div_mod`/`mod_lt`.
  - Reads: `p31` (each read passes le31), `pl1` (at least one), `pl2` (a split asks two
    or more), `pmax` (at most `max(1, b - a)`).
  - Shape of the list: `ph` (the first read is on c, from a), `pallc` (every read on c),
    `plast` (the last read ends at b), `pp_true`.
  - Fuel bounds for the halves: `hf_a`/`hf_b`, which use `two_of` (a read that fails
    le31 has 2 letters or more).
  - le31: `le31_mono`, `le31_fit`, `gt31`.
- `proof_b_cache_te.bend`: `te`, `text_of(E.enc(s)) == s` for a byte text within
  `P.le31`.
- `proof_b_cache.bend`:
  - `W2`: a list of two reads or more is read as a window in parts, up to the last
    read's end.
  - `WP_some`/`WP_none`: the first answer fixes the window.
  - `rt_app`: the answers to two lists, joined.
  - `rw`: the answers decoded and joined give the letters, through `letters_cat` at the
    middle.
  - `wt.*`, `wo.*`: the two halves of `win_truths`.
  - `sv.*`, `cx.*`, `ws`: `serve_ok`.
  - `rq.p`: `req_holds` by cases on `wpReq`'s test.
  - `rok31_eq`: `E.reqs_ok` is `rok31`.
- `proof_b_cache_hit.bend` (`against_hit`):
  - `rq_pair`/`rq_acc`/`rq_val`: refeq's loop hands both buffers back, and its value
    means the slices are equal up to case.
  - `chk`/`pb`: the per-byte fact (an upper-case ACGTN byte and a byte < 256 equal up to
    case read as the same base), checked for all 256 bytes by computation.
  - `bq`: the same, lifted to lists of bases.
  - Word facts with powers kept symbolic (`f31_*`, `four_pow`, `sum32`, `pos31`, `tpp`,
    `tend`).
  - `ofs`: `NR.of_str` of a byte name; a copy of the run area's `of_str` with the 2^28
    bound.
  - `f2`: CHROM's text, after a passed CHROM test.
  - `rc`: `ref_check` is `Some(True)` from Nat facts.
  - In `proof_b_cache.bend`:
    - `f3.*`: the REF conclusion. Without fits31, `end <= 0` is impossible; with it,
      the U32 cover/fits tests give the Nat facts.
    - `ah.*`: one rewrite chain per outcome of `against`.
- `proof_b_cachedefs.bend`: `wpOf.k` picks with `Norm.le31(b - a)`; `wp_ok`'s single-read
  bound is `P.le31(b - a)`; it adds `wpReq`.

## Findings (research data)

- **A closed power compared in the full pass, even indirectly, overflows.** Examples:
  - `four_pow` with exponent 31 compared `mul(pow(2,2), ...)` against `mul(4n, ...)`,
    so the whole type went to the full pass.
  - `fits_le31` compared `Bool.and(True, Nat.is_le(.., to_nat(2147483648)))` against
    the bare `Nat.is_le`.

  Fix: keep exponents and words as variables in the lemma (`four_pow.g`, `u_le_of_lt`),
  and instantiate them only where the types match syntactically.
- **Failed checks whose context holds a closed power crash the error printer**, which
  normalizes it to unary: the output is a JS `RangeError` with no location. Bisect by
  holing defs cumulatively, from the last good one.
- **Byte facts by computation.** `chk(256n, x)` checks a per-byte Bool property for all
  bytes in about a second. Small numbers (256) are fine to compute; it avoided reasoning
  about xor/and on symbolic words.
- **Generating long statements from templates** needs word-bounded, single-pass
  substitution. A naive `replace("BT", ...)` also rewrote `C.BT(`, and `X` rewrote the
  module alias `X.`.

- **No closed big Nat in the code made the parts proofs short.**
  - With `big()` a power, every unfolding of `parts` overflowed. As
    `U32.to_nat(2147483648)` it did too. As a bare literal, `le31` of it could not be
    shown.
  - The halving `parts` has no constant, and the lemmas need no bound hypothesis at all:
    le31 comes from the code's own test, and `two_of` gives the >= 2 letters that make
    each half smaller.
- **An affine list cannot be let-bound** (`+T = M.truths(...)`): write it out at each use.
- **Lets used in a signature** (`l`, `lt` in a statement) are refused: expand them there.

- **Big closed Nats.** The checker compares in two passes: syntactic, then with full
  unfolding.
  - The full pass expands any closed big Nat that is not a bare literal
    (`Nat.pow(2n, 31n)`, `Norm.big()` when it was a power, `U32.to_nat(2147483648)`)
    into unary, so the comparison overflows.
  - Bare literals compare by value, but cannot be related to anything else.
  - Comparing a computed 2^24 with a literal took 46 s; 2^31 would take about
    100 minutes.
- **Wrapper defs around a stuck call break unfolding.** `X.PG(...) := Norm.parts.go(...)`
  failed against `Norm.parts(c, a, b)`. The lemma restated on `Norm.parts.go` directly
  checked. The failed check's error printing then overflowed (it normalizes, and unrolls
  stuck recursions on a literal).
- **`parts.go(x, True, ...)` does not reduce for a symbolic fuel x:** the match looks at
  the fuel first. `pg_true` cases on it.
- **The usual traps.**
  - Rewrite direction: about 8 errors.
  - A match after a let.
  - Lets used in a signature.
  - Destructuring a computed pair is refused; three separate lemmas `pg1`–`pg3` avoid it.
- **The two false first statements** (now fixed by the lead):
  - `against_hit`: POS near 2^32 wrapped the U32 end; empty REF with off >= 2^32.
  - `serve_ok`: a single-read window of more than 2^32 letters.

## Helping adv (2026-10-28): the String-mode holes adv.ms.sb / adv.ms.sl

- Proven in `proof_b_adv_msx.bend` (`ms_sb`, `ms_sl`); each hole in `proof_b_adv.bend` is one
  call to it. Shared with pb-alleles: the verdict lemma `vd_ok` (VWant also gives
  `fst_c(reqs) == Some{CHROM field}`) and the statement `judge_bytes` (open, for the lead).
- Counterexample found on the way (fixed by the lead): an SL source holding an LF
  (`proof_b_adv_msx_cex.bend`); `src_ok(SLP{p})` now also asks `nolf(p)`.
- Details for pb-alleles: `notes/bytes_proofs_adv.md`, section "For pb-alleles, from pb-cache".
