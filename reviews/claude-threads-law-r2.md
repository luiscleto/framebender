# Law review `--threads`, round 2

**Verdict: ACCEPT.** Every round-1 finding is resolved, and the revised statement has no new hole. Four minor items remain, none blocking. I checked the revised definitions and the 18 new examples by hand against the drafted parser. I ran no `bend` check, and the repository is untouched.

## Your two questions

**Does `Args.expecting` exactly capture "where an option may come"?** Yes, for every prefix without an earlier error.
- In the state `PNone` with `ok` true, the next word goes to `Args.word`. There `--threads` is matched as the option, before the "VCF path" fallback.
- In `PRef`, `PCheck`, `PWin` and `PThr`, the next word is a value, and `expecting` is false there. That excludes my round-1 counterexample, `-f --threads 8`.
- The position after the VCF path is included, as it should be.
- Splitting the command line into `pre` and `post` is sound: reading `pre ++ post` from the start is the same as reading `post` from the state after `pre`.
- Repeated `--threads` work by removing one at a time, and the earlier one stays at a position where `expecting` holds.

**Does `Args.threads` now return `Some` only for accepted lines?** Yes.
- `Args.threads.if` checks the `"norm"` word.
- `Args.thr.done` requires the same final state as `Args.done`: nothing pending, a reference, a VCF path, and `ok` true. That is exactly the condition for `Args.parse` to return `Some`.
- `ok` true means every `--threads` value passed the 1 to `max_threads()` check, so the last one is in range too.
- `threads_trailing`, `threads_cmd`, `threads_big`, `threads_zero` and `threads_refused` all give `None`, as they should.

## Round-1 findings
| # | Finding | Status |
|---|---|---|
| 1 | Memory exception | Resolved: in the law's comment and in law machine's runtime bullet. For `docs/LAWS.md`, see item 3 below. |
| 2 | `Args.threads` gave counts for refused lines | Resolved. |
| 3 | Driver internals in the law's comment | Resolved: moved to a trusted bullet of law machine. |
| 4 | Documented form not the proven form | Resolved: the law now covers every option position, so keeping `[--threads N]` among the options is fine. |
| 5 | Missing examples | Resolved: all present and correct. |
| 6 | Say why the law holds | Resolved. |
| 7 | 2^48 values | No change, as agreed. |

The answers to the five design questions stand as decided.

## Findings

1. **Minor: `Args.expecting` is narrower than its name** (`types.bend`, `Args.expecting.of`).
   - **Why:** the `ok` part makes it false after an earlier error, for example after `-c x` (example `expecting_error`). But the parser still reads the next word there as an option. This is harmless: after an error both sides of the law are usage errors. Still, the law's comment lists "after an option's value" without the "no error so far" condition.
   - **Fix, either of:**
     - Drop `ok`, so `expecting` means only "no option waiting for its value". The law is then strictly stronger and still true, since both sides are `None`. The proof needs one small lemma: once `ok` is false it stays false.
     - Or add "with no error so far" to the parenthetical in the law's comment.

2. **Minor: the bound on `Args.threads` is a comment, not a proof** (`types.bend`, `Args.thr.done`).
   - **Why:** `Args.thr.done` copies the pattern of `Args.done` instead of using it. The claims "None for every command line Args.parse refuses" and "1 ≤ n ≤ max_threads" are stated only in the comment, and the driver's 128-slot tables rely on them. A later edit to `Args.done` could make the two disagree without anything failing.
   - **Fix:** in step 2, either define `Args.threads` through `match Args.parse(argv)`, or prove a small lemma: `Args.threads(argv) == Some{n}` implies `Args.parse(argv)` is `Some` and n is in range. In either case, have `io64.c` cap the value at 128 as well, as a second guard.

3. **Minor: the `docs/LAWS.md` text is not in the shown diff.**
   - **Why:** the notes say the docs now give the memory exception, the driver depths and law `threads` under "The program", but the round-2 diff shows only `types.bend`, `MACHINE.bend` and `examples.bend`.
   - **Fix:** include the docs text in the step 2 diff, so the final review sees it.

4. **Minor, for the driver review: the C scan's copy of the grammar.**
   - **Why:** the constructor must copy some edge cases of the parser exactly:
     - a lone `-` is a VCF path, while `-x` is refused (the parser's `opt` rule);
     - an empty word is accepted as a VCF path;
     - `+RTS … -RTS` and `--RTS` words are separated out as Bend's `main` does.
   - A mismatch cannot change the output either way: on a usage error it only sets threads for a run that exits 2 anyway, and otherwise it only falls back to the default thread count. But "it only ever sets an N that `Args.threads` returns" is only as exact as that copy.
   - **Fix:** say "at most" in the notes, and test these edge cases in the driver review.
