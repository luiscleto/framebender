# Law review `--threads`, round 1: responses

Reviewers: Claude (`claude-threads-law.md`: ACCEPT with two should-fix), GPT 6.1 Sol
(`gpt-threads-law.md`: three should-fix), Grok 4.7 (`grok-threads-law.md`: one blocker).
Prompt: `THREADS_LAW_PROMPT.md`. Draft: `notes/threads.md`.

| # | finding | by | response |
|---|---|---|---|
| 1 | `law threads` covers only `--threads` right after `norm`; the form users write (`norm -f ref.fa --threads 8 in.vcf`, or after the VCF path) is outside it, and inserting at the front says nothing about a later `--threads` in `rest` | Grok (blocker), GPT (should fix); Claude preferred the front-only form plus documenting it there | **Accepted.** State it at every position where the parser expects an option: `launch` of `norm <> pre <> ["--threads", x] <> post` equals `launch` of `norm <> pre <> post`, under `Args.expecting(pre)` (the parse of `pre` from `Args.init()` is `ok` with nothing pending), `Pos.read(x) == Some{n}`, `1 <= n <= max_threads()`, and `hf`, `h`, `hb` as in law machine (`hb` on the longer line). `pre` empty is the old statement. The parser fact becomes a lemma over `pre` (Claude's counterexample, `-f --threads 8`, is excluded by `expecting`). |
| 2 | `Args.threads` returns a count for command lines `parse` refuses (`--threads 999` → 999, `x --threads 8` → 8, a trailing incomplete `--threads` keeps an earlier one) while the driver's arrays have 128 slots | all three | **Accepted.** `Args.threads(argv)` is `Some{n}` only when `Args.parse(argv)` is `Some`; then `1 <= n <= max_threads()`. |
| 3 | "never changes what the program does" needs the memory exception: memory grows with N, so the runtime's own out-of-memory stop (exit 1, already outside law machine) can happen at one N and not another | Claude, GPT | **Accepted.** Say it in the law's comment, in law machine's runtime bullet, and in `docs/LAWS.md` ("What the laws do not cover"). |
| 4 | The law's comment lists driver internals (read-ahead, reads in flight, runtime threads) that the law does not cover | Claude | **Accepted.** The law's comment says only that the program may size its work by N; the list goes to the docs and to a trusted bullet of law machine's comment ("the driver's depths and the runtime's thread count follow `--threads`; reading and writing stay exactly as above"). |
| 5 | Say why the law holds | Claude | **Accepted:** "It follows from law machine: parse gives the same Cfg with or without `--threads N` where an option is expected." |
| 6 | More examples: `-c --threads`, `-w --threads` (usage errors); `norm --threads -f r.fa in.vcf` (None); `--threads 0 … --threads 8` (None); `parse(norm --threads 8 in.vcf)` (None); `Args.threads` on `008` (Some 8), on `-f --threads` as a path (None), on a refused line (None) | Claude, Grok | **Accepted**, all of them. |
| 7 | Byte-for-byte compatibility holds for accepted command lines; the usage message itself changes | GPT | **Accepted:** reword the note. |
| 8 | Header: leave `--threads N` out of `Opts.args` | all three agree | **Kept.** Say in the `Opts.args` comment that it records the arguments that decide the output. |
| 9 | Range 1 to 128, 0 a usage error, no unlimited value | all three agree | **Kept.** Describe 128 as the chosen limit (the runtime's worker cap and the driver's arrays). |
| 10 | Parser fact: a lemma, not a law in `LAWS.bend` | all three agree | **Kept.** |
| 11 | Runtime threads: C constructor setting `BENDRTS`, or document `+RTS --threads N -RTS` | Grok: constructor; Claude: decide by measurement, fail safe; GPT: `+RTS` first | **Constructor, by measurement.** Build it; keep it only if step 2's timings or memory show a gain over `--threads` without it. It must fail safe: anything unexpected → it does nothing; it only ever sets an N that `Args.threads` would return. The docs promise no exact thread count (a user's `BENDRTS` or `+RTS` wins). It goes to the driver review either way. |
| 12 | Usage string: show the documented form | Claude | With item 1 any position is covered; keep `[--threads N]` among the options. |
| 13 | A value of 2^48 or more stops in the runtime (exit 1), as `-w` does | Claude | No change; mention in the usage docs. |
