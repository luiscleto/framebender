# Law review: `--threads N`

**Verdict: ACCEPT, with two should-fix items (1 and 2). No blockers.**

I checked all nine drafted examples by hand against the drafted parser. I did not run `bend` on a copy; the only check run is the one `notes/threads.md` reports.

## Findings

1. **Should fix: the law's claim needs the memory exception.** In the drafted comment on `law threads` (`MACHINE.bend`), law machine's runtime bullet, and `docs/LAWS.md` ("What the laws do not cover").
   - **Why:** "never changes what the program does" holds only inside the law. Memory grows with N: about 11 MB per batched piece, plus 3.5 MB per piece read ahead. So a run that succeeds at the default can stop with "bend: out of memory" (exit 1) at N = 128, and a run that fails at the default can succeed at N = 1. Law machine already leaves the runtime's stops out, so the statement is true. But in plain terms it reads as having no exception, and this is the difference a user will actually see.
   - **Fix:** add "except that Bend's runtime may run out of memory at a different N (memory grows with N)" in all three places.

2. **Should fix: `B.Args.threads` returns a count for command lines that `parse` refuses.** In the drafted `Args.threads` / `Args.thr_of` (`types.bend`).
   - **Why:** it skips the `"norm"` check and ignores `ok`. For example, `["norm","--threads","0"]` gives `Some{0}`, `["norm","--threads","999"]` gives `Some{999}`, and `["x","--threads","8"]` gives `Some{8}`. `Norm.start` is safe because it uses the value only after `parse` succeeds. But `main.bend` passes the same value to `Io.threads(n)`, and `io64.c` keeps 128-slot arrays. Safety would then depend on the driver calling `Io.threads` only after the usage check, which is a trap for the driver review.
   - **Fix:** return `None` unless `Args.parse(argv)` is `Some`. Every result is then between 1 and `max_threads()` by construction. Add the example `B.Args.threads(["norm","--threads","0","-f","r.fa","in.vcf"]) == None{}`.

3. **Minor: the law's comment lists driver internals.** In the drafted comment: "pieces normalized at once; the driver's read-ahead, reference reads in flight and Bend's worker threads".
   - **Why:** only the batch size is inside the proven machine. The law holds for the driver's depths and the runtime's threads only because `launch` does not model them, not because anything checked them. Listing them suggests coverage the law does not have. It also contradicts the note's "code, not law", and the text would have to change if question 5 goes the `+RTS` way.
   - **Fix:** the law says only "the program may size its work by N", and the list moves to the docs. Add a bullet to law machine's trusted list: "the driver's read-ahead and reference reads in flight, and the runtime's thread count, follow --threads; reading and writing stay exactly as above."

4. **Minor: the documented form is not the proven form.** In the drafted `usage()` and the README.
   - **Why:** the law covers `--threads` right after `norm`, but the usage string shows it after `-w N`.
   - **Fix:** use `framebender norm [--threads N] -f ref.fa [-c e|w] [-w N] in.vcf`. In the docs, add: "anywhere else among the options it is read the same way; right after `-f`, `-c` or `-w` it is that option's value; every `--threads` must be valid, and the last one counts."

5. **Minor: missing examples** (`examples.bend`):
   - `-c --threads …` and `-w --threads …` are usage errors.
   - `norm --threads -f r.fa in.vcf` is `None`: the missing value takes `-f` as the value.
   - `--threads 0 … --threads 8` is `None`: an invalid earlier one still fails, as with `-w`.
   - `parse(norm --threads 8 in.vcf) == None`: the lemma's shape on a rest that does not parse.
   - The `Args.threads` example from item 2.

6. **Minor: say why the law holds.** In the law comment and in `docs/LAWS.md`, "The program".
   - **Why:** `law threads` follows from three things: law machine (which holds for every accepted command line, so for every batch size `Norm.start` picks), law usage, and the parser fact. Its only new content is that `parse` drops `--threads N`. That is the right reason, not an accidental one, but a reviewer should be told where to look: `Args.step` and `Args.done`.
   - **Fix:** add one sentence: "It follows from law machine: parse gives the same Cfg with or without --threads N."

7. **Minor, no change needed:** a number of 2^48 or more after `--threads` stops in the runtime with exit 1, not as a usage error with exit 2. This matches `-w` and is already covered by law machine. Mention it in the usage docs.

## Question 2: the grammar
- **Unambiguous:** yes. The parser reads the words left to right in one fixed way, so each command line has exactly one reading.
- **Without `--threads` as an option, nothing changes:** every branch adds each word to `keep` exactly as before. So `keep == rest`, and the `Cfg`, including `Opts.args`, is byte for byte the old one.
- **The accepted set only grows:** the old grammar refused `--threads` wherever an option was expected, since it starts with `-`. The only new lines are those with `--threads` in that position.
- **`--threads` as a value:** after `-f` it is still a path (`args_threads_path`). After `-c` or `-w` it is still a usage error.
- **Drafted examples:** all nine are correct, including `008`, `four`, 0, 129, a trailing `--threads`, and the last one counting.

## The author's five questions
1. **Header:** leave `--threads` out, as proposed. The law then needs no exception, and the recorded line still reproduces the output exactly. Say in the `Opts.args` comment that it records the arguments that decide the output.
2. **Range:** keep 1 to 128, with 0 a usage error.
   - Making 0 mean the default would reverse bcftools' meaning, where 0 means no extra threads. A loud error is better than a silent surprise.
   - Do not remove the limit: an unbounded read-ahead is a memory trap. Because `max_threads()` is in the law's hypothesis, raising it later goes through review, which is right.
3. **Position:** keep "right after norm". A general position really does need the parser's state, because "both sides parse" is not enough. For example, `norm -f --threads 8 -c e` and `norm -f -c e` both parse, to different `Cfg`s: reference `--threads` and VCF `8`, against reference `-c` and VCF `e`. Cover the documented form instead (item 4).
4. **Lemma or law:** keep it a lemma. `law threads` already says the same thing in the user's terms (the same `launch`), and the parser fact is visible in `Args.step`. Add item 6's sentence.
5. **Constructor or `+RTS --threads N -RTS`:** the laws do not care either way.
   - The constructor is a second copy of the grammar in trusted C. Decide by the step 2 measurement, and drop it if it gains nothing.
   - If it stays, it must fail safe: on anything unexpected it does nothing, and it only ever sets an N that the fixed `Args.threads` (item 2) would return.
   - Keep the law text independent of this choice (item 3).

## Question 4: for a scientist
Open the docs entry with "`--threads` changes only speed and memory, never stdout, messages or exit code (apart from memory, item 1)", then give the law.
